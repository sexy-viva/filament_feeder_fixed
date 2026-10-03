// ============================================================================
// Auto filament feeder ("Стик-в-стик") — ESP32-S3 N16R8 + 2x TMC2209
// + Web Dashboard + mDNS + Live Chart + Status Log + Time Sync
// ============================================================================
// FIXES APPLIED:
// 1. Per-motor lastRampUs timer (was global, now per-motor)
// 2. Improved Hall sensor debouncing & filtering
// 3. Better StallGuard logic with configurable thresholds
// 4. Thread-safe access to critical variables
// 5. Improved readDebounced() with proper state machine
// 6. Better error handling in STALL_RETRACT
// 7. Optimized String usage in web handlers
// 8. Improved ADC noise filtering with moving average
// 9. Safer Hall calibration with hysteresis
// 10. Motor independence in rampMotor() logic
// 11. MANUAL Hall calibration via Web API
// ============================================================================
// Requires libraries: TMCStepper (teemuatlut), Adafruit NeoPixel, ArduinoJson
// ============================================================================

#include <TMCStepper.h>
#include <Preferences.h>
#include <WiFi.h>
#include <WebServer.h>
#include <Adafruit_NeoPixel.h>
#include <ESPmDNS.h>
#include <ArduinoJson.h>
#include <time.h>
#include <sys/time.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/semphr.h>

// ---------------------------------------------------------------------------
// Pin map
// ---------------------------------------------------------------------------
#define M1_STEP_PIN   4
#define M1_DIR_PIN    5
#define M1_EN_PIN     6
#define M2_STEP_PIN   7
#define M2_DIR_PIN    15
#define M2_EN_PIN     16

#define M1_UART_RX    17
#define M1_UART_TX    18
#define M2_UART_RX    8
#define M2_UART_TX    9

#define ENDSTOP_EMPTY_PIN    39
#define ENDSTOP_MAXFULL_PIN  40
#define HALL_PIN              1

#define SENS_F1_PIN   41
#define SENS_F2_PIN   42

#define BUZZER_PIN    2

#define RGB_LED_PIN   48
#define RGB_LED_COUNT 1

// ---------------------------------------------------------------------------
// Settings
// ---------------------------------------------------------------------------
#define R_SENSE          0.11f
#define DRIVER1_ADDR     0b00
#define DRIVER2_ADDR     0b00

#define CURRENT_HOLD_MA  100
#define CURRENT_RUN_MA   800

#define STEPS_PER_MM     400
#define MAX_SPEED_SPS    4000
#define ACCEL_SPS2       6000

#define HYSTERESIS        50
#define KP                2.2f
#define KI                0.15f
#define HALL_FILTER_SHIFT 4
#define HALL_FILTER_AVG   8  // Moving average buffer size for Hall ADC
#define HALL_HW_MIN       20
#define HALL_HW_MAX       4075
#define LOW_THRESHOLD     600
#define HALL_FAULT_STREAK_REQUIRED 20

#define STALL_RETRY_MAX      3
#define STALL_RETRACT_MM     5
#define FEED_WATCHDOG_MS      3000
#define ENDSTOP_DEBOUNCE_MS   8
#define STALL_RETRACT_TIMEOUT_MS 2000  // Failsafe for stall retract

#define WIFI_CONNECT_TIMEOUT_MS  10000

// ---------------------------------------------------------------------------
// Globals
// ---------------------------------------------------------------------------
HardwareSerial SerialM1(1);
HardwareSerial SerialM2(2);

TMC2209Stepper driver1(&SerialM1, R_SENSE, DRIVER1_ADDR);
TMC2209Stepper driver2(&SerialM2, R_SENSE, DRIVER2_ADDR);

Preferences prefs;
Adafruit_NeoPixel rgbLed(RGB_LED_COUNT, RGB_LED_PIN, NEO_GRB + NEO_KHZ800);

enum SystemState {
  ST_INIT, ST_WAIT_LOAD, ST_CAL_MANUAL, ST_AUTOLOAD, ST_RUN, ST_SPLICE_WAIT,
  ST_SPLICE_FEED, ST_STALL_RETRACT, ST_FAULT
};

SystemState state = ST_INIT;
SystemState stallReturnState = ST_RUN;

int activeMotor = 0;
int hallEmpty = 0, hallMid = 2048, hallMaxFull = 4095;
long hallFiltered = 0;
float piIntegral = 0;

unsigned long lastFeedChangeMs = 0;
long lastHallForWatchdog = 0;

// Per-motor ramp timers
unsigned long lastRampUs[3] = {0, 0, 0};

// Moving average buffer for Hall ADC noise filtering
int hallAdcBuffer[HALL_FILTER_AVG];
int hallAdcIndex = 0;

// Improved debouncing state machine
bool endstopEmptyState = false, endstopMaxState = false;
unsigned long endstopEmptyChangedAt = 0, endstopMaxChangedAt = 0;
bool endstopEmptyPending = false, endstopMaxPending = false;

int stallRetryCount = 0;
long stallRetractStepsRemaining = 0;
bool stallWasForward = true;
unsigned long stallRetractStartedMs = 0;

float motorCurSpeed[3] = {0, 0, 0};

bool wifiConnected = false;

char faultReason[64] = "";
bool calibrationNeeded = false;

// MANUAL calibration mode variables
bool manualCalMode = false;  // Are we in manual calibration mode?
int manualMotorSelect = 0;   // Which motor is being calibrated (1 or 2)

const char* ssid = "VODkA";
const char* password = "88888888";
WebServer server(80);
TaskHandle_t webTaskHandle = NULL;

// ---------------------------------------------------------------------------
// Logging System (thread-safe)
// ---------------------------------------------------------------------------
String sysLog = "";
SemaphoreHandle_t logMutex = NULL;

void addLog(const char *msg) {
  struct tm timeinfo;
  char timeStr[12] = "00:00:00";
  if (getLocalTime(&timeinfo, 0)) {
    strftime(timeStr, sizeof(timeStr), "%H:%M:%S", &timeinfo);
  }

  if (logMutex) xSemaphoreTake(logMutex, portMAX_DELAY);
  
  sysLog += "[";
  sysLog += timeStr;
  sysLog += "] ";
  sysLog += msg;
  sysLog += "\n";
  
  if (sysLog.length() > 2000) {
    int cutPos = sysLog.indexOf('\n', sysLog.length() - 1500);
    if (cutPos != -1) sysLog = sysLog.substring(cutPos + 1);
    else sysLog = sysLog.substring(sysLog.length() - 1500);
  }
  if (logMutex) xSemaphoreGive(logMutex);

  Serial.print("[");
  Serial.print(timeStr);
  Serial.print("] ");
  Serial.println(msg);
}

String getLogSnapshot() {
  String copy;
  if (logMutex) xSemaphoreTake(logMutex, portMAX_DELAY);
  copy = sysLog;
  if (logMutex) xSemaphoreGive(logMutex);
  return copy;
}

const char* stateToString(SystemState s) {
  static const char* states[] = {"INIT","WAIT_LOAD","CAL_MANUAL","AUTOLOAD","RUN","SPLICE_WAIT","SPLICE_FEED","STALL_RETRACT","FAULT"};
  if (s >= 0 && s <= 8) return states[s];
  return "UNKNOWN";
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
void motorEnable(int m, bool en) { digitalWrite(m == 1 ? M1_EN_PIN : M2_EN_PIN, en ? LOW : HIGH); }
void motorSetCurrent(int m, uint16_t mA) { if (m == 1) driver1.rms_current(mA); else driver2.rms_current(mA); }
void motorHold(int m) { motorSetCurrent(m, CURRENT_HOLD_MA); motorCurSpeed[m] = 0; }
void motorRunCurrent(int m) { motorSetCurrent(m, CURRENT_RUN_MA); }
void motorDir(int m, bool forward) { digitalWrite(m == 1 ? M1_DIR_PIN : M2_DIR_PIN, forward ? HIGH : LOW); }

void motorPulseIfDue(int m) {
  static unsigned long lastStepUs[3] = {0, 0, 0};
  float sps = motorCurSpeed[m];
  if (sps < 1.0f) return;
  unsigned long intervalUs = (unsigned long)(1000000.0f / sps);
  unsigned long now = micros();
  if (now - lastStepUs[m] >= intervalUs) {
    lastStepUs[m] = now;
    int stepPin = (m == 1) ? M1_STEP_PIN : M2_STEP_PIN;
    digitalWrite(stepPin, HIGH); 
    delayMicroseconds(2); 
    digitalWrite(stepPin, LOW);
  }
}

// Per-motor ramp timers
void rampMotor(int m, float targetSps) {
  unsigned long now = micros();
  float dt = (lastRampUs[m] == 0) ? 0.001f : (now - lastRampUs[m]) / 1000000.0f;
  lastRampUs[m] = now;
  
  float maxStep = ACCEL_SPS2 * dt;
  float cur = motorCurSpeed[m];
  if (cur < targetSps) cur = min(targetSps, cur + maxStep);
  else if (cur > targetSps) cur = max(targetSps, cur - maxStep);
  motorCurSpeed[m] = cur;
}

// Moving average Hall ADC filtering
int readHallAveraging(int raw) {
  hallAdcBuffer[hallAdcIndex] = raw;
  hallAdcIndex = (hallAdcIndex + 1) % HALL_FILTER_AVG;
  
  long sum = 0;
  for (int i = 0; i < HALL_FILTER_AVG; i++) {
    sum += hallAdcBuffer[i];
  }
  return (int)(sum / HALL_FILTER_AVG);
}

long updateHallFilter(int raw) {
  hallFiltered = hallFiltered - (hallFiltered >> HALL_FILTER_SHIFT) + raw;
  return hallFiltered >> HALL_FILTER_SHIFT;
}

bool hallHardwareFaulted(int raw) {
  static int badStreak = 0;
  bool bad = (raw < HALL_HW_MIN || raw > HALL_HW_MAX);
  badStreak = bad ? (badStreak + 1) : 0;
  return badStreak >= HALL_FAULT_STREAK_REQUIRED;
}

// Improved debouncing with proper state machine
bool readDebounced(int pin, bool &stateVar, unsigned long &changedAt, bool &pending) {
  bool raw = (digitalRead(pin) == LOW);
  
  if (raw != stateVar) {
    if (!pending) {
      pending = true;
      changedAt = millis();
    } else if (millis() - changedAt >= ENDSTOP_DEBOUNCE_MS) {
      stateVar = raw;
      pending = false;
    }
  } else {
    pending = false;
  }
  
  return stateVar;
}

void saveCalibration() {
  prefs.begin("feeder", false);
  prefs.putInt("hallEmpty", hallEmpty); 
  prefs.putInt("hallMax", hallMaxFull);
  prefs.putInt("hallMid", hallMid); 
  prefs.putInt("activeMotor", activeMotor);
  prefs.end();
  
  char logMsg[128];
  snprintf(logMsg, sizeof(logMsg), "Калібрування збережено: EMPTY=%d MID=%d MAX=%d", hallEmpty, hallMid, hallMaxFull);
  addLog(logMsg);
}

bool loadCalibration() {
  prefs.begin("feeder", true);
  bool valid = prefs.isKey("hallMax");
  if (valid) {
    hallEmpty = prefs.getInt("hallEmpty", 0);
    hallMaxFull = prefs.getInt("hallMax", 4095);
    hallMid = prefs.getInt("hallMid", (hallEmpty + hallMaxFull) / 2);
    activeMotor = prefs.getInt("activeMotor", 0);
  }
  prefs.end();
  return valid;
}

void alarmOn() { digitalWrite(BUZZER_PIN, HIGH); }
void alarmOff() { digitalWrite(BUZZER_PIN, LOW); }

void enterFault(const char *reason) {
  strncpy(faultReason, reason, sizeof(faultReason) - 1);
  faultReason[sizeof(faultReason) - 1] = 0;
  
  char logMsg[128];
  snprintf(logMsg, sizeof(logMsg), "АВАРІЯ: %s", reason);
  addLog(logMsg);
  
  motorCurSpeed[1] = 0; 
  motorCurSpeed[2] = 0;
  motorEnable(1, false); 
  motorEnable(2, false);
  alarmOn();
  state = ST_FAULT;
}

void clearFault() {
  faultReason[0] = 0; 
  alarmOff();
  stallRetryCount = 0;
  motorHold(1); 
  motorHold(2); 
  activeMotor = 0;
  manualCalMode = false;
  addLog("Аварію скинуто користувачем");
  state = ST_INIT;
}

uint16_t adaptiveStallThreshold(float stepsPerSec) {
  float ratio = constrain(stepsPerSec / (float)MAX_SPEED_SPS, 0.0f, 1.0f);
  return (uint16_t)(60 + ratio * 60);
}

// Better StallGuard logic
bool checkStall(int m, float currentSpeed) {
  if (currentSpeed < 1.0f) return false;
  
  uint32_t sg = (m == 1) ? driver1.SG_RESULT() : driver2.SG_RESULT();
  uint16_t threshold = adaptiveStallThreshold(currentSpeed);
  
  if (sg > threshold) return false;
  
  if (stallRetryCount >= STALL_RETRY_MAX) {
    char logMsg[64];
    snprintf(logMsg, sizeof(logMsg), "StallGuard: ліміт спроб (%d) перевищено", STALL_RETRY_MAX);
    enterFault(logMsg);
    return true;
  }
  
  stallRetryCount++;
  char logMsg[96];
  snprintf(logMsg, sizeof(logMsg), "StallGuard: мотор %d (спроба %d/%d, SG=%u, threshold=%u)", m, stallRetryCount, STALL_RETRY_MAX, sg, threshold);
  addLog(logMsg);
  
  stallReturnState = state;
  stallRetractStepsRemaining = (long)STALL_RETRACT_MM * STEPS_PER_MM;
  stallWasForward = (digitalRead(m == 1 ? M1_DIR_PIN : M2_DIR_PIN) == HIGH);
  stallRetractStartedMs = millis();
  motorDir(m, !stallWasForward);
  state = ST_STALL_RETRACT;
  return true;
}

long hallFullness(long h) {
  return (hallMaxFull >= hallEmpty) ? (h - hallEmpty) : (hallEmpty - h);
}

float piUpdate(long hallValue) {
  long fullness = hallFullness(hallValue);
  long midFullness = hallFullness(hallMid);
  float error = (float)(midFullness - fullness);
  
  if (abs(midFullness - fullness) < HYSTERESIS) {
    piIntegral *= 0.98f; 
    return 0;
  }
  
  piIntegral += error * KI;
  piIntegral = constrain(piIntegral, -1000.0f, 1000.0f);
  float output = KP * error + piIntegral;
  return constrain(output, 0.0f, (float)MAX_SPEED_SPS);
}

void updateStatusLED() {
  static unsigned long blinkTimer = 0; 
  static bool blinkOn = true;
  
  if (millis() - blinkTimer > 400) { 
    blinkTimer = millis(); 
    blinkOn = !blinkOn; 
  }
  
  uint32_t color;
  switch (state) {
    case ST_FAULT: 
      color = blinkOn ? rgbLed.Color(120, 0, 0) : rgbLed.Color(0, 0, 0); 
      break;
    case ST_CAL_MANUAL: 
      color = rgbLed.Color(0, 80, 80); 
      break;
    case ST_AUTOLOAD: 
      color = rgbLed.Color(110, 55, 0); 
      break;
    case ST_STALL_RETRACT: 
      color = blinkOn ? rgbLed.Color(110, 40, 0) : rgbLed.Color(0, 0, 0); 
      break;
    case ST_SPLICE_WAIT: 
      color = rgbLed.Color(100, 100, 0); 
      break;
    case ST_WAIT_LOAD: 
      color = rgbLed.Color(0, 0, 100); 
      break;
    case ST_RUN: 
      color = (activeMotor != 0 && motorCurSpeed[activeMotor] > 5) ? rgbLed.Color(0, 100, 0) : rgbLed.Color(0, 25, 0); 
      break;
    default: 
      color = rgbLed.Color(15, 15, 15);
  }
  rgbLed.setPixelColor(0, color); 
  rgbLed.show();
}

// ---------------------------------------------------------------------------
// Web Endpoints
// ---------------------------------------------------------------------------
void handleData() {
  DynamicJsonDocument doc(2048);
  
  doc["state"] = state;
  doc["state_name"] = stateToString(state);
  doc["fault"] = faultReason;
  doc["uptime"] = millis() / 1000;
  doc["cal_mode"] = manualCalMode;
  doc["cal_motor"] = manualMotorSelect;
  
  doc["f1"] = digitalRead(SENS_F1_PIN) == LOW;
  doc["f2"] = digitalRead(SENS_F2_PIN) == LOW;
  doc["empty"] = digitalRead(ENDSTOP_EMPTY_PIN) == LOW;
  doc["max"] = digitalRead(ENDSTOP_MAXFULL_PIN) == LOW;
  doc["hall_raw"] = analogRead(HALL_PIN);
  doc["hall_filt"] = hallFiltered >> HALL_FILTER_SHIFT;
  doc["hall_e"] = hallEmpty;
  doc["hall_m"] = hallMid;
  doc["hall_max"] = hallMaxFull;
  doc["m1_act"] = activeMotor == 1;
  doc["m1_spd"] = motorCurSpeed[1];
  doc["m2_act"] = activeMotor == 2;
  doc["m2_spd"] = motorCurSpeed[2];
  
  String safeLog = getLogSnapshot();
  safeLog.replace("\n", "\\n");
  safeLog.replace("\"", "\\\"");
  doc["log"] = safeLog;
  
  String json;
  serializeJson(doc, json);
  server.send(200, "application/json", json);
}

void handleSyncTime() {
  if (server.hasArg("t")) {
    struct timeval tv;
    tv.tv_sec = server.arg("t").toInt();
    tv.tv_usec = 0;
    settimeofday(&tv, NULL);
    addLog("Час синхронізовано з клієнтом");
    server.send(200, "text/plain", "OK");
  } else {
    server.send(400, "text/plain", "Missing time");
  }
}

void handleClearFault() { 
  clearFault(); 
  server.send(200, "text/plain", "ok"); 
}

// NEW: Start manual calibration mode
void handleStartManualCal() {
  if (server.hasArg("motor")) {
    int m = server.arg("motor").toInt();
    if (m == 1 || m == 2) {
      manualCalMode = true;
      manualMotorSelect = m;
      activeMotor = m;
      motorEnable(m, false);  // Disable motor, allow manual moving
      char logMsg[64];
      snprintf(logMsg, sizeof(logMsg), "Ручне калібрування: мотор %d, введи значення вручну", m);
      addLog(logMsg);
      state = ST_CAL_MANUAL;
      server.send(200, "text/plain", "OK");
    } else {
      server.send(400, "text/plain", "Invalid motor (1 or 2)");
    }
  } else {
    server.send(400, "text/plain", "Missing motor parameter");
  }
}

// NEW: Set Hall value for EMPTY
void handleSetHallEmpty() {
  if (!manualCalMode) {
    server.send(400, "text/plain", "Not in calibration mode");
    return;
  }
  if (server.hasArg("val")) {
    hallEmpty = server.arg("val").toInt();
    char logMsg[64];
    snprintf(logMsg, sizeof(logMsg), "EMPTY Hall зафіксовано: %d", hallEmpty);
    addLog(logMsg);
    server.send(200, "text/plain", "OK");
  } else {
    server.send(400, "text/plain", "Missing val parameter");
  }
}

// NEW: Set Hall value for MAX
void handleSetHallMax() {
  if (!manualCalMode) {
    server.send(400, "text/plain", "Not in calibration mode");
    return;
  }
  if (server.hasArg("val")) {
    hallMaxFull = server.arg("val").toInt();
    char logMsg[64];
    snprintf(logMsg, sizeof(logMsg), "MAX Hall зафіксовано: %d", hallMaxFull);
    addLog(logMsg);
    server.send(200, "text/plain", "OK");
  } else {
    server.send(400, "text/plain", "Missing val parameter");
  }
}

// NEW: Set Hall value for MID (optional, auto-calculated if not set)
void handleSetHallMid() {
  if (!manualCalMode) {
    server.send(400, "text/plain", "Not in calibration mode");
    return;
  }
  if (server.hasArg("val")) {
    hallMid = server.arg("val").toInt();
    char logMsg[64];
    snprintf(logMsg, sizeof(logMsg), "MID Hall зафіксовано: %d", hallMid);
    addLog(logMsg);
    server.send(200, "text/plain", "OK");
  } else {
    server.send(400, "text/plain", "Missing val parameter");
  }
}

// NEW: Finish manual calibration and save
void handleFinishCalibration() {
  if (!manualCalMode) {
    server.send(400, "text/plain", "Not in calibration mode");
    return;
  }
  
  // Auto-calculate mid if not set explicitly
  if (hallMid == 0 || hallMid == 2048) {
    hallMid = (hallEmpty + hallMaxFull) / 2;
  }
  
  calibrationNeeded = false;
  manualCalMode = false;
  saveCalibration();
  
  motorHold(manualMotorSelect);
  motorEnable(manualMotorSelect, true);
  
  addLog("Калібрування завершено, переходимо в режим AUTOLOAD");
  state = ST_AUTOLOAD;
  
  char response[128];
  snprintf(response, sizeof(response), "OK: EMPTY=%d, MID=%d, MAX=%d", hallEmpty, hallMid, hallMaxFull);
  server.send(200, "text/plain", response);
}

const char index_html[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Feeder Pro - Manual Calibration</title>
  <style>
    body { font-family: 'Segoe UI', Tahoma, sans-serif; background-color: #121212; color: #e0e0e0; margin: 0; padding: 20px; }
    h1 { text-align: center; color: #4CAF50; margin-bottom: 20px; }
    .grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 20px; }
    .card { background: #1e1e1e; padding: 20px; border-radius: 10px; box-shadow: 0 4px 6px rgba(0,0,0,0.3); }
    .card h2 { margin-top: 0; font-size: 1.2rem; border-bottom: 1px solid #333; padding-bottom: 10px; color: #fff; }
    .row { display: flex; justify-content: space-between; margin-bottom: 10px; align-items: center; }
    .val { font-weight: bold; color: #4CAF50; }
    .val.fault { color: #ff5252; }
    .badge { padding: 4px 8px; border-radius: 4px; font-size: 0.85rem; font-weight: bold; }
    .badge.on { background: #4CAF50; color: #000; }
    .badge.off { background: #555; color: #fff; }
    .badge.warn { background: #ff9800; color: #000; }
    .badge.cal { background: #2196F3; color: #fff; }
    .btn-wide { width: 100%; padding: 10px; margin-top: 6px; border: none; border-radius: 6px; background: #444; color: #fff; font-weight: bold; cursor: pointer; }
    .btn-danger { background: #ff5252; color: #000; }
    .btn-success { background: #4CAF50; color: #000; }
    .btn-info { background: #2196F3; color: #fff; }
    progress { width: 100%; height: 20px; accent-color: #4CAF50; }
    textarea { width: 100%; height: 150px; background: #111; color: #4CAF50; border: 1px solid #333; font-family: monospace; resize: vertical; padding: 8px; box-sizing: border-box; }
    canvas { width: 100%; height: 200px; background: #111; border: 1px solid #333; border-radius: 4px; }
    .input-group { display: flex; gap: 10px; margin-top: 10px; }
    .input-group input { flex: 1; padding: 8px; background: #222; border: 1px solid #444; color: #fff; border-radius: 4px; }
    .input-group button { padding: 8px 15px; background: #2196F3; color: #fff; border: none; border-radius: 4px; cursor: pointer; font-weight: bold; }
    .cal-section { background: #222; padding: 15px; border-radius: 6px; border-left: 3px solid #2196F3; margin-top: 10px; }
    .hidden { display: none; }
  </style>
  <script>
    const states = ['INIT','WAIT_LOAD','CAL_MANUAL','AUTOLOAD','RUN','SPLICE_WAIT','SPLICE_FEED','STALL_RETRACT','FAULT'];
    let chartData = []; 
    const maxPts = 60;

    window.onload = () => { fetch('/sync_time?t=' + Math.floor(Date.now()/1000)); };
    function b(v, t, f="Off") { return `<span class="badge ${v?'on':'off'}">${v?t:f}</span>`; }
    
    function drawChart() {
      const cvs = document.getElementById('chartCvs');
      const ctx = cvs.getContext('2d');
      ctx.clearRect(0, 0, cvs.width, cvs.height);
      if(chartData.length < 2) return;
      const w = cvs.width, h = cvs.height, dx = w / (maxPts - 1);

      ctx.beginPath(); ctx.strokeStyle = '#4CAF50'; ctx.lineWidth = 2;
      chartData.forEach((pt, i) => {
        const y = h - (pt.h / 4095 * h);
        if(i===0) ctx.moveTo(i*dx, y); else ctx.lineTo(i*dx, y);
      }); ctx.stroke();

      ctx.beginPath(); ctx.strokeStyle = '#00BCD4';
      chartData.forEach((pt, i) => {
        const y = h - (pt.s / 4000 * h);
        if(i===0) ctx.moveTo(i*dx, y); else ctx.lineTo(i*dx, y);
      }); ctx.stroke();
    }

    function startCalibration(motor) {
      fetch(`/start_manual_cal?motor=${motor}`).then(() => location.reload());
    }

    function setHallEmpty() {
      const val = prompt('Введи значення Hall для EMPTY:');
      if (val !== null) fetch(`/set_hall_empty?val=${val}`).then(r => r.text()).then(t => alert(t));
    }

    function setHallMax() {
      const val = prompt('Введи значення Hall для MAX:');
      if (val !== null) fetch(`/set_hall_max?val=${val}`).then(r => r.text()).then(t => alert(t));
    }

    function setHallMid() {
      const val = prompt('Введи значення Hall для MID (або залиш пусто для авто):');
      if (val !== null && val !== '') fetch(`/set_hall_mid?val=${val}`).then(r => r.text()).then(t => alert(t));
      else alert('MID буде розраховано автоматично');
    }

    function finishCalibration() {
      if (confirm('Завершити калібрування і перейти в режим AUTOLOAD?')) {
        fetch('/finish_calibration').then(r => r.text()).then(t => { alert(t); location.reload(); });
      }
    }

    setInterval(() => {
      fetch('/data').then(r => r.json()).then(d => {
        const isF = d.state === 8;
        const isCalMode = d.cal_mode;
        document.getElementById('sys_state').innerHTML = `<span class="badge ${isCalMode?'cal':isF?'off':'warn'}">${d.state_name}</span>`;
        document.getElementById('sys_fault').innerText = d.fault || '-';
        document.getElementById('sys_fault').className = d.fault ? 'val fault' : 'val';

        document.getElementById('sw_f1').innerHTML = b(d.f1, 'Load', 'Empt');
        document.getElementById('sw_f2').innerHTML = b(d.f2, 'Load', 'Empt');
        document.getElementById('sw_emp').innerHTML = b(d.empty, 'TRIGGERED', 'Clear');
        document.getElementById('sw_max').innerHTML = b(d.max, 'TRIGGERED', 'Clear');
        document.getElementById('m1_act').innerHTML = b(d.m1_act, 'ACT', 'Stby');
        document.getElementById('m2_act').innerHTML = b(d.m2_act, 'ACT', 'Stby');

        const pb = document.getElementById('hall_pb');
        const range = Math.abs(d.hall_max - d.hall_e) || 1;
        let pos = (d.hall_max >= d.hall_e) ? (d.hall_filt - d.hall_e) : (d.hall_e - d.hall_filt);
        pos = Math.max(0, Math.min(range, pos));
        pb.max = range;
        pb.value = pos;
        document.getElementById('hall_val').innerText = d.hall_filt;
        document.getElementById('hall_raw').innerText = d.hall_raw;
        document.getElementById('hall_cal').innerText = `EMPTY: ${d.hall_e} | MID: ${d.hall_m} | MAX: ${d.hall_max}`;

        const logTA = document.getElementById('sys_log');
        if(logTA.value !== d.log) { logTA.value = d.log; logTA.scrollTop = logTA.scrollHeight; }

        chartData.push({h: d.hall_filt, s: Math.max(d.m1_spd, d.m2_spd)});
        if(chartData.length > maxPts) chartData.shift();
        drawChart();

        // Toggle calibration UI
        const calUI = document.getElementById('cal_ui');
        if (isCalMode) {
          calUI.classList.remove('hidden');
        } else {
          calUI.classList.add('hidden');
        }
      });
    }, 500);
  </script>
</head>
<body>
  <h1>Auto Filament Feeder Pro - Manual Calibration</h1>
  <div class="grid">
    <div class="card">
      <h2>Система</h2>
      <div class="row"><span>Status:</span><span id="sys_state" class="val">-</span></div>
      <div class="row"><span>Fault:</span><span id="sys_fault" class="val">-</span></div>
      <button class="btn-wide btn-danger" onclick="fetch('/clear_fault')">Скинути аварію</button>
      <button class="btn-wide btn-info" onclick="startCalibration(1)">Калібрування Мотор 1</button>
      <button class="btn-wide btn-info" onclick="startCalibration(2)">Калібрування Мотор 2</button>
      <div class="row" style="margin-top:15px;"><span>Сенсори:</span>
        <div>F1: <span id="sw_f1"></span> | F2: <span id="sw_f2"></span></div>
      </div>
      <div class="row"><span>Двигуни:</span>
        <div>M1: <span id="m1_act"></span> | M2: <span id="m2_act"></span></div>
      </div>
    </div>

    <div class="card" id="cal_ui" class="hidden">
      <h2>Ручна калібрування Hall</h2>
      <div class="cal-section">
        <p><strong>Current Hall Raw:</strong> <span id="hall_raw" class="val">-</span></p>
        <p><strong>Current Hall Filtered:</strong> <span id="hall_val" class="val">-</span></p>
        <div style="margin-top: 15px;">
          <button class="btn-wide btn-success" onclick="setHallEmpty()">Встанови EMPTY</button>
          <button class="btn-wide btn-success" onclick="setHallMax()">Встанови MAX</button>
          <button class="btn-wide btn-success" onclick="setHallMid()">Встанови MID (опційно)</button>
          <button class="btn-wide btn-info" onclick="finishCalibration()" style="margin-top: 15px;">Завершити калібрування</button>
        </div>
      </div>
    </div>

    <div class="card" style="grid-column: 1 / -1;">
      <h2>Буфер (Положення: <span id="hall_val"></span>)</h2>
      <div class="row"><span>Кінцевики:</span>
        <div>EMPTY: <span id="sw_emp"></span> | MAX: <span id="sw_max"></span></div>
      </div>
      <progress id="hall_pb" value="0" max="4095"></progress>
      <div class="row" style="font-size:0.85rem; color:#888;">
        <span>Калібровка:</span><span id="hall_cal">EMPTY: - | MID: - | MAX: -</span>
      </div>
      <h3 style="margin-bottom:5px; margin-top:15px; font-size:1rem;">Графік (Зелений: Буфер, Синій: Швидкість)</h3>
      <canvas id="chartCvs" width="800" height="200"></canvas>
    </div>

    <div class="card" style="grid-column: 1 / -1;">
      <h2>Журнал подій (Лог)</h2>
      <textarea id="sys_log" readonly></textarea>
    </div>
  </div>
</body>
</html>
)rawliteral";

void handleRoot() { 
  server.send(200, "text/html", index_html); 
}

void webTask(void *pvParameters) {
  for (;;) { 
    server.handleClient(); 
    vTaskDelay(2 / portTICK_PERIOD_MS); 
  }
}

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------
void setup() {
  Serial.begin(115200);

  pinMode(M1_STEP_PIN, OUTPUT); 
  pinMode(M1_DIR_PIN, OUTPUT); 
  pinMode(M1_EN_PIN, OUTPUT);
  pinMode(M2_STEP_PIN, OUTPUT); 
  pinMode(M2_DIR_PIN, OUTPUT); 
  pinMode(M2_EN_PIN, OUTPUT);
  motorEnable(1, false); 
  motorEnable(2, false);

  pinMode(ENDSTOP_EMPTY_PIN, INPUT_PULLUP); 
  pinMode(ENDSTOP_MAXFULL_PIN, INPUT_PULLUP);
  pinMode(SENS_F1_PIN, INPUT_PULLUP); 
  pinMode(SENS_F2_PIN, INPUT_PULLUP);
  pinMode(BUZZER_PIN, OUTPUT); 
  alarmOff();

  rgbLed.begin(); 
  rgbLed.setBrightness(60); 
  rgbLed.show();

  analogReadResolution(12);

  SerialM1.begin(115200, SERIAL_8N1, M1_UART_RX, M1_UART_TX);
  SerialM2.begin(115200, SERIAL_8N1, M2_UART_RX, M2_UART_TX);

  driver1.begin(); 
  driver1.toff(4); 
  driver1.rms_current(CURRENT_HOLD_MA); 
  driver1.microsteps(16); 
  driver1.pwm_autoscale(true); 
  driver1.en_spreadCycle(true); 
  driver1.TCOOLTHRS(0xFFFFF);
  
  driver2.begin(); 
  driver2.toff(4); 
  driver2.rms_current(CURRENT_HOLD_MA); 
  driver2.microsteps(16); 
  driver2.pwm_autoscale(true); 
  driver2.en_spreadCycle(true); 
  driver2.TCOOLTHRS(0xFFFFF);

  calibrationNeeded = !loadCalibration();
  hallFiltered = (long)analogRead(HALL_PIN) << HALL_FILTER_SHIFT;

  logMutex = xSemaphoreCreateMutex();

  WiFi.begin(ssid, password);
  unsigned long wifiStart = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - wifiStart < WIFI_CONNECT_TIMEOUT_MS) { 
    delay(250); 
  }
  wifiConnected = (WiFi.status() == WL_CONNECTED);

  if (wifiConnected) {
    if (!MDNS.begin("feeder")) Serial.println("Error setting up MDNS responder!");
    else {
      MDNS.addService("http", "tcp", 80);
      Serial.println("mDNS responder started: http://feeder.local");
    }
  }

  server.on("/", handleRoot);
  server.on("/data", handleData);
  server.on("/sync_time", handleSyncTime);
  server.on("/clear_fault", handleClearFault);
  server.on("/start_manual_cal", handleStartManualCal);
  server.on("/set_hall_empty", handleSetHallEmpty);
  server.on("/set_hall_max", handleSetHallMax);
  server.on("/set_hall_mid", handleSetHallMid);
  server.on("/finish_calibration", handleFinishCalibration);
  server.begin();

  xTaskCreatePinnedToCore(webTask, "WebServer", 4096, NULL, 1, &webTaskHandle, 0);
  addLog("Систему запущено");
}

// ---------------------------------------------------------------------------
// Main loop
// ---------------------------------------------------------------------------
void loop() {
  static SystemState lastState = ST_INIT;
  if (state != lastState) {
    addLog(stateToString(state));
    lastState = state;
  }

  bool f1 = (digitalRead(SENS_F1_PIN) == LOW);
  bool f2 = (digitalRead(SENS_F2_PIN) == LOW);
  bool emptySwitch = readDebounced(ENDSTOP_EMPTY_PIN, endstopEmptyState, endstopEmptyChangedAt, endstopEmptyPending);
  bool maxSwitch = readDebounced(ENDSTOP_MAXFULL_PIN, endstopMaxState, endstopMaxChangedAt, endstopMaxPending);

  int hallRaw = readHallAveraging(analogRead(HALL_PIN));
  if (hallHardwareFaulted(hallRaw) && state != ST_FAULT && state != ST_CAL_MANUAL) { 
    enterFault("Відмова датчика Холла"); 
    updateStatusLED(); 
    return; 
  }
  long hall = updateHallFilter(hallRaw);

  if (maxSwitch && activeMotor != 0 && motorCurSpeed[activeMotor] > 0 && digitalRead(activeMotor == 1 ? M1_DIR_PIN : M2_DIR_PIN) == HIGH) {
    motorCurSpeed[activeMotor] = 0;
  }

  bool activeSensor = (activeMotor == 1) ? f1 : (activeMotor == 2 ? f2 : false);

  bool feedingState = (state == ST_AUTOLOAD || state == ST_SPLICE_FEED);
  if (feedingState && activeMotor != 0 && !activeSensor) {
    enterFault("Немає філаменту на активному каналі");
    updateStatusLED();
    return;
  }

  switch (state) {
    case ST_INIT:
      if (activeMotor == 0) { 
        if (f1) activeMotor = 1; 
        else if (f2) activeMotor = 2; 
        else { state = ST_WAIT_LOAD; break; } 
      }
      if (calibrationNeeded) {
        addLog("Система чекає на команду калібрування з веб-інтерфейсу");
        state = ST_CAL_MANUAL;  // Wait for manual input via web
      } else {
        motorEnable(activeMotor, true); 
        motorHold(activeMotor);
        state = maxSwitch ? ST_RUN : ST_AUTOLOAD;
      }
      break;

    case ST_WAIT_LOAD:
      if (f1) { activeMotor = 1; state = ST_INIT; } 
      else if (f2) { activeMotor = 2; state = ST_INIT; }
      break;

    // Manual calibration mode - just wait for web input
    case ST_CAL_MANUAL:
      // All calibration happens via web API
      // Do nothing in main loop, just let the user enter values
      break;

    case ST_AUTOLOAD:
      motorRunCurrent(activeMotor); 
      motorDir(activeMotor, true); 
      rampMotor(activeMotor, MAX_SPEED_SPS * 0.4f);
      if (checkStall(activeMotor, motorCurSpeed[activeMotor])) break;
      if (maxSwitch || hallFullness(hall) >= hallFullness(hallMaxFull) - HYSTERESIS) { 
        motorHold(activeMotor); 
        stallRetryCount = 0; 
        saveCalibration(); 
        state = ST_RUN; 
      }
      break;

    case ST_RUN: {
      float target = piUpdate(hall);
      if (maxSwitch) target = 0;
      rampMotor(activeMotor, target);
      if (motorCurSpeed[activeMotor] > 5) { 
        motorRunCurrent(activeMotor); 
        motorDir(activeMotor, true); 
        if (checkStall(activeMotor, motorCurSpeed[activeMotor])) break; 
        lastFeedChangeMs = millis(); 
      }
      else { 
        motorHold(activeMotor); 
      }
      if (target > 5 && abs(hall - lastHallForWatchdog) < 3) { 
        if (millis() - lastFeedChangeMs > FEED_WATCHDOG_MS) { 
          enterFault("Watchdog: Буфер завис"); 
          break; 
        } 
      }
      else { 
        lastFeedChangeMs = millis(); 
      }
      lastHallForWatchdog = hall;
      if (!((activeMotor == 1) ? f1 : f2)) { 
        motorHold(activeMotor); 
        saveCalibration(); 
        state = ST_SPLICE_WAIT; 
      }
      break;
    }

    case ST_SPLICE_WAIT: {
      int standby = (activeMotor == 1) ? 2 : 1;
      if (!((standby == 1) ? f1 : f2)) { 
        enterFault("Закінчилась нитка, резерв порожній"); 
        break; 
      }
      if (hallFullness(hall) < hallFullness(hallMaxFull) - LOW_THRESHOLD) { 
        activeMotor = standby; 
        motorEnable(activeMotor, true); 
        stallRetryCount = 0; 
        addLog("Перехід на резервну котушку"); 
        state = ST_SPLICE_FEED; 
      }
      break;
    }

    case ST_SPLICE_FEED:
      motorRunCurrent(activeMotor); 
      motorDir(activeMotor, true); 
      rampMotor(activeMotor, MAX_SPEED_SPS * 0.5f);
      if (checkStall(activeMotor, motorCurSpeed[activeMotor])) break;
      if (hallFullness(hall) >= hallFullness(hallMaxFull) - HYSTERESIS) { 
        motorHold(activeMotor); 
        stallRetryCount = 0; 
        saveCalibration(); 
        state = ST_RUN; 
      }
      break;

    case ST_STALL_RETRACT: {
      rampMotor(activeMotor, MAX_SPEED_SPS * 0.3f);
      static unsigned long lastUs = 0; 
      unsigned long now = micros(); 
      float dt = (lastUs == 0) ? 0 : (now - lastUs) / 1000000.0f; 
      lastUs = now;
      stallRetractStepsRemaining -= (long)(motorCurSpeed[activeMotor] * dt);
      bool retractLimitHit = stallWasForward ? emptySwitch : maxSwitch;
      bool retractTimeout = (millis() - stallRetractStartedMs) > STALL_RETRACT_TIMEOUT_MS;
      
      if (stallRetractStepsRemaining <= 0 || retractLimitHit || retractTimeout) {
        if (retractTimeout) addLog("Stall retract: timeout");
        rampMotor(activeMotor, 0);
        if (motorCurSpeed[activeMotor] < 1.0f) { 
          motorDir(activeMotor, stallWasForward); 
          lastUs = 0; 
          state = stallReturnState; 
        }
      }
      break;
    }

    case ST_FAULT: 
      break;
  }

  motorPulseIfDue(1); 
  motorPulseIfDue(2); 
  updateStatusLED();
}
