/*
 * ================================================================
 *   L U M B E R J A C K   F U R Y  -  Native Graphical Championship
 * ================================================================
 *
 *   A high-performance Win32 graphical axe-throwing game featuring:
 *   - Native high-res 1024x620 window (no console clipping!)
 *   - Full 60 FPS double-buffered smooth GDI rendering
 *   - Full-size solid archery target with gold, red, white & blue rings
 *   - Screen-wide smooth trajectory arc with live Target Lock crosshair
 *   - 5 escalating moving target challenges (Elevator, Runner, Figure-8, Gusts, Chaos)
 *   - Sleek, modern dashboard UI with wind compass, streak multipliers, and telemetry
 *   - Non-blocking 8-bit sound effects (toggle with M)
 *
 *   Compile (MinGW):  g++ -o axe_game.exe axe_game.cpp -O2 -mwindows -lgdi32 -luser32 -lkernel32
 * ================================================================
 */

#include <windows.h>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <string>
#include <vector>
#include <algorithm>

// ================================================================
//  Constants & Dimensions
// ================================================================
static const int   WIN_W      = 1024;        // Client area width
static const int   WIN_H      = 620;         // Client area height
static const float PI_F       = 3.14159265f;
static const float GRAV       = 480.0f;      // Gravity in pixels/sec^2
static const float DT         = 1.0f / 60.0f;// 60 FPS physics tick
static const float V_REF      = 650.0f;      // Fixed reference trajectory velocity (pixels/sec)
static const int   ROUNDS     = 5;           // Match rounds
static const int   GROUND_Y   = 490;         // Ground horizon line

// Target physical movement bounds (kept completely inside screen)
static const float TGT_MIN_X  = 650.0f;      // Leftmost target limit
static const float TGT_MAX_X  = 880.0f;      // Rightmost target limit (safe margin from 1024)
static const float TGT_MIN_Y  = 160.0f;      // Highest elevation
static const float TGT_MAX_Y  = 360.0f;      // Lowest elevation
static const float TGT_RADIUS = 55.0f;       // Outer board radius (px)

// Overhead Track coordinates
static const int   TRACK_Y    = 75;          // Rail vertical position
static const int   TRACK_X1   = 580;         // Left support tower
static const int   TRACK_X2   = 960;         // Right support tower

// ================================================================
//  Structures
// ================================================================
struct V2 {
    float x, y;
    V2(float a = 0, float b = 0) : x(a), y(b) {}
};

struct Particle {
    V2    p, v;
    float life, maxLife;
    COLORREF col;
    int   size;
};

struct Leaf {
    float x, y, spd, rot, rotSpd;
    COLORREF col;
};

struct StuckAxe {
    float ox, oy;   // Offset relative to target center
    float rot;      // Rotation angle
};

struct TrailPoint {
    float x, y;
    float life;
};

enum GameState {
    STATE_TITLE,
    STATE_AIM,
    STATE_CHARGE,
    STATE_FLY,
    STATE_RESULT,
    STATE_GAMEOVER
};

enum Pattern {
    PAT_VERTICAL = 0,   // Round 1: Elevator vertical crane
    PAT_HORIZONTAL,     // Round 2: Rail runner
    PAT_FIGURE8,        // Round 3: Lissajous curve / Figure-8 swing
    PAT_GUSTS,          // Round 4: Wind buffeted erratic shifts
    PAT_HYPER           // Round 5: Extreme agility evasive drone
};

enum CalibRating {
    CALIB_NONE,
    CALIB_PERFECT,
    CALIB_GREAT,
    CALIB_GOOD,
    CALIB_UNDER,
    CALIB_OVER
};

// ================================================================
//  Global Game Variables
// ================================================================
static HWND         ghWnd      = NULL;
static HDC          gMemDC     = NULL;
static HBITMAP      gMemBM     = NULL;
static HBITMAP      gOldBM     = NULL;

static GameState    gState     = STATE_TITLE;
static float        gAngle     = -22.0f;      // Degrees (-60 to +10)
static float        gAimPower  = 65.0f;       // Dialed power in aim mode (15..100%)
static float        gPower     = 0.0f;        // Dynamic charge power
static float        gWind      = 0.0f;        // Wind speed (-15..+15)
static int          gRound     = 0;           // Round index (0..4)
static int          gScore     = 0;           // Total score
static int          gLastScore = 0;           // Last throw points
static int          gStreak    = 0;           // Consecutive hits
static int          gMaxStreak = 0;           // Best streak in match
static float        gTimer     = 0.0f;        // State timer
static bool         gSound     = true;        // Audio toggle

// Interactive Speed & Flight-Time Calibration Telemetry
static float        gSpeedMult   = 1.0f;       // Speed multiplier scaling travel time
static float        gFlightTime  = 0.0f;       // Active flight elapsed time
static float        gCalibPower  = 65.0f;      // Last calibrated throw power
static float        gCalibSpeed  = 707.5f;     // Last calibrated axe speed (px/s)
static int          gCalibBonus  = 0;          // Calibration timing score bonus
static CalibRating  gCalibRating = CALIB_NONE; // Rating: Perfect, Great, Good, Under, Over
static std::string  gCalibMsg    = "";         // Telemetry readout text
static float        gCalibFlash  = 0.0f;       // Visual flash timer

// Target dynamics
static float        gTgtX      = 760.0f;
static float        gTgtY      = 240.0f;
static float        gTgtVX     = 0.0f;
static float        gTgtVY     = 0.0f;
static float        gTgtSpd    = 90.0f;
static float        gTgtTime   = 0.0f;
static Pattern      gPattern   = PAT_VERTICAL;
static const char*  gPatName   = "";

// Calculate estimated flight duration to target based on speed
static float calcFlightTime(float pow) {
    float rad = gAngle * PI_F / 180.0f;
    float baseVx = cosf(rad) * V_REF;
    if (baseVx <= 1.0f) baseVx = 1.0f;
    float distX = (std::max)(gTgtX - 170.0f, 50.0f);
    float spd = pow * 7.5f + 220.0f;
    float mult = spd / V_REF;
    return (distX / baseVx) / mult;
}

// Axe physical flight
static V2           gAxeP, gAxeV;
static float        gAxeRot    = 0.0f;
static float        gAxeSpin   = 0.0f;
static bool         gAxeActive = false;

// Visual FX
static std::string             gResultMsg;
static std::vector<Particle>   gParticles;
static std::vector<StuckAxe>   gStuckAxes;
static std::vector<TrailPoint> gTrail;
static std::vector<Leaf>       gLeaves;

// Cached GDI fonts
static HFONT hFontTitle = NULL;
static HFONT hFontLarge = NULL;
static HFONT hFontBold  = NULL;
static HFONT hFontNorm  = NULL;
static HFONT hFontSmall = NULL;

// ================================================================
//  Non-blocking Audio
// ================================================================
struct BeepParams { int freq, dur; };
static DWORD WINAPI BeepThread(LPVOID param) {
    BeepParams* bp = (BeepParams*)param;
    Beep(bp->freq, bp->dur);
    delete bp;
    return 0;
}

static void playSound(int freq, int dur) {
    if (!gSound) return;
    BeepParams* bp = new BeepParams{ freq, dur };
    HANDLE hThread = CreateThread(NULL, 0, BeepThread, bp, 0, NULL);
    if (hThread) CloseHandle(hThread);
}

// ================================================================
//  GDI Drawing Helpers
// ================================================================
static void fillSolidRect(HDC hdc, int x, int y, int w, int h, COLORREF col) {
    RECT r = { x, y, x + w, y + h };
    HBRUSH br = CreateSolidBrush(col);
    FillRect(hdc, &r, br);
    DeleteObject(br);
}

static void drawCircle(HDC hdc, int cx, int cy, int r, COLORREF fillCol, COLORREF strokeCol, int strokeWidth = 1) {
    HPEN pen = strokeWidth > 0 ? CreatePen(PS_SOLID, strokeWidth, strokeCol) : (HPEN)GetStockObject(NULL_PEN);
    HBRUSH br = CreateSolidBrush(fillCol);
    HPEN oldPen = (HPEN)SelectObject(hdc, pen);
    HBRUSH oldBr = (HBRUSH)SelectObject(hdc, br);

    Ellipse(hdc, cx - r, cy - r, cx + r, cy + r);

    SelectObject(hdc, oldPen);
    SelectObject(hdc, oldBr);
    DeleteObject(br);
    if (strokeWidth > 0) DeleteObject(pen);
}

static void drawLine(HDC hdc, int x1, int y1, int x2, int y2, COLORREF col, int width = 1) {
    HPEN pen = CreatePen(PS_SOLID, width, col);
    HPEN oldPen = (HPEN)SelectObject(hdc, pen);
    MoveToEx(hdc, x1, y1, NULL);
    LineTo(hdc, x2, y2);
    SelectObject(hdc, oldPen);
    DeleteObject(pen);
}

static void drawRoundedBox(HDC hdc, int x, int y, int w, int h, int rad, COLORREF fillCol, COLORREF strokeCol, int strokeWidth = 1) {
    HPEN pen = strokeWidth > 0 ? CreatePen(PS_SOLID, strokeWidth, strokeCol) : (HPEN)GetStockObject(NULL_PEN);
    HBRUSH br = CreateSolidBrush(fillCol);
    HPEN oldPen = (HPEN)SelectObject(hdc, pen);
    HBRUSH oldBr = (HBRUSH)SelectObject(hdc, br);

    RoundRect(hdc, x, y, x + w, y + h, rad, rad);

    SelectObject(hdc, oldPen);
    SelectObject(hdc, oldBr);
    DeleteObject(br);
    if (strokeWidth > 0) DeleteObject(pen);
}

static void drawCenteredText(HDC hdc, const std::string& str, int cx, int y, HFONT font, COLORREF col) {
    HFONT oldFont = (HFONT)SelectObject(hdc, font);
    SetTextColor(hdc, col);
    SetBkMode(hdc, TRANSPARENT);
    SIZE sz;
    GetTextExtentPoint32A(hdc, str.c_str(), (int)str.size(), &sz);
    TextOutA(hdc, cx - sz.cx / 2, y, str.c_str(), (int)str.size());
    SelectObject(hdc, oldFont);
}

static void drawTextAt(HDC hdc, const std::string& str, int x, int y, HFONT font, COLORREF col) {
    HFONT oldFont = (HFONT)SelectObject(hdc, font);
    SetTextColor(hdc, col);
    SetBkMode(hdc, TRANSPARENT);
    TextOutA(hdc, x, y, str.c_str(), (int)str.size());
    SelectObject(hdc, oldFont);
}

// ================================================================
//  Particles & FX
// ================================================================
static void spawnSparks(float x, float y, int count, COLORREF col) {
    for (int i = 0; i < count; ++i) {
        Particle p;
        p.p = V2(x, y);
        float a = ((float)rand() / (float)RAND_MAX) * 2.0f * PI_F;
        float s = 40.0f + ((float)rand() / (float)RAND_MAX) * 220.0f;
        p.v = V2(cosf(a) * s, sinf(a) * s - 70.0f);
        p.life = 0.0f;
        p.maxLife = 0.4f + ((float)rand() / (float)RAND_MAX) * 0.45f;
        p.col = col;
        p.size = 2 + rand() % 3;
        gParticles.push_back(p);
    }
}

static void updateParticles() {
    for (auto it = gParticles.begin(); it != gParticles.end(); ) {
        it->p.x += it->v.x * DT;
        it->p.y += it->v.y * DT;
        it->v.y += GRAV * 0.5f * DT;
        it->life += DT;
        if (it->life >= it->maxLife) it = gParticles.erase(it);
        else ++it;
    }
}

static void initLeaves() {
    gLeaves.clear();
    for (int i = 0; i < 30; ++i) {
        Leaf l;
        l.x = (float)(rand() % WIN_W);
        l.y = (float)(rand() % GROUND_Y);
        l.spd = 40.0f + (float)(rand() % 60);
        l.rot = ((float)rand() / (float)RAND_MAX) * 2.0f * PI_F;
        l.rotSpd = -2.0f + ((float)rand() / (float)RAND_MAX) * 4.0f;
        l.col = (rand() % 2 == 0) ? RGB(46, 139, 87) : RGB(218, 165, 32);
        gLeaves.push_back(l);
    }
}

static void updateLeaves() {
    for (auto& l : gLeaves) {
        l.x += (l.spd + gWind * 18.0f) * DT;
        l.y += 25.0f * DT + sinf(l.rot) * 0.6f;
        l.rot += l.rotSpd * DT;
        if (l.x > WIN_W + 20) l.x = -20;
        if (l.x < -20)        l.x = WIN_W + 20;
        if (l.y > GROUND_Y)   l.y = 80;
    }
}

// ================================================================
//  Target Dynamics & Modes
// ================================================================
static void initTargetRound() {
    gTgtTime = 0.0f;
    gPattern = (Pattern)(gRound % 5);

    switch (gPattern) {
    case PAT_VERTICAL:
        gPatName = "ELEVATOR CRANE";
        gTgtX   = 760.0f;
        gTgtY   = 240.0f;
        gTgtSpd = 110.0f;
        gTgtVX  = 0.0f;
        gTgtVY  = 110.0f;
        break;

    case PAT_HORIZONTAL:
        gPatName = "RAIL RUNNER";
        gTgtX   = 740.0f;
        gTgtY   = 240.0f;
        gTgtSpd = 150.0f;
        gTgtVX  = 150.0f;
        gTgtVY  = 0.0f;
        break;

    case PAT_FIGURE8:
        gPatName = "FIGURE-8 ORBIT";
        gTgtX   = 760.0f;
        gTgtY   = 250.0f;
        gTgtSpd = 2.0f;
        gTgtVX  = 0.0f;
        gTgtVY  = 0.0f;
        break;

    case PAT_GUSTS:
        gPatName = "GUST SURFER";
        gTgtX   = 760.0f;
        gTgtY   = 220.0f;
        gTgtSpd = 180.0f;
        gTgtVX  = 120.0f;
        gTgtVY  = -120.0f;
        break;

    case PAT_HYPER:
        gPatName = "CHAOS DRONE (2X POINTS!)";
        gTgtX   = 760.0f;
        gTgtY   = 230.0f;
        gTgtSpd = 230.0f;
        gTgtVX  = 160.0f;
        gTgtVY  = 150.0f;
        break;
    }
}

static void updateTarget() {
    gTgtTime += DT;

    if (gPattern == PAT_FIGURE8) {
        gTgtX  = 760.0f + 95.0f * sinf(gTgtTime * 2.2f);
        gTgtY  = 240.0f + 65.0f * sinf(gTgtTime * 4.4f);
        gTgtVX = 209.0f * cosf(gTgtTime * 2.2f);
        gTgtVY = 286.0f * cosf(gTgtTime * 4.4f);
    } else {
        gTgtX += gTgtVX * DT;
        gTgtY += gTgtVY * DT;

        // Occasional gust acceleration in Rounds 4 & 5
        if ((gPattern == PAT_GUSTS || gPattern == PAT_HYPER) && (rand() % 45 == 0)) {
            float mult = (gPattern == PAT_HYPER) ? 1.3f : 1.1f;
            gTgtVX = ((rand() % 2 == 0) ? 1.0f : -1.0f) * gTgtSpd * mult;
            gTgtVY = ((rand() % 2 == 0) ? 1.0f : -1.0f) * gTgtSpd * mult;
        }

        // Horizontal bounce within safe, fully visible range
        if (gTgtX <= TGT_MIN_X) { gTgtX = TGT_MIN_X; gTgtVX =  fabsf(gTgtVX); }
        if (gTgtX >= TGT_MAX_X) { gTgtX = TGT_MAX_X; gTgtVX = -fabsf(gTgtVX); }

        // Vertical bounce
        if (gTgtY <= TGT_MIN_Y) { gTgtY = TGT_MIN_Y; gTgtVY =  fabsf(gTgtVY); }
        if (gTgtY >= TGT_MAX_Y) { gTgtY = TGT_MAX_Y; gTgtVY = -fabsf(gTgtVY); }
    }
}

// Distance from target centre
static float targetDist(float x, float y) {
    float dx = x - gTgtX;
    float dy = y - gTgtY;
    return sqrtf(dx * dx + dy * dy);
}

// Ring scoring calculation
static int calcScore(float dist) {
    int mult = (gPattern == PAT_HYPER) ? 2 : 1;
    if (dist <= 12.0f) return 100 * mult;   // Bullseye
    if (dist <= 26.0f) return 75  * mult;   // Red Inner Ring
    if (dist <= 40.0f) return 50  * mult;   // White Middle Ring
    if (dist <= 55.0f) return 25  * mult;   // Blue Outer Ring
    return 0;
}

// ================================================================
//  Axe Throwing & Physics
// ================================================================
static void startThrow(float pow) {
    float rad = gAngle * PI_F / 180.0f;
    float spd = pow * 7.5f + 220.0f;

    gCalibPower = pow;
    gCalibSpeed = spd;
    gSpeedMult  = spd / V_REF;
    gFlightTime = 0.0f;

    // Fixed reference velocity ensures the physical trajectory path is constant
    gAxeP    = V2(170.0f, 395.0f);
    gAxeV    = V2(cosf(rad) * V_REF, sinf(rad) * V_REF);
    gAxeRot  = 0.0f;
    gAxeSpin = 12.0f + pow * 0.12f;
    gAxeActive = true;
    gTrail.clear();
    gState   = STATE_FLY;

    playSound(600, 30);
}

static void updateAxe() {
    if (!gAxeActive) return;

    gFlightTime += DT;

    // Physical travel scales with gSpeedMult: exact same trajectory path, reduced travel time!
    float effDT = DT * gSpeedMult;
    gAxeP.x += gAxeV.x * effDT;
    gAxeP.y += gAxeV.y * effDT;
    gAxeV.y += GRAV * effDT;
    gAxeV.x += gWind * 6.0f * effDT;
    gAxeRot += gAxeSpin * effDT;

    // Flight trail
    gTrail.push_back({ gAxeP.x, gAxeP.y, 0.4f });
    for (auto& t : gTrail) t.life -= DT;
    while (!gTrail.empty() && gTrail.front().life <= 0.0f) gTrail.erase(gTrail.begin());

    // ── Hit Moving Target? ──
    float d = targetDist(gAxeP.x, gAxeP.y);
    if (d <= TGT_RADIUS) {
        gLastScore = calcScore(d);
        gStreak++;
        if (gStreak > gMaxStreak) gMaxStreak = gStreak;
        int bonus = (gStreak > 1) ? (gStreak - 1) * 25 : 0;
        gScore += gLastScore + bonus;

        gAxeActive = false;
        // Anchor axe relative to target's center so it rides with it
        gStuckAxes.push_back({ gAxeP.x - gTgtX, gAxeP.y - gTgtY, gAxeRot });

        spawnSparks(gAxeP.x, gAxeP.y, 45, RGB(255, 215, 0));
        spawnSparks(gAxeP.x, gAxeP.y, 25, RGB(180, 80, 20));

        if (gLastScore >= 100 * ((gPattern == PAT_HYPER) ? 2 : 1)) {
            gResultMsg = "*** GOLDEN BULLSEYE!! *** +" + std::to_string(gLastScore);
            playSound(900, 60);
            playSound(1250, 90);
        } else if (gLastScore >= 75) {
            gResultMsg = "RED RING HIT! +" + std::to_string(gLastScore);
            playSound(600, 50);
        } else if (gLastScore >= 50) {
            gResultMsg = "WHITE RING HIT! +" + std::to_string(gLastScore);
            playSound(440, 45);
        } else {
            gResultMsg = "BLUE RING HIT! +" + std::to_string(gLastScore);
            playSound(350, 40);
        }

        gTimer = 0.0f;
        gState = STATE_RESULT;
        return;
    }

    // ── Hit Ground? ──
    if (gAxeP.y >= GROUND_Y) {
        gAxeActive = false;
        gStreak = 0;
        spawnSparks(gAxeP.x, (float)GROUND_Y, 20, RGB(139, 90, 43));
        gLastScore = 0;
        gResultMsg = "MISS! The axe dug into the dirt!";
        playSound(150, 90);
        gTimer = 0.0f;
        gState = STATE_RESULT;
        return;
    }

    // ── Flew Off Screen? ──
    if (gAxeP.x > WIN_W + 50 || gAxeP.x < -50 || gAxeP.y < -80) {
        gAxeActive = false;
        gStreak = 0;
        gLastScore = 0;
        gResultMsg = "MISS! The axe flew past the target range!";
        playSound(120, 80);
        gTimer = 0.0f;
        gState = STATE_RESULT;
    }
}

static void newRound() {
    gWind       = -8.0f + ((float)rand() / (float)RAND_MAX) * 16.0f; // -8 .. +8
    gAngle      = -22.0f;
    gPower      = 0.0f;
    gAxeActive  = false;
    gResultMsg.clear();
    gLastScore  = 0;
    gTrail.clear();
    gFlightTime = 0.0f;

    initTargetRound();
    gState = STATE_AIM;
}

// ================================================================
//  Rendering Systems
// ================================================================

// 1. Sky, Moon, Stars, Distant Forest, Grass
static void renderEnvironment(HDC hdc) {
    // Night Sky gradient
    for (int y = 0; y < GROUND_Y; ++y) {
        float t = (float)y / (float)GROUND_Y;
        int r = (int)(10  + t * 25);
        int g = (int)(15  + t * 35);
        int b = (int)(45  + t * 65);
        drawLine(hdc, 0, y, WIN_W, y, RGB(r, g, b));
    }

    // Moon
    drawCircle(hdc, 920, 95, 24, RGB(255, 250, 205), RGB(240, 230, 140), 2);
    drawCircle(hdc, 910, 90, 20, RGB(18, 26, 60), RGB(18, 26, 60), 0); // Crescent cut

    // Distant Pine Forest Silhouettes
    for (int x = 200; x < WIN_W; x += 65) {
        POINT pts[3] = { { x, GROUND_Y }, { x + 30, GROUND_Y - 95 }, { x + 60, GROUND_Y } };
        HBRUSH br = CreateSolidBrush(RGB(15, 30, 35));
        HPEN pen = (HPEN)GetStockObject(NULL_PEN);
        SelectObject(hdc, br);
        SelectObject(hdc, pen);
        Polygon(hdc, pts, 3);
        DeleteObject(br);
    }

    // Ground & Grass
    fillSolidRect(hdc, 0, GROUND_Y, WIN_W, WIN_H - GROUND_Y, RGB(34, 100, 34)); // Lush green
    drawLine(hdc, 0, GROUND_Y, WIN_W, GROUND_Y, RGB(50, 160, 50), 2);            // Horizon highlight
    fillSolidRect(hdc, 0, GROUND_Y + 30, WIN_W, WIN_H - GROUND_Y - 30, RGB(28, 80, 28)); // Deep earth

    // Distance Stakes
    int dists[3] = { 450, 650, 850 };
    const char* dlbls[3] = { "20m", "30m", "40m" };
    for (int i = 0; i < 3; ++i) {
        int sx = dists[i];
        fillSolidRect(hdc, sx - 3, GROUND_Y - 24, 6, 24, RGB(139, 90, 43));
        drawTextAt(hdc, dlbls[i], sx - 10, GROUND_Y + 4, hFontSmall, RGB(200, 230, 200));
    }

    // Drifting Wind Leaves
    for (auto& l : gLeaves) {
        int lx = (int)l.x, ly = (int)l.y;
        drawCircle(hdc, lx, ly, 3, l.col, RGB(0, 0, 0), 1);
    }
}

// 2. Overhead Mechanical Track & Full Moving Target
static void renderTargetSystem(HDC hdc) {
    int cx = (int)gTgtX;
    int cy = (int)gTgtY;

    // 1. Steel Support Towers (Left & Right)
    fillSolidRect(hdc, TRACK_X1 - 5, TRACK_Y, 10, GROUND_Y - TRACK_Y, RGB(70, 75, 85));
    fillSolidRect(hdc, TRACK_X2 - 5, TRACK_Y, 10, GROUND_Y - TRACK_Y, RGB(70, 75, 85));
    // Cross-braces
    drawLine(hdc, TRACK_X1, TRACK_Y + 80, TRACK_X1 + 35, GROUND_Y, RGB(60, 65, 75), 2);
    drawLine(hdc, TRACK_X2, TRACK_Y + 80, TRACK_X2 - 35, GROUND_Y, RGB(60, 65, 75), 2);

    // 2. Overhead Track I-Beam Rail
    fillSolidRect(hdc, TRACK_X1 - 20, TRACK_Y - 6, (TRACK_X2 - TRACK_X1) + 40, 12, RGB(90, 95, 105));
    fillSolidRect(hdc, TRACK_X1 - 20, TRACK_Y - 10, (TRACK_X2 - TRACK_X1) + 40, 4, RGB(140, 145, 155));

    // 3. Motorized Trolley Carriage (moves with cx)
    drawRoundedBox(hdc, cx - 22, TRACK_Y - 14, 44, 20, 4, RGB(50, 55, 65), RGB(255, 215, 0), 2);
    // Brass Pulley Wheels
    drawCircle(hdc, cx - 14, TRACK_Y - 14, 6, RGB(218, 165, 32), RGB(0, 0, 0), 1);
    drawCircle(hdc, cx + 14, TRACK_Y - 14, 6, RGB(218, 165, 32), RGB(0, 0, 0), 1);

    // 4. Dual Steel Suspension Cables
    drawLine(hdc, cx - 14, TRACK_Y + 6, cx - 14, cy - (int)TGT_RADIUS, RGB(190, 195, 205), 2);
    drawLine(hdc, cx + 14, TRACK_Y + 6, cx + 14, cy - (int)TGT_RADIUS, RGB(190, 195, 205), 2);

    // 5. Full Solid High-Contrast Archery Target Board
    // Outer Timber Backboard (radius 60)
    drawCircle(hdc, cx, cy, 60, RGB(101, 67, 33), RGB(180, 130, 70), 3);
    // Outer Rivet rim
    for (int a = 0; a < 8; ++a) {
        float ang = a * (PI_F / 4.0f);
        int rx = cx + (int)(cosf(ang) * 56.0f);
        int ry = cy + (int)(sinf(ang) * 56.0f);
        drawCircle(hdc, rx, ry, 2, RGB(255, 215, 0), RGB(0, 0, 0), 1);
    }

    // Ring 4: Solid Blue Ring (25 pts)
    drawCircle(hdc, cx, cy, 52, RGB(30, 144, 255), RGB(20, 80, 180), 2);

    // Ring 3: Solid White Ring (50 pts)
    drawCircle(hdc, cx, cy, 38, RGB(248, 248, 255), RGB(180, 180, 190), 2);

    // Ring 2: Solid Red Ring (75 pts)
    drawCircle(hdc, cx, cy, 25, RGB(220, 20, 60), RGB(140, 10, 30), 2);

    // Ring 1: Solid Gold Bullseye (100 pts)
    drawCircle(hdc, cx, cy, 12, RGB(255, 215, 0), RGB(200, 140, 0), 2);

    // Center Crosshair
    drawLine(hdc, cx - 6, cy, cx + 6, cy, RGB(0, 0, 0), 1);
    drawLine(hdc, cx, cy - 6, cx, cy + 6, RGB(0, 0, 0), 1);

    // 6. Target Telemetry Badge & Reticle Brackets
    drawRoundedBox(hdc, cx - 45, cy - (int)TGT_RADIUS - 28, 90, 20, 4, RGB(20, 25, 35), RGB(255, 215, 0), 1);
    char badge[32];
    sprintf(badge, "SPEED: %.0f", fabsf(gTgtVX) + fabsf(gTgtVY));
    drawCenteredText(hdc, badge, cx, cy - (int)TGT_RADIUS - 26, hFontSmall, RGB(255, 215, 0));

    // Corner targeting brackets
    int bS = 70;
    HPEN penB = CreatePen(PS_SOLID, 2, RGB(255, 215, 0));
    HPEN oldPen = (HPEN)SelectObject(hdc, penB);
    // Top-left
    MoveToEx(hdc, cx - bS, cy - bS + 10, NULL); LineTo(hdc, cx - bS, cy - bS); LineTo(hdc, cx - bS + 10, cy - bS);
    // Top-right
    MoveToEx(hdc, cx + bS, cy - bS + 10, NULL); LineTo(hdc, cx + bS, cy - bS); LineTo(hdc, cx + bS - 10, cy - bS);
    // Bottom-left
    MoveToEx(hdc, cx - bS, cy + bS - 10, NULL); LineTo(hdc, cx - bS, cy + bS); LineTo(hdc, cx - bS + 10, cy + bS);
    // Bottom-right
    MoveToEx(hdc, cx + bS, cy + bS - 10, NULL); LineTo(hdc, cx + bS, cy + bS); LineTo(hdc, cx + bS - 10, cy + bS);
    SelectObject(hdc, oldPen);
    DeleteObject(penB);

    // 7. Embedded Axes (stuck from previous hits, moving synchronously!)
    for (auto& sa : gStuckAxes) {
        int ax = cx + (int)sa.ox;
        int ay = cy + (int)sa.oy;
        // Mini stuck axe
        drawLine(hdc, ax, ay, ax + 14, ay + 14, RGB(139, 69, 19), 3); // Handle
        drawCircle(hdc, ax, ay, 4, RGB(192, 192, 192), RGB(255, 255, 255), 1); // Blade
    }
}

// 3. Detailed Lumberjack Character
static void renderLumberjack(HDC hdc, bool followThrough) {
    int bx = 110, by = GROUND_Y;

    // ── 1. Soft Ground Shadow under boots ──
    drawCircle(hdc, bx - 6, by + 1, 24, RGB(18, 55, 18), RGB(18, 55, 18), 0);
    drawCircle(hdc, bx + 12, by + 1, 20, RGB(18, 55, 18), RGB(18, 55, 18), 0);

    // ── 2. Heavy Leather Logging Boots with Lug Soles & Cross-Laces ──
    // Left Boot (Front)
    fillSolidRect(hdc, bx - 19, by - 6, 18, 6, RGB(30, 20, 15)); // Deep tread lug sole
    for (int t = bx - 18; t < bx - 2; t += 4) {
        drawLine(hdc, t, by - 6, t, by - 1, RGB(15, 10, 8), 1);   // Tread grip cuts
    }
    drawRoundedBox(hdc, bx - 19, by - 24, 18, 19, 4, RGB(85, 48, 26), RGB(50, 25, 15), 1); // Oiled leather upper
    drawRoundedBox(hdc, bx - 19, by - 14, 11, 9, 3, RGB(105, 60, 32), RGB(50, 25, 15), 1); // Toe cap
    // Cross-laces & metal eyelets
    drawLine(hdc, bx - 15, by - 20, bx - 7, by - 16, RGB(225, 195, 140), 1);
    drawLine(hdc, bx - 7,  by - 20, bx - 15, by - 16, RGB(225, 195, 140), 1);
    drawLine(hdc, bx - 15, by - 16, bx - 7, by - 12, RGB(225, 195, 140), 1);
    drawLine(hdc, bx - 7,  by - 16, bx - 15, by - 12, RGB(225, 195, 140), 1);
    drawCircle(hdc, bx - 16, by - 20, 1, RGB(255, 215, 0), RGB(0, 0, 0), 1);
    drawCircle(hdc, bx - 6,  by - 20, 1, RGB(255, 215, 0), RGB(0, 0, 0), 1);

    // Right Boot (Back)
    fillSolidRect(hdc, bx + 3, by - 6, 18, 6, RGB(30, 20, 15)); // Deep tread lug sole
    for (int t = bx + 4; t < bx + 20; t += 4) {
        drawLine(hdc, t, by - 6, t, by - 1, RGB(15, 10, 8), 1);
    }
    drawRoundedBox(hdc, bx + 3, by - 24, 18, 19, 4, RGB(80, 44, 24), RGB(45, 22, 12), 1);
    drawRoundedBox(hdc, bx + 10, by - 14, 11, 9, 3, RGB(100, 56, 30), RGB(45, 22, 12), 1);
    // Cross-laces
    drawLine(hdc, bx + 7,  by - 20, bx + 15, by - 16, RGB(225, 195, 140), 1);
    drawLine(hdc, bx + 15, by - 20, bx + 7,  by - 16, RGB(225, 195, 140), 1);
    drawLine(hdc, bx + 7,  by - 16, bx + 15, by - 12, RGB(225, 195, 140), 1);
    drawLine(hdc, bx + 15, by - 16, bx + 7,  by - 12, RGB(225, 195, 140), 1);

    // ── 3. Denim Work Jeans with Rolled Cuffs & Golden Stitching ──
    // Rolled denim cuffs (lighter underside denim fabric)
    drawRoundedBox(hdc, bx - 20, by - 28, 20, 6, 2, RGB(90, 115, 155), RGB(50, 70, 105), 1);
    drawRoundedBox(hdc, bx + 2,  by - 28, 20, 6, 2, RGB(90, 115, 155), RGB(50, 70, 105), 1);
    drawLine(hdc, bx - 20, by - 28, bx, by - 28, RGB(255, 215, 0), 1); // Gold hem stitch
    drawLine(hdc, bx + 2,  by - 28, bx + 22, by - 28, RGB(255, 215, 0), 1);

    // Denim pant legs (rich indigo with seams)
    drawRoundedBox(hdc, bx - 19, by - 70, 18, 44, 5, RGB(45, 72, 118), RGB(28, 45, 80), 1); // Left leg
    drawRoundedBox(hdc, bx + 3,  by - 70, 18, 44, 5, RGB(50, 78, 125), RGB(28, 45, 80), 1); // Right leg

    // Reinforced double-knee work patches
    drawRoundedBox(hdc, bx - 17, by - 52, 14, 16, 3, RGB(58, 88, 138), RGB(35, 55, 95), 1);
    drawRoundedBox(hdc, bx + 5,  by - 52, 14, 16, 3, RGB(62, 92, 142), RGB(35, 55, 95), 1);
    // Gold contrast seam stitching
    drawLine(hdc, bx - 18, by - 68, bx - 18, by - 28, RGB(220, 180, 50), 1); // Outer seam
    drawLine(hdc, bx + 20, by - 68, bx + 20, by - 28, RGB(220, 180, 50), 1);

    // ── 4. Leather Tool Belt, Brass Buckle & Side Hatchet Holster ──
    fillSolidRect(hdc, bx - 21, by - 75, 44, 8, RGB(60, 35, 15)); // Thick saddle leather
    drawLine(hdc, bx - 21, by - 75, bx + 23, by - 75, RGB(180, 130, 60), 1); // Edge crease
    drawLine(hdc, bx - 21, by - 68, bx + 23, by - 68, RGB(180, 130, 60), 1);

    // Polished Brass Belt Buckle
    drawRoundedBox(hdc, bx - 7, by - 77, 14, 12, 2, RGB(255, 215, 0), RGB(180, 140, 0), 2);
    fillSolidRect(hdc, bx - 2, by - 75, 4, 8, RGB(35, 20, 10)); // Buckle tongue pin

    // Side Hatchet Holster on left hip (Spare throwing axe sheathed)
    fillSolidRect(hdc, bx - 24, by - 73, 7, 18, RGB(45, 25, 12)); // Leather frog holster
    drawLine(hdc, bx - 26, by - 70, bx - 19, by - 48, RGB(139, 69, 19), 4); // Ash handle
    drawCircle(hdc, bx - 25, by - 70, 5, RGB(190, 195, 200), RGB(100, 100, 100), 1); // Forged blade

    // ── 5. Buffalo-Check Plaid Flannel Shirt & Heavy Suspenders ──
    // Dynamic lean when charging power
    float windupLean = (gState == STATE_CHARGE) ? (gPower / 100.0f) * 8.0f : 0.0f;
    int torsoX = bx - (int)windupLean;

    drawRoundedBox(hdc, torsoX - 22, by - 124, 44, 52, 6, RGB(200, 25, 25), RGB(130, 15, 15), 1);

    // Buffalo plaid pattern: woven horizontal & vertical black check blocks
    for (int py = by - 120; py < by - 74; py += 10) {
        drawLine(hdc, torsoX - 21, py, torsoX + 21, py, RGB(25, 18, 18), 3); // Black horizontal bands
        drawLine(hdc, torsoX - 21, py + 5, torsoX + 21, py + 5, RGB(140, 15, 15), 1); // Shadow lines
    }
    for (int px = torsoX - 16; px < torsoX + 20; px += 10) {
        drawLine(hdc, px, by - 123, px, by - 74, RGB(25, 18, 18), 3); // Black vertical bands
    }

    // Shirt front placket & shiny brass buttons
    drawLine(hdc, torsoX, by - 122, torsoX, by - 75, RGB(140, 15, 15), 3);
    drawCircle(hdc, torsoX, by - 114, 2, RGB(255, 215, 0), RGB(60, 40, 0), 1);
    drawCircle(hdc, torsoX, by - 102, 2, RGB(255, 215, 0), RGB(60, 40, 0), 1);
    drawCircle(hdc, torsoX, by - 90,  2, RGB(255, 215, 0), RGB(60, 40, 0), 1);

    // Sturdy Black Leather Suspenders over shoulders
    drawLine(hdc, torsoX - 13, by - 124, torsoX - 13, by - 75, RGB(35, 30, 30), 5);
    drawLine(hdc, torsoX + 13, by - 124, torsoX + 13, by - 75, RGB(35, 30, 30), 5);
    // Suspender brass attachment clips at waistband
    drawRoundedBox(hdc, torsoX - 15, by - 77, 5, 6, 1, RGB(230, 185, 40), RGB(40, 30, 0), 1);
    drawRoundedBox(hdc, torsoX + 11, by - 77, 5, 6, 1, RGB(230, 185, 40), RGB(40, 30, 0), 1);

    // ── 6. Head, Facial Features, Rugged Beard & Winter Cap ──
    int headX = torsoX + 2;

    // Muscular neck & pointed shirt collar flaps
    fillSolidRect(hdc, headX - 8, by - 130, 16, 9, RGB(235, 185, 145)); // Neck
    POINT colL[3] = { { headX - 12, by - 125 }, { headX - 2, by - 121 }, { headX - 10, by - 118 } };
    POINT colR[3] = { { headX + 12, by - 125 }, { headX + 2, by - 121 }, { headX + 10, by - 118 } };
    HBRUSH brCol = CreateSolidBrush(RGB(155, 20, 20));
    SelectObject(hdc, brCol);
    Polygon(hdc, colL, 3);
    Polygon(hdc, colR, 3);
    DeleteObject(brCol);

    // Head base with ear
    drawCircle(hdc, headX, by - 138, 16, RGB(242, 195, 155), RGB(180, 125, 85), 1);
    drawCircle(hdc, headX - 16, by - 138, 4, RGB(235, 185, 145), RGB(170, 115, 75), 1); // Ear with inner fold
    drawCircle(hdc, headX - 16, by - 138, 2, RGB(200, 145, 105), RGB(170, 115, 75), 0);

    // Focused, Intense Eyes locked on target
    // Left eye
    fillSolidRect(hdc, headX - 6, by - 143, 5, 4, RGB(255, 255, 255));
    fillSolidRect(hdc, headX - 3, by - 143, 3, 4, RGB(45, 30, 20)); // Dark brown iris looking downrange
    fillSolidRect(hdc, headX - 2, by - 143, 1, 2, RGB(255, 255, 255)); // Catchlight glint
    // Right eye
    fillSolidRect(hdc, headX + 4, by - 143, 5, 4, RGB(255, 255, 255));
    fillSolidRect(hdc, headX + 7, by - 143, 3, 4, RGB(45, 30, 20)); // Looking downrange
    fillSolidRect(hdc, headX + 8, by - 143, 1, 2, RGB(255, 255, 255)); // Glint

    // Furrowed, bushy lumberjack eyebrows angled in concentration
    drawLine(hdc, headX - 9, by - 147, headX - 1, by - 144, RGB(95, 48, 18), 3);
    drawLine(hdc, headX + 2, by - 144, headX + 10, by - 147, RGB(95, 48, 18), 3);

    // Weathered Chiseled Nose
    drawLine(hdc, headX, by - 143, headX + 3, by - 135, RGB(205, 145, 105), 2);
    drawLine(hdc, headX + 3, by - 135, headX - 1, by - 135, RGB(180, 120, 80), 2);

    // Bushy Multi-Layered Auburn Beard & Mustache
    drawRoundedBox(hdc, headX - 15, by - 136, 30, 24, 8, RGB(120, 58, 22), RGB(80, 35, 12), 1); // Main beard
    // Beard hair strands & chiseled chin point
    drawLine(hdc, headX - 8, by - 128, headX - 5, by - 114, RGB(155, 80, 32), 2);
    drawLine(hdc, headX - 2, by - 128, headX - 2, by - 112, RGB(160, 85, 35), 2);
    drawLine(hdc, headX + 4, by - 128, headX + 3, by - 113, RGB(155, 80, 32), 2);
    drawLine(hdc, headX + 9, by - 128, headX + 7, by - 115, RGB(140, 70, 28), 2);
    // Distinctive Handlebar Mustache curling over beard
    drawRoundedBox(hdc, headX - 11, by - 139, 22, 7, 3, RGB(95, 45, 15), RGB(65, 28, 10), 1);
    drawLine(hdc, headX - 11, by - 136, headX - 14, by - 138, RGB(95, 45, 15), 2); // Mustache left tip
    drawLine(hdc, headX + 11, by - 136, headX + 14, by - 138, RGB(95, 45, 15), 2); // Mustache right tip

    // Classic Lumberjack Red Winter Beanie (Toque)
    drawCircle(hdc, headX, by - 150, 16, RGB(195, 25, 25), RGB(130, 15, 15), 1); // Wool crown
    // Folded ribbed brim of cap
    drawRoundedBox(hdc, headX - 17, by - 151, 34, 10, 3, RGB(220, 35, 35), RGB(145, 18, 18), 1);
    for (int rx = headX - 14; rx < headX + 15; rx += 4) {
        drawLine(hdc, rx, by - 151, rx, by - 142, RGB(160, 20, 20), 1); // Ribbed knit lines
    }
    // Warm white yarn pom-pom on top
    drawCircle(hdc, headX, by - 165, 5, RGB(245, 245, 245), RGB(180, 180, 180), 1);

    // Cold breath vapor wisp puffing into the night air
    float breathT = fmodf(gTgtTime * 1.6f, 3.0f);
    if (breathT < 1.4f) {
        float bFrac = breathT / 1.4f;
        int pfx = headX + 16 + (int)(bFrac * 26.0f);
        int pfy = by - 132 - (int)(bFrac * 12.0f);
        int pfr = 3 + (int)(bFrac * 7.0f);
        drawCircle(hdc, pfx, pfy, pfr, RGB(215, 230, 245), RGB(180, 205, 230), 0);
    }

    // ── 7. Arms, Gloves & Handheld Throwing Axe ──
    if (!followThrough) {
        // ── LEFT ARM: Sighting / Pointing at target downrange ──
        // Shoulder to elbow
        drawLine(hdc, torsoX + 13, by - 116, torsoX + 32, by - 108, RGB(200, 25, 25), 8);
        // Rolled flannel sleeve cuff
        drawCircle(hdc, torsoX + 32, by - 108, 6, RGB(25, 18, 18), RGB(200, 25, 25), 1);
        // Muscular forearm extended
        drawLine(hdc, torsoX + 32, by - 108, torsoX + 54, by - 105, RGB(238, 190, 150), 7);
        // Fingerless leather shooting glove
        drawRoundedBox(hdc, torsoX + 52, by - 109, 14, 8, 2, RGB(70, 42, 20), RGB(40, 22, 10), 1);
        // Index finger sighting along the target line!
        drawLine(hdc, torsoX + 64, by - 105, torsoX + 74, by - 105, RGB(238, 190, 150), 3);

        // ── RIGHT ARM: Cocked back in powerful windup ──
        float extraWindup = (gState == STATE_CHARGE) ? (gPower / 100.0f) * 16.0f : 0.0f;
        int rShX = torsoX - 13;
        int rShY = by - 116;
        int rElbX = torsoX - 28 - (int)extraWindup;
        int rElbY = by - 106 + (int)(extraWindup * 0.3f);
        int rHandX = torsoX - 18 - (int)(extraWindup * 1.3f);
        int rHandY = by - 136 - (int)(extraWindup * 0.5f);

        // Shoulder to elbow
        drawLine(hdc, rShX, rShY, rElbX, rElbY, RGB(200, 25, 25), 9);
        // Rolled flannel cuff
        drawCircle(hdc, rElbX, rElbY, 6, RGB(25, 18, 18), RGB(200, 25, 25), 1);
        // Forearm cocked up & back
        drawLine(hdc, rElbX, rElbY, rHandX, rHandY, RGB(238, 190, 150), 7);
        // Leather glove gripping axe handle
        drawCircle(hdc, rHandX, rHandY, 7, RGB(70, 42, 20), RGB(40, 22, 10), 1);

        // ── IN-HAND THROWING AXE (Ashwood shaft & double-bitted steel head) ──
        int axH1_x = rHandX - 10;
        int axH1_y = rHandY + 24;
        int axH2_x = rHandX + 18;
        int axH2_y = rHandY - 34;

        // Ash handle with dark grip swell
        drawLine(hdc, axH1_x, axH1_y, axH2_x, axH2_y, RGB(139, 69, 19), 5);
        drawLine(hdc, axH1_x - 2, axH1_y + 2, axH1_x + 4, axH1_y - 8, RGB(45, 22, 10), 5); // Grip swell

        // Double-bitted forged steel head
        int headX2 = axH2_x;
        int headY2 = axH2_y;
        drawLine(hdc, headX2 - 14, headY2 - 8, headX2 + 14, headY2 + 8, RGB(220, 225, 230), 8);
        // Razor-sharp blade cutting bevels
        drawCircle(hdc, headX2 - 14, headY2 - 8, 4, RGB(255, 255, 255), RGB(180, 185, 190), 1);
        drawCircle(hdc, headX2 + 14, headY2 + 8, 4, RGB(255, 255, 255), RGB(180, 185, 190), 1);

    } else {
        // ── FOLLOW-THROUGH POSE (Full explosive release!) ──
        // Left arm swung back for aerodynamic counter-balance
        drawLine(hdc, torsoX - 12, by - 114, torsoX - 34, by - 98, RGB(200, 25, 25), 7);
        drawLine(hdc, torsoX - 34, by - 98, torsoX - 50, by - 86, RGB(238, 190, 150), 6);
        drawCircle(hdc, torsoX - 50, by - 86, 6, RGB(70, 42, 20), RGB(40, 22, 10), 1);

        // Right arm fully whipped forward toward the target!
        drawLine(hdc, torsoX + 13, by - 116, torsoX + 46, by - 108, RGB(200, 25, 25), 9);
        // Rolled cuff
        drawCircle(hdc, torsoX + 46, by - 108, 6, RGB(25, 18, 18), RGB(200, 25, 25), 1);
        // Forearm extended whip-cracking
        drawLine(hdc, torsoX + 46, by - 108, torsoX + 75, by - 100, RGB(238, 190, 150), 7);
        // Open throwing glove right after releasing axe
        drawRoundedBox(hdc, torsoX + 73, by - 104, 12, 8, 2, RGB(70, 42, 20), RGB(40, 22, 10), 1);
        drawLine(hdc, torsoX + 83, by - 100, torsoX + 90, by - 100, RGB(238, 190, 150), 3); // Extended fingers
    }
}

// 4. Rotating Double-Bitted Axe in Flight
static void renderAxe(HDC hdc) {
    if (!gAxeActive) return;

    // Flight trail
    for (size_t i = 0; i < gTrail.size(); ++i) {
        float alpha = gTrail[i].life / 0.4f;
        int sz = (int)(alpha * 5.0f) + 1;
        drawCircle(hdc, (int)gTrail[i].x, (int)gTrail[i].y, sz, RGB(255, 215, 0), RGB(255, 255, 255), 0);
    }

    int ax = (int)gAxeP.x;
    int ay = (int)gAxeP.y;

    float cosA = cosf(gAxeRot);
    float sinA = sinf(gAxeRot);

    // Wooden Handle (length 38px)
    int hx1 = ax - (int)(cosA * 19.0f);
    int hy1 = ay - (int)(sinA * 19.0f);
    int hx2 = ax + (int)(cosA * 19.0f);
    int hy2 = ay + (int)(sinA * 19.0f);
    drawLine(hdc, hx1, hy1, hx2, hy2, RGB(139, 69, 19), 5);

    // Double-Bitted Steel Blades at the head
    float perpCos = -sinA;
    float perpSin = cosA;

    int bx1 = hx2 + (int)(perpCos * 14.0f);
    int by1 = hy2 + (int)(perpSin * 14.0f);
    int bx2 = hx2 - (int)(perpCos * 14.0f);
    int by2 = hy2 - (int)(perpSin * 14.0f);

    drawLine(hdc, bx1, by1, bx2, by2, RGB(220, 225, 230), 6);
    drawCircle(hdc, bx1, by1, 4, RGB(255, 255, 255), RGB(180, 185, 190), 1);
    drawCircle(hdc, bx2, by2, 4, RGB(255, 255, 255), RGB(180, 185, 190), 1);
}

// 5. Full Trajectory Arc with Live Target-Lock Intercept Crosshair
static void renderTrajectory(HDC hdc) {
    float rad = gAngle * PI_F / 180.0f;
    float simVX = cosf(rad) * V_REF;
    float simVY = sinf(rad) * V_REF;
    float simX  = 170.0f;
    float simY  = 395.0f;

    bool  lockedOn = false;
    float lockX = 0, lockY = 0;

    std::vector<POINT> arcPoints;
    arcPoints.push_back({ (int)simX, (int)simY });

    for (int step = 0; step < 115; ++step) {
        simX  += simVX * 0.025f;
        simY  += simVY * 0.025f;
        simVY += GRAV * 0.025f;
        simVX += gWind * 6.0f * 0.025f;

        if (simX > WIN_W || simX < 0) break;
        if (simY >= GROUND_Y) {
            arcPoints.push_back({ (int)simX, (int)GROUND_Y });
            break;
        }

        arcPoints.push_back({ (int)simX, (int)simY });

        // Check if trajectory point intersects the moving target
        float dx = simX - gTgtX;
        float dy = simY - gTgtY;
        if (sqrtf(dx * dx + dy * dy) <= TGT_RADIUS && !lockedOn) {
            lockedOn = true;
            lockX = simX;
            lockY = simY;
        }
    }

    // Draw the continuous trajectory arc - completely fixed and independent of space/power!
    COLORREF arcCol = lockedOn ? RGB(50, 255, 120) : RGB(255, 215, 80);
    HPEN pen = CreatePen(PS_DOT, 2, arcCol);
    HPEN oldPen = (HPEN)SelectObject(hdc, pen);
    for (size_t i = 1; i < arcPoints.size(); ++i) {
        MoveToEx(hdc, arcPoints[i - 1].x, arcPoints[i - 1].y, NULL);
        LineTo(hdc, arcPoints[i].x, arcPoints[i].y);
    }
    SelectObject(hdc, oldPen);
    DeleteObject(pen);

    // Draw landing marker or Lock-On reticle
    if (lockedOn) {
        int lx = (int)lockX, ly = (int)lockY;
        drawCircle(hdc, lx, ly, 12, RGB(0, 0, 0), RGB(50, 255, 120), 3);
        drawLine(hdc, lx - 18, ly, lx + 18, ly, RGB(50, 255, 120), 2);
        drawLine(hdc, lx, ly - 18, lx, ly + 18, RGB(50, 255, 120), 2);
        drawRoundedBox(hdc, lx - 60, ly - 34, 120, 20, 4, RGB(20, 60, 30), RGB(50, 255, 120), 1);
        drawCenteredText(hdc, "TARGET LOCKED!", lx, ly - 32, hFontSmall, RGB(50, 255, 120));
    } else if (!arcPoints.empty()) {
        POINT last = arcPoints.back();
        if (last.y >= GROUND_Y) {
            drawCircle(hdc, last.x, last.y, 6, RGB(255, 50, 50), RGB(255, 255, 255), 2);
        }
    }
}

// 6. Modern, Sleek Dashboard UI
static void renderHUD(HDC hdc) {
    // ── TOP DASHBOARD BAR ──
    drawRoundedBox(hdc, 15, 10, WIN_W - 30, 48, 8, RGB(18, 22, 32), RGB(255, 215, 0), 2);

    // Score
    char scTxt[32];
    sprintf(scTxt, "★ SCORE: %d", gScore);
    drawTextAt(hdc, scTxt, 35, 22, hFontLarge, RGB(255, 215, 0));

    // Streak
    if (gStreak > 1) {
        char stTxt[32];
        sprintf(stTxt, "🔥 STREAK: x%d (+%d)", gStreak, (gStreak - 1) * 25);
        drawTextAt(hdc, stTxt, 240, 24, hFontBold, RGB(50, 255, 120));
    }

    // Wind Meter
    char wTxt[48];
    if (fabsf(gWind) < 0.8f) sprintf(wTxt, "💨 WIND: Calm");
    else if (gWind > 0)     sprintf(wTxt, "💨 WIND: +%.1f m/s >>", gWind);
    else                    sprintf(wTxt, "💨 WIND: %.1f m/s <<", gWind);
    drawTextAt(hdc, wTxt, 440, 24, hFontBold, RGB(100, 220, 255));

    // Audio status
    drawTextAt(hdc, gSound ? "🔊 SFX: ON [M]" : "🔇 MUTED [M]", 670, 26, hFontNorm, gSound ? RGB(180, 220, 180) : RGB(140, 140, 140));

    // Round
    char rdTxt[32];
    sprintf(rdTxt, "ROUND %d / %d", gRound + 1, ROUNDS);
    drawTextAt(hdc, rdTxt, WIN_W - 170, 22, hFontLarge, RGB(255, 255, 255));

    // ── BOTTOM CONTROL DECK ──
    drawRoundedBox(hdc, 20, 520, WIN_W - 40, 85, 10, RGB(16, 20, 28), RGB(70, 80, 105), 1);

    // 1. Angle Readout (Left Column)
    char angTxt[32];
    sprintf(angTxt, "ANGLE: %.0f°", -gAngle);
    drawTextAt(hdc, angTxt, 38, 533, hFontBold, RGB(100, 220, 255));
    drawTextAt(hdc, "[↑/↓] Pitch Aim", 38, 556, hFontSmall, RGB(160, 175, 195));
    drawTextAt(hdc, "Trajectory: Live", 38, 576, hFontSmall, RGB(120, 140, 165));

    // 2. Interactive Speed & Flight-Time Deck (Middle Column)
    float curPow = (gState == STATE_CHARGE) ? gPower : gAimPower;
    float curSpd = curPow * 7.5f + 220.0f;
    float estFlightTime = calcFlightTime(curPow);

    // Header readout: Power %, Axe Speed & Flight Time to Target
    char powTxt[80];
    if (gState == STATE_CHARGE) {
        sprintf(powTxt, "⚡ CHARGING SPEED: %.0f px/s  |  FLIGHT TIME: %.2fs ⚡", curSpd, estFlightTime);
        drawTextAt(hdc, powTxt, 165, 527, hFontBold, RGB(255, 215, 0));
    } else if (gState == STATE_FLY) {
        sprintf(powTxt, "🚀 IN FLIGHT: %.0f px/s (%.1f m/s)  |  ELAPSED: %.2fs", gCalibSpeed, gCalibSpeed * 0.05f, gFlightTime);
        drawTextAt(hdc, powTxt, 165, 527, hFontBold, RGB(100, 220, 255));
    } else {
        sprintf(powTxt, "SPEED: %.0f px/s (%.0f%%)  |  FLIGHT TIME TO TARGET: %.2fs", curSpd, curPow, estFlightTime);
        drawTextAt(hdc, powTxt, 165, 527, hFontBold, RGB(255, 215, 0));
    }

    // Gauge frame (w = 380, h = 20)
    int gX = 165, gY = 549, gW = 380, gH = 20;
    drawRoundedBox(hdc, gX, gY, gW, gH, 4, RGB(22, 26, 36), RGB(70, 85, 115), 1);

    // Active inner track bounds
    int trackX = gX + 3;
    int trackW = gW - 6;

    // Fill bar up to curPow
    float normCur = (curPow - 15.0f) / 85.0f;
    if (normCur < 0.0f) normCur = 0.0f;
    if (normCur > 1.0f) normCur = 1.0f;
    int fillW = (int)(normCur * (float)trackW);

    COLORREF barCol = (curPow < 45.0f) ? RGB(45, 160, 220) :
                      (curPow < 75.0f) ? RGB(50, 215, 90)  :
                      (curPow < 90.0f) ? RGB(255, 205, 40) : RGB(255, 65, 55);
    if (fillW > 0) fillSolidRect(hdc, trackX, gY + 2, fillW, gH - 4, barCol);

    // Target marker tick at dialed power
    float normTgt = (gAimPower - 15.0f) / 85.0f;
    int tgtX = trackX + (int)(normTgt * (float)trackW);
    drawLine(hdc, tgtX, gY - 3, tgtX, gY + gH + 3, RGB(100, 220, 255), 1);

    // Calibration Needle
    int nX = trackX + fillW;
    COLORREF nCol = (gState == STATE_CHARGE) ? RGB(255, 235, 80) : RGB(255, 255, 255);

    drawLine(hdc, nX - 1, gY - 3, nX - 1, gY + gH + 3, RGB(20, 20, 20), 1);
    drawLine(hdc, nX,     gY - 3, nX,     gY + gH + 3, nCol, 3);
    drawLine(hdc, nX,     gY - 2, nX,     gY + gH + 2, RGB(255, 255, 255), 1);
    drawLine(hdc, nX + 1, gY - 3, nX + 1, gY + gH + 3, RGB(20, 20, 20), 1);

    // Triangle pointers at needle tips
    POINT triTop[3] = { { nX - 4, gY - 5 }, { nX + 4, gY - 5 }, { nX, gY } };
    POINT triBot[3] = { { nX - 4, gY + gH + 5 }, { nX + 4, gY + gH + 5 }, { nX, gY + gH } };
    HBRUSH brN = CreateSolidBrush(nCol);
    HBRUSH oldBrN = (HBRUSH)SelectObject(hdc, brN);
    Polygon(hdc, triTop, 3);
    Polygon(hdc, triBot, 3);
    SelectObject(hdc, oldBrN);
    DeleteObject(brN);

    // Gauge bottom instructions / live advice
    if (gState == STATE_CHARGE) {
        drawTextAt(hdc, ">>> RELEASE [SPACE] TO THROW! (TIME REDUCES AS YOU CHARGE) <<<", 165, 578, hFontSmall, RGB(255, 215, 0));
    } else if (gState == STATE_FLY) {
        drawTextAt(hdc, "Axe in flight! Fixed trajectory path at calibrated speed.", 165, 578, hFontSmall, RGB(100, 220, 255));
    } else {
        drawTextAt(hdc, "[SPACE Hold & Rel] Charge Speed to Reduce Time  |  [←/→] Dial Speed", 165, 578, hFontSmall, RGB(160, 185, 210));
    }

    // 3. Target Telemetry & Telemetry Deck (Right Column)
    char telTxt[64];
    sprintf(telTxt, "TARGET: %s  |  RANGE: %.0fm  |  SPEED: %.0f px/s", gPatName, (gTgtX - 110.0f) * 0.05f, fabsf(gTgtVX) + fabsf(gTgtVY));
    drawTextAt(hdc, telTxt, 570, 527, hFontBold, RGB(255, 160, 255));

    drawTextAt(hdc, "[AIM ANGLE FOR PATH  •  HOLD SPACE TO REDUCE TIME]", 570, 551, hFontNorm, RGB(175, 195, 220));

    drawTextAt(hdc, "[SPACE] Charge & Reduce Time  |  [ENTER] Quick Throw  |  [M] SFX  |  [ESC] Exit", 570, 578, hFontSmall, RGB(255, 215, 0));
}

// 7. Overlays: Title, Result, Game Over
static void renderTitle(HDC hdc) {
    fillSolidRect(hdc, 0, 0, WIN_W, WIN_H, RGB(10, 14, 24));

    drawRoundedBox(hdc, 160, 60, WIN_W - 320, 500, 16, RGB(18, 24, 38), RGB(255, 215, 0), 3);

    drawCenteredText(hdc, "L U M B E R J A C K   F U R Y", WIN_W / 2, 95, hFontTitle, RGB(255, 215, 0));
    drawCenteredText(hdc, "CHAMPIONSHIP AXE THROWING", WIN_W / 2, 145, hFontLarge, RGB(255, 80, 80));

    // Target preview graphic in menu
    drawCircle(hdc, WIN_W / 2, 230, 45, RGB(30, 144, 255), RGB(20, 80, 180), 2);
    drawCircle(hdc, WIN_W / 2, 230, 32, RGB(250, 250, 250), RGB(180, 180, 180), 2);
    drawCircle(hdc, WIN_W / 2, 230, 20, RGB(220, 20, 60), RGB(140, 10, 30), 2);
    drawCircle(hdc, WIN_W / 2, 230, 10, RGB(255, 215, 0), RGB(200, 140, 0), 2);

    drawCenteredText(hdc, "TARGET RULES & SCORING", WIN_W / 2, 290, hFontBold, RGB(100, 220, 255));
    drawCenteredText(hdc, "Gold Bullseye: 100 pts  |  Red Ring: 75 pts  |  White: 50 pts  |  Blue: 25 pts", WIN_W / 2, 320, hFontNorm, RGB(230, 235, 245));
    drawCenteredText(hdc, "Target MOVES on an overhead rail! Lead your throws ahead of it!", WIN_W / 2, 350, hFontBold, RGB(255, 215, 0));

    drawCenteredText(hdc, "CONTROLS & FLIGHT TIME CALIBRATION:", WIN_W / 2, 395, hFontBold, RGB(100, 220, 255));
    drawCenteredText(hdc, "[UP / DOWN] Set Trajectory Path  |  [LEFT / RIGHT] Dial Throw Speed", WIN_W / 2, 420, hFontNorm, RGB(230, 235, 245));
    drawCenteredText(hdc, "[SPACE Hold & Rel] Charge Speed to Reduce Flight Time!  |  [ENTER] Quick Throw", WIN_W / 2, 445, hFontNorm, RGB(230, 235, 245));

    if ((clock() / 450) % 2 == 0) {
        drawCenteredText(hdc, ">>> PRESS [ENTER] OR [SPACE] TO START <<<", WIN_W / 2, 495, hFontLarge, RGB(255, 215, 0));
    }
}

static void renderResult(HDC hdc) {
    drawRoundedBox(hdc, WIN_W / 2 - 250, 160, 500, 195, 12, RGB(16, 20, 30), RGB(255, 215, 0), 2);
    drawCenteredText(hdc, gResultMsg, WIN_W / 2, 185, hFontLarge, RGB(255, 215, 0));

    // Display calibrated throw speed and actual flight time
    if (gCalibSpeed > 0.0f) {
        char calTxt[80];
        sprintf(calTxt, "Axe Throw Speed: %.0f px/s (%.1f m/s)  |  Flight Time: %.2fs", gCalibSpeed, gCalibSpeed * 0.05f, gFlightTime);
        drawCenteredText(hdc, calTxt, WIN_W / 2, 225, hFontBold, RGB(100, 220, 255));
    }

    if (gStreak > 1) {
        char strk[48];
        sprintf(strk, "Consecutive Streak: x%d (+%d BONUS PTS)", gStreak, (gStreak - 1) * 25);
        drawCenteredText(hdc, strk, WIN_W / 2, 260, hFontBold, RGB(50, 255, 120));
    }

    drawCenteredText(hdc, "Press [ENTER] or [SPACE] for next throw", WIN_W / 2, 305, hFontNorm, RGB(220, 230, 245));
}

static void renderGameOver(HDC hdc) {
    drawRoundedBox(hdc, WIN_W / 2 - 280, 120, 560, 380, 16, RGB(16, 22, 34), RGB(255, 215, 0), 3);

    drawCenteredText(hdc, "CHAMPIONSHIP COMPLETE!", WIN_W / 2, 145, hFontLarge, RGB(255, 215, 0));

    char sc[48];
    sprintf(sc, "FINAL SCORE: %d PTS", gScore);
    drawCenteredText(hdc, sc, WIN_W / 2, 200, hFontTitle, RGB(255, 255, 255));

    char st[48];
    sprintf(st, "BEST STREAK: %d in a row", gMaxStreak);
    drawCenteredText(hdc, st, WIN_W / 2, 260, hFontBold, RGB(50, 255, 120));

    const char* rank;
    COLORREF rc;
    if      (gScore >= 500) { rank = "LEGENDARY AXE GOD!";       rc = RGB(255, 215, 0); }
    else if (gScore >= 380) { rank = "MASTER LUMBERJACK!";       rc = RGB(50, 255, 120); }
    else if (gScore >= 260) { rank = "EXPERT MARKSMAN";          rc = RGB(100, 220, 255); }
    else if (gScore >= 150) { rank = "SKILLED THROWER";          rc = RGB(230, 235, 245); }
    else                    { rank = "TIMBER ROOKIE";            rc = RGB(200, 150, 100); }

    std::string rankStr = "RANKING: " + std::string(rank);
    drawCenteredText(hdc, rankStr, WIN_W / 2, 305, hFontLarge, rc);

    char avg[48];
    sprintf(avg, "Average: %.1f pts / throw", (float)gScore / (float)ROUNDS);
    drawCenteredText(hdc, avg, WIN_W / 2, 355, hFontNorm, RGB(180, 195, 215));

    drawCenteredText(hdc, "Press [ENTER] to play again  |  [ESC] to quit", WIN_W / 2, 420, hFontBold, RGB(255, 215, 0));
}

// ================================================================
//  Frame Loop
// ================================================================
static void updateAndRender() {
    // ── State Updates ──
    switch (gState) {
    case STATE_TITLE:
        break;

    case STATE_AIM:
        updateTarget();
        break;

    case STATE_CHARGE:
        updateTarget();
        // Holding SPACE charges power & speed, directly reducing flight time!
        gPower = (std::min)(gPower + 85.0f * DT, 100.0f);
        break;

    case STATE_FLY:
        updateTarget();
        updateAxe();
        break;

    case STATE_RESULT:
        gTimer += DT;
        updateParticles();
        break;

    case STATE_GAMEOVER:
        gTimer += DT;
        break;
    }

    updateLeaves();
    updateParticles();
    if (gCalibFlash > 0.0f) gCalibFlash -= DT;

    // ── Render into Memory DC (Double Buffer) ──
    if (gState == STATE_TITLE) {
        renderTitle(gMemDC);
    } else {
        renderEnvironment(gMemDC);
        renderTargetSystem(gMemDC);
        renderLumberjack(gMemDC, gState == STATE_FLY || gState == STATE_RESULT || gState == STATE_GAMEOVER);

        if (gState == STATE_AIM || gState == STATE_CHARGE) {
            renderTrajectory(gMemDC);
        }

        renderAxe(gMemDC);

        // Particle sparks
        for (auto& p : gParticles) {
            drawCircle(gMemDC, (int)p.p.x, (int)p.p.y, p.size, p.col, p.col, 0);
        }

        renderHUD(gMemDC);

        if (gState == STATE_RESULT)   renderResult(gMemDC);
        if (gState == STATE_GAMEOVER) renderGameOver(gMemDC);
    }

    // ── Blit to screen ──
    HDC hdc = GetDC(ghWnd);
    BitBlt(hdc, 0, 0, WIN_W, WIN_H, gMemDC, 0, 0, SRCCOPY);
    ReleaseDC(ghWnd, hdc);
}

// ================================================================
//  Windows Window Procedure
// ================================================================
static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_CREATE: {
        HDC hdc = GetDC(hwnd);
        gMemDC  = CreateCompatibleDC(hdc);
        gMemBM  = CreateCompatibleBitmap(hdc, WIN_W, WIN_H);
        gOldBM  = (HBITMAP)SelectObject(gMemDC, gMemBM);
        ReleaseDC(hwnd, hdc);

        // Load fonts
        hFontTitle = CreateFontA(36, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE, ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH, "Segoe UI");
        hFontLarge = CreateFontA(24, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE, ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH, "Segoe UI");
        hFontBold  = CreateFontA(18, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE, ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH, "Segoe UI");
        hFontNorm  = CreateFontA(16, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH, "Segoe UI");
        hFontSmall = CreateFontA(13, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE, ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH, "Segoe UI");

        initLeaves();
        SetTimer(hwnd, 1, 16, NULL); // ~60 FPS
        return 0;
    }

    case WM_TIMER:
        updateAndRender();
        return 0;

    case WM_KEYDOWN: {
        if (wParam == VK_ESCAPE) {
            PostQuitMessage(0);
            return 0;
        }

        if (wParam == 'M') {
            gSound = !gSound;
            return 0;
        }

        if (gState == STATE_TITLE) {
            if (wParam == VK_RETURN || wParam == VK_SPACE) {
                gScore       = 0;
                gRound       = 0;
                gStreak      = 0;
                gMaxStreak   = 0;
                gCalibBonus  = 0;
                gCalibRating = CALIB_NONE;
                gCalibMsg.clear();
                gStuckAxes.clear();
                gParticles.clear();
                newRound();
            }
            return 0;
        }

        if (gState == STATE_AIM) {
            if (wParam == VK_UP)    gAngle    = (std::max)(gAngle - 1.5f, -60.0f);
            if (wParam == VK_DOWN)  gAngle    = (std::min)(gAngle + 1.5f,  10.0f);
            if (wParam == VK_LEFT)  gAimPower = (std::max)(gAimPower - 3.0f, 15.0f);
            if (wParam == VK_RIGHT) gAimPower = (std::min)(gAimPower + 3.0f, 100.0f);

            if (wParam == VK_SPACE) {
                // Hold SPACE to charge speed and reduce flight time!
                gPower = gAimPower;
                gState = STATE_CHARGE;
                playSound(500, 30);
            } else if (wParam == VK_RETURN) {
                startThrow(gAimPower);
            }
            return 0;
        }

        if (gState == STATE_CHARGE) {
            if (wParam == VK_BACK || wParam == VK_ESCAPE) {
                gState = STATE_AIM;
                gPower = gAimPower;
            }
            return 0;
        }

        if (gState == STATE_RESULT) {
            if ((wParam == VK_RETURN || wParam == VK_SPACE) && gTimer > 0.3f) {
                ++gRound;
                if (gRound >= ROUNDS) {
                    gState = STATE_GAMEOVER;
                    gTimer = 0.0f;
                } else {
                    newRound();
                }
            }
            return 0;
        }

        if (gState == STATE_GAMEOVER) {
            if (wParam == VK_RETURN || wParam == VK_SPACE) {
                gState = STATE_TITLE;
            }
            return 0;
        }
        return 0;
    }

    case WM_KEYUP: {
        if (gState == STATE_CHARGE && wParam == VK_SPACE) {
            gAimPower = gPower;
            startThrow(gPower);
        }
        return 0;
    }

    case WM_DESTROY:
        KillTimer(hwnd, 1);
        if (gMemDC && gOldBM) SelectObject(gMemDC, gOldBM);
        if (gMemBM) DeleteObject(gMemBM);
        if (gMemDC) DeleteDC(gMemDC);
        if (hFontTitle) DeleteObject(hFontTitle);
        if (hFontLarge) DeleteObject(hFontLarge);
        if (hFontBold)  DeleteObject(hFontBold);
        if (hFontNorm)  DeleteObject(hFontNorm);
        if (hFontSmall) DeleteObject(hFontSmall);
        PostQuitMessage(0);
        return 0;
    }

    return DefWindowProc(hwnd, msg, wParam, lParam);
}

// ================================================================
//  Main Entry Point
// ================================================================
int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int nCmdShow) {
    srand((unsigned)time(NULL));

    WNDCLASSA wc = {};
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = hInstance;
    wc.lpszClassName = "LumberjackFuryWin";
    wc.hCursor       = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)GetStockObject(BLACK_BRUSH);
    RegisterClassA(&wc);

    // Calculate exact outer window size so client area is 1024x620
    RECT wr = { 0, 0, WIN_W, WIN_H };
    AdjustWindowRect(&wr, WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX, FALSE);
    int windowW = wr.right - wr.left;
    int windowH = wr.bottom - wr.top;

    int screenW = GetSystemMetrics(SM_CXSCREEN);
    int screenH = GetSystemMetrics(SM_CYSCREEN);
    int posX    = (screenW - windowW) / 2;
    int posY    = (screenH - windowH) / 2;

    ghWnd = CreateWindowExA(
        0,
        wc.lpszClassName,
        "LUMBERJACK FURY  -  Championship Axe Throwing",
        WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_VISIBLE,
        posX, posY, windowW, windowH,
        NULL, NULL, hInstance, NULL);

    ShowWindow(ghWnd, nCmdShow);
    UpdateWindow(ghWnd);

    MSG msg;
    while (GetMessage(&msg, NULL, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }

    return (int)msg.wParam;
}
