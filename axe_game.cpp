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

// Target dynamics
static float        gTgtX      = 760.0f;
static float        gTgtY      = 240.0f;
static float        gTgtVX     = 0.0f;
static float        gTgtVY     = 0.0f;
static float        gTgtSpd    = 90.0f;
static float        gTgtTime   = 0.0f;
static Pattern      gPattern   = PAT_VERTICAL;
static const char*  gPatName   = "";

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

    gAxeP    = V2(140.0f, 410.0f);
    gAxeV    = V2(cosf(rad) * spd, sinf(rad) * spd);
    gAxeRot  = 0.0f;
    gAxeSpin = 12.0f + pow * 0.12f;
    gAxeActive = true;
    gTrail.clear();
    gState   = STATE_FLY;

    playSound(600, 30);
}

static void updateAxe() {
    if (!gAxeActive) return;

    gAxeP.x += gAxeV.x * DT;
    gAxeP.y += gAxeV.y * DT;
    gAxeV.y += GRAV * DT;
    gAxeV.x += gWind * 6.0f * DT;
    gAxeRot += gAxeSpin * DT;

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
    gWind     = -8.0f + ((float)rand() / (float)RAND_MAX) * 16.0f; // -8 .. +8
    gAngle    = -22.0f;
    gPower    = 0.0f;
    gAxeActive= false;
    gResultMsg.clear();
    gLastScore= 0;
    gTrail.clear();

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

// 3. Lumberjack Character
static void renderLumberjack(HDC hdc, bool followThrough) {
    int bx = 110, by = GROUND_Y;

    // Boots
    fillSolidRect(hdc, bx - 14, by - 16, 12, 16, RGB(50, 30, 20));
    fillSolidRect(hdc, bx + 2,  by - 16, 12, 16, RGB(50, 30, 20));

    // Denim Trousers
    fillSolidRect(hdc, bx - 12, by - 60, 10, 46, RGB(40, 60, 100));
    fillSolidRect(hdc, bx + 2,  by - 60, 10, 46, RGB(40, 60, 100));

    // Torso (Red & Black Plaid Flannel Shirt)
    fillSolidRect(hdc, bx - 14, by - 110, 28, 52, RGB(180, 20, 20));
    drawLine(hdc, bx - 6, by - 110, bx - 6, by - 58, RGB(20, 20, 20), 2); // Plaid stripe
    drawLine(hdc, bx + 6, by - 110, bx + 6, by - 58, RGB(20, 20, 20), 2);

    // Head, Beard & Cap
    drawCircle(hdc, bx, by - 122, 14, RGB(240, 190, 150), RGB(0, 0, 0), 1); // Face
    fillSolidRect(hdc, bx - 8, by - 118, 16, 10, RGB(100, 50, 20));          // Beard
    drawCircle(hdc, bx, by - 130, 12, RGB(190, 20, 20), RGB(0, 0, 0), 1);   // Cap

    // Arms & Axe
    if (!followThrough) {
        // Cocked arm ready to throw
        drawLine(hdc, bx + 8, by - 100, bx + 28, by - 85, RGB(180, 20, 20), 6);
        drawLine(hdc, bx + 28, by - 85, bx + 34, by - 105, RGB(240, 190, 150), 5);
        // Axe in hand
        drawLine(hdc, bx + 30, by - 100, bx + 48, by - 124, RGB(139, 69, 19), 4);
        drawCircle(hdc, bx + 48, by - 124, 7, RGB(210, 215, 220), RGB(255, 255, 255), 2);
    } else {
        // Extended follow-through arm
        drawLine(hdc, bx + 8, by - 100, bx + 36, by - 95, RGB(180, 20, 20), 6);
        drawLine(hdc, bx + 36, by - 95, bx + 52, by - 95, RGB(240, 190, 150), 5);
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
    float pow = (gState == STATE_CHARGE) ? gPower : gAimPower;
    float spd = pow * 7.5f + 220.0f;

    float simVX = cosf(rad) * spd;
    float simVY = sinf(rad) * spd;
    float simX  = 140.0f;
    float simY  = 410.0f;

    bool  lockedOn = false;
    float lockX = 0, lockY = 0;

    std::vector<POINT> arcPoints;
    arcPoints.push_back({ (int)simX, (int)simY });

    for (int step = 0; step < 110; ++step) {
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

    // Draw the continuous trajectory arc
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

    // Angle Readout
    char angTxt[32];
    sprintf(angTxt, "ANGLE: %.0f°", -gAngle);
    drawTextAt(hdc, angTxt, 40, 535, hFontBold, RGB(100, 220, 255));
    drawTextAt(hdc, "[↑/↓] Adjust", 40, 560, hFontSmall, RGB(160, 175, 195));

    // Power Gauge Slider
    float curPow = (gState == STATE_CHARGE) ? gPower : gAimPower;
    char powTxt[32];
    sprintf(powTxt, "POWER: %.0f%%", curPow);
    drawTextAt(hdc, powTxt, 180, 535, hFontBold, (curPow >= 95.0f) ? RGB(255, 70, 70) : RGB(255, 215, 0));

    // Gauge bar
    drawRoundedBox(hdc, 180, 560, 240, 16, 4, RGB(30, 35, 45), RGB(90, 100, 120), 1);
    int fillW = (int)((curPow / 100.0f) * 236.0f);
    COLORREF barCol = (curPow < 50.0f) ? RGB(50, 200, 80) : (curPow < 80.0f) ? RGB(255, 215, 0) : RGB(255, 60, 60);
    if (fillW > 0) fillSolidRect(hdc, 182, 562, fillW, 12, barCol);
    drawTextAt(hdc, "[←/→] Dial  [SPACE] Charge", 180, 582, hFontSmall, RGB(160, 175, 195));

    // Target Telemetry Info
    char telTxt[64];
    sprintf(telTxt, "TARGET: %s", gPatName);
    drawTextAt(hdc, telTxt, 460, 535, hFontBold, RGB(255, 160, 255));
    char rngTxt[64];
    sprintf(rngTxt, "RANGE: %.0fm   SPEED: %.0f px/s", (gTgtX - 110.0f) * 0.05f, fabsf(gTgtVX) + fabsf(gTgtVY));
    drawTextAt(hdc, rngTxt, 460, 560, hFontNorm, RGB(200, 210, 225));

    // Controls Help Summary
    drawTextAt(hdc, "[SPACE / ENTER] Hurl Axe   |   [M] Toggle Audio   |   [ESC] Exit", 460, 582, hFontSmall, RGB(255, 215, 0));
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

    drawCenteredText(hdc, "CONTROLS:", WIN_W / 2, 395, hFontBold, RGB(100, 220, 255));
    drawCenteredText(hdc, "[UP / DOWN] Throw Angle  |  [LEFT / RIGHT] Throw Power (Live Arc!)", WIN_W / 2, 420, hFontNorm, RGB(230, 235, 245));
    drawCenteredText(hdc, "[SPACE Hold & Rel] Charge & Hurl  |  [ENTER] Quick Throw", WIN_W / 2, 445, hFontNorm, RGB(230, 235, 245));

    if ((clock() / 450) % 2 == 0) {
        drawCenteredText(hdc, ">>> PRESS [ENTER] OR [SPACE] TO START <<<", WIN_W / 2, 495, hFontLarge, RGB(255, 215, 0));
    }
}

static void renderResult(HDC hdc) {
    drawRoundedBox(hdc, WIN_W / 2 - 250, 180, 500, 160, 12, RGB(16, 20, 30), RGB(255, 215, 0), 2);
    drawCenteredText(hdc, gResultMsg, WIN_W / 2, 210, hFontLarge, RGB(255, 215, 0));

    if (gStreak > 1) {
        char strk[48];
        sprintf(strk, "Consecutive Streak: x%d (+%d BONUS PTS)", gStreak, (gStreak - 1) * 25);
        drawCenteredText(hdc, strk, WIN_W / 2, 255, hFontBold, RGB(50, 255, 120));
    }

    drawCenteredText(hdc, "Press [ENTER] or [SPACE] for next throw", WIN_W / 2, 295, hFontNorm, RGB(220, 230, 245));
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
        gPower = (std::min)(gPower + 105.0f * DT, 100.0f);
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
                gScore     = 0;
                gRound     = 0;
                gStreak    = 0;
                gMaxStreak = 0;
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
                gPower = gAimPower;
                gState = STATE_CHARGE;
            } else if (wParam == VK_RETURN) {
                startThrow(gAimPower);
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
