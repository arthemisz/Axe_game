# Axe Game (Lumberjack Fury)

A native Win32 2D graphical axe-throwing game written in C++ using the Windows GDI API.

## Features

- Double-buffered 60 FPS rendering in a 1024x620 native window.
- 5 escalating target patterns: Elevator, Rail Runner, Figure-8, Wind Gusts, and Chaos.
- Real-time trajectory arc, wind influence, and flight calibration scoring.
- Streak multipliers and audio feedback.

## Controls

- Up / Down: Adjust throw angle (-60 deg to +10 deg)
- Left / Right: Adjust aim power (15% to 100%)
- Space: Hold to charge throw power, release to throw
- Enter: Quick throw at dialed power / advance screen
- M: Toggle sound on or off
- Esc: Quit game

## Building and Running

### Prerequisites

- Windows OS
- MinGW / GCC (g++)

### Compilation

Compile with g++:

```bash
g++ -o axe_game.exe axe_game.cpp -O2 -mwindows -lgdi32 -luser32 -lkernel32
```

### Running

Launch the executable:

```bash
./axe_game.exe
```
