@echo off
setlocal

cd /d "%~dp0"

echo ==========================================
echo  Missile Chase - CS6501 Final Project
echo ==========================================
echo.

echo Generating frames.json from Lean...
lake env lean --run Project.lean

if errorlevel 1 (
    echo.
    echo Lean failed. Fix Project.lean before starting the game.
    pause
    exit /b 1
)

echo.
echo Starting local Python server...
start "Missile Chase Server" cmd /k "cd /d ^"%~dp0^" && python -m http.server 8000"

echo.
echo Opening browser...
timeout /t 2 /nobreak >nul
start "" "http://localhost:8000/game.html"

echo.
echo Done. You can close this window.
timeout /t 3 /nobreak >nul
exit /b 0