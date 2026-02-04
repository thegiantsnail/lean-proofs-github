#!/usr/bin/env pwsh
# Interactive menu for resolving Windows Error 206

Write-Host @"
╔════════════════════════════════════════════════════════════════════╗
║                                                                    ║
║         Windows Error 206 - Lean Build Problem Solver             ║
║                                                                    ║
╚════════════════════════════════════════════════════════════════════╝
"@ -ForegroundColor Cyan

Write-Host "`nRunning diagnostics..." -ForegroundColor Yellow

# Run basic checks
$projectPath = "C:\AI-Local\tel\lean-formalization"
Set-Location $projectPath

# Check WSL
Write-Host "  [1/4] Checking WSL..." -NoNewline
$wslAvailable = $false
try {
    $null = wsl --status 2>&1
    if ($LASTEXITCODE -eq 0) {
        $wslAvailable = $true
        Write-Host " ✓" -ForegroundColor Green
    } else {
        Write-Host " ✗" -ForegroundColor Red
    }
} catch {
    Write-Host " ✗" -ForegroundColor Red
}

# Check Lake
Write-Host "  [2/4] Checking Lake..." -NoNewline
$lakeAvailable = Get-Command lake -ErrorAction SilentlyContinue
if ($lakeAvailable) {
    Write-Host " ✓" -ForegroundColor Green
} else {
    Write-Host " ✗" -ForegroundColor Red
}

# Check for circular imports
Write-Host "  [3/4] Checking for circular imports..." -NoNewline
$uiFile = Get-Content "CondensedTEL\UIObservationSite.lean" -Raw
$plFile = Get-Content "CondensedTEL\PullbackLemmas.lean" -Raw
$circularImport = ($uiFile -match "import.*PullbackLemmas") -and ($plFile -match "import.*UIObservationSite")
if ($circularImport) {
    Write-Host " ⚠️  FOUND" -ForegroundColor Red
} else {
    Write-Host " ✓" -ForegroundColor Green
}

# Check for previous build artifacts
Write-Host "  [4/4] Checking build artifacts..." -NoNewline
$hasBuildArtifacts = Test-Path ".lake\build"
if ($hasBuildArtifacts) {
    Write-Host " ✓" -ForegroundColor Yellow
} else {
    Write-Host " ✗" -ForegroundColor Gray
}

Write-Host "`n" + ("═" * 70)
Write-Host "Diagnosis Complete" -ForegroundColor Cyan
Write-Host ("═" * 70) + "`n"

# Present menu
function Show-Menu {
    Write-Host "Choose a solution:`n" -ForegroundColor Cyan
    
    if ($wslAvailable) {
        Write-Host "  1) " -NoNewline -ForegroundColor White
        Write-Host "Use WSL2 (RECOMMENDED)" -ForegroundColor Green
        Write-Host "     → Avoids Windows limitations entirely" -ForegroundColor Gray
    } else {
        Write-Host "  1) " -NoNewline -ForegroundColor DarkGray
        Write-Host "Use WSL2 (Not Available)" -ForegroundColor DarkGray
    }
    
    Write-Host "`n  2) " -NoNewline -ForegroundColor White
    Write-Host "Use Mathlib Cache (Quick workaround)" -ForegroundColor Yellow
    Write-Host "     → Downloads pre-built Mathlib" -ForegroundColor Gray
    
    if ($circularImport) {
        Write-Host "`n  3) " -NoNewline -ForegroundColor White
        Write-Host "Fix Circular Imports (REQUIRED)" -ForegroundColor Red
        Write-Host "     → Must fix before any build works" -ForegroundColor Gray
    } else {
        Write-Host "`n  3) " -NoNewline -ForegroundColor DarkGray
        Write-Host "Fix Circular Imports (Already Fixed)" -ForegroundColor DarkGray
    }
    
    Write-Host "`n  4) " -NoNewline -ForegroundColor White
    Write-Host "Run Full Diagnostics" -ForegroundColor Cyan
    Write-Host "     → Detailed analysis of the problem" -ForegroundColor Gray
    
    Write-Host "`n  5) " -NoNewline -ForegroundColor White
    Write-Host "Read Full Documentation" -ForegroundColor Cyan
    Write-Host "     → Opens WINDOWS-ERROR-206-SOLUTIONS.md" -ForegroundColor Gray
    
    Write-Host "`n  Q) " -NoNewline -ForegroundColor White
    Write-Host "Quit" -ForegroundColor White
    
    Write-Host "`n"
}

do {
    Show-Menu
    Write-Host "Enter choice (1-5, Q): " -ForegroundColor Cyan -NoNewline
    $choice = Read-Host
    Write-Host ""
    
    switch ($choice) {
        "1" {
            if ($wslAvailable) {
                Write-Host "Launching WSL2 setup..." -ForegroundColor Green
                & "$projectPath\setup-wsl-lean.ps1"
            } else {
                Write-Host "WSL2 not available. Install with: wsl --install" -ForegroundColor Red
            }
            Write-Host "`nPress any key to continue..." -ForegroundColor Gray
            $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
        }
        "2" {
            Write-Host "Attempting to use Mathlib cache..." -ForegroundColor Yellow
            & "$projectPath\use-mathlib-cache.ps1"
            Write-Host "`nPress any key to continue..." -ForegroundColor Gray
            $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
        }
        "3" {
            if ($circularImport) {
                Write-Host "Attempting to fix circular imports..." -ForegroundColor Yellow
                & "$projectPath\fix-circular-import.ps1"
            } else {
                Write-Host "No circular imports detected." -ForegroundColor Green
            }
            Write-Host "`nPress any key to continue..." -ForegroundColor Gray
            $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
        }
        "4" {
            Write-Host "Running full diagnostics..." -ForegroundColor Cyan
            & "$projectPath\diagnose-build-issue.ps1"
            Write-Host "`nPress any key to continue..." -ForegroundColor Gray
            $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
        }
        "5" {
            Write-Host "Opening documentation..." -ForegroundColor Cyan
            Start-Process "notepad.exe" -ArgumentList "$projectPath\WINDOWS-ERROR-206-SOLUTIONS.md"
            Write-Host "Documentation opened in notepad." -ForegroundColor Green
            Write-Host "`nPress any key to continue..." -ForegroundColor Gray
            $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
        }
        "q" {
            Write-Host "Exiting..." -ForegroundColor White
        }
        "Q" {
            Write-Host "Exiting..." -ForegroundColor White
        }
        default {
            Write-Host "Invalid choice. Please enter 1-5 or Q." -ForegroundColor Red
            Write-Host "`nPress any key to continue..." -ForegroundColor Gray
            $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
        }
    }
    
} while ($choice -ne "q" -and $choice -ne "Q")

Write-Host "`nFor additional help, see:" -ForegroundColor Cyan
Write-Host "  - WINDOWS-ERROR-206-SOLUTIONS.md (detailed guide)" -ForegroundColor Gray
Write-Host "  - https://leanprover.zulipchat.com/ (community support)" -ForegroundColor Gray
Write-Host ""
