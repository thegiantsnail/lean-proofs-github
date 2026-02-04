#!/usr/bin/env pwsh
# Diagnose Windows Error 206 - Command Line Too Long

Write-Host "===== Windows Build Diagnostics =====" -ForegroundColor Cyan

Write-Host "`n1. Checking path lengths..." -ForegroundColor Yellow
$projectPath = "C:\AI-Local\tel\lean-formalization"
Write-Host "Project path: $projectPath"
Write-Host "Path length: $($projectPath.Length) characters"

$lakeBuildPath = Join-Path $projectPath ".lake\build"
if (Test-Path $lakeBuildPath) {
    $objFiles = Get-ChildItem -Path $lakeBuildPath -Filter "*.o" -Recurse
    $totalObjFiles = $objFiles.Count
    $avgPathLength = ($objFiles | Measure-Object -Property FullName -Average -Maximum).Average
    $maxPathLength = ($objFiles | Measure-Object -Property FullName -Average -Maximum).Maximum
    
    Write-Host "Object files found: $totalObjFiles"
    Write-Host "Average path length: $([int]$avgPathLength) characters"
    Write-Host "Maximum path length: $([int]$maxPathLength) characters"
    
    # Estimate command line length
    $estimatedCmdLength = $totalObjFiles * $avgPathLength + 500
    Write-Host "`nEstimated command line length: $([int]$estimatedCmdLength) characters" -ForegroundColor $(if ($estimatedCmdLength -gt 8191) { "Red" } else { "Green" })
    Write-Host "Windows limit: 8191 characters" -ForegroundColor Yellow
    
    if ($estimatedCmdLength -gt 8191) {
        Write-Host "`n⚠️  PROBLEM IDENTIFIED: Command line will exceed Windows limit!" -ForegroundColor Red
    }
}

Write-Host "`n2. Checking for build cycle issues..." -ForegroundColor Yellow
if (Test-Path (Join-Path $projectPath "build_output.txt")) {
    $buildOutput = Get-Content (Join-Path $projectPath "build_output.txt") -Raw
    if ($buildOutput -match "build cycle detected") {
        Write-Host "⚠️  Build cycle detected in previous build!" -ForegroundColor Red
        if ($buildOutput -match "UIObservationSite|PullbackLemmas") {
            Write-Host "   Issue: Circular imports between UIObservationSite and PullbackLemmas" -ForegroundColor Yellow
        }
    }
}

Write-Host "`n3. Checking Lean/Lake versions..." -ForegroundColor Yellow
if (Get-Command lake -ErrorAction SilentlyContinue) {
    & lake --version
    & lean --version
} else {
    Write-Host "Lake not found in PATH" -ForegroundColor Red
}

Write-Host "`n===== Recommendations =====" -ForegroundColor Cyan

Write-Host "`n✅ BEST SOLUTION: Use WSL2" -ForegroundColor Green
Write-Host "   Run: .\setup-wsl-lean.ps1"
Write-Host "   This avoids Windows command line limits entirely"

Write-Host "`n⚠️  WORKAROUND: Fix circular imports first" -ForegroundColor Yellow
Write-Host "   The build cycle must be fixed before building will work"
Write-Host "   Check CondensedTEL/UIObservationSite.lean and CondensedTEL/PullbackLemmas.lean"

Write-Host "`n📋 Alternative: Use cached Mathlib" -ForegroundColor Yellow
Write-Host "   Run: lake exe cache get"
Write-Host "   This downloads pre-built Mathlib to avoid compilation"
