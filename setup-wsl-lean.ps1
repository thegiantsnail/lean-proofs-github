#!/usr/bin/env pwsh
# Setup Lean build environment in WSL2 to avoid Windows Error 206

Write-Host "===== Lean WSL2 Build Setup =====" -ForegroundColor Cyan

# Check if WSL is installed
Write-Host "`nChecking WSL installation..." -ForegroundColor Yellow
$wslCheck = wsl --status 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: WSL not properly configured" -ForegroundColor Red
    Write-Host "Run: wsl --install" -ForegroundColor Yellow
    exit 1
}

# Show WSL distributions
Write-Host "`nWSL Distributions:" -ForegroundColor Yellow
wsl --list --verbose

# Check if we have a default distribution
$defaultDistro = wsl --list --quiet | Select-Object -First 1
if (-not $defaultDistro) {
    Write-Host "ERROR: No WSL distribution found" -ForegroundColor Red
    Write-Host "Install Ubuntu: wsl --install -d Ubuntu" -ForegroundColor Yellow
    exit 1
}

Write-Host "`nUsing WSL distribution: $defaultDistro" -ForegroundColor Green

# Setup script to run inside WSL
$wslScript = @'
#!/bin/bash
set -e

echo "===== Setting up Lean in WSL ====="

# Install elan (Lean version manager) if not present
if ! command -v elan &> /dev/null; then
    echo "Installing elan..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    source ~/.profile
fi

# Add elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Navigate to project (Windows path is mounted at /mnt/c/)
cd /mnt/c/AI-Local/tel/lean-formalization

echo ""
echo "===== Current Configuration ====="
elan show
echo ""

echo "===== Cleaning build artifacts ====="
lake clean

echo ""
echo "===== Starting build (this will take a while...) ====="
echo "Mathlib compilation can take 30-60 minutes on first build"
echo ""

# Build with output
lake build 2>&1 | tee wsl-build-output.txt

if [ $? -eq 0 ]; then
    echo ""
    echo "===== Build Successful! =====" 
    echo "Build output saved to: wsl-build-output.txt"
else
    echo ""
    echo "===== Build Failed =====" 
    echo "Check wsl-build-output.txt for details"
    exit 1
fi
'@

# Write the script to a temporary file
$tempScript = [System.IO.Path]::GetTempFileName()
$wslScript | Out-File -FilePath $tempScript -Encoding UTF8

# Copy script to WSL and execute
Write-Host "`nCopying setup script to WSL..." -ForegroundColor Yellow
wsl cp $tempScript /tmp/setup-lean.sh
wsl chmod +x /tmp/setup-lean.sh

Write-Host "`nExecuting build in WSL (this may take 30-60 minutes)..." -ForegroundColor Yellow
Write-Host "Press Ctrl+C to cancel`n" -ForegroundColor Gray

# Run the script in WSL
wsl bash /tmp/setup-lean.sh

# Cleanup
Remove-Item $tempScript

Write-Host "`n===== Complete =====" -ForegroundColor Green
Write-Host "Your Lean build is now in WSL2."
Write-Host "To work with it: wsl" -ForegroundColor Yellow
Write-Host "Then: cd /mnt/c/AI-Local/tel/lean-formalization" -ForegroundColor Yellow
