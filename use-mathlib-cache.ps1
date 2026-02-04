#!/usr/bin/env pwsh
# Use Mathlib cache to avoid Windows Error 206

Write-Host "===== Mathlib Cache Setup =====" -ForegroundColor Cyan
Write-Host "This downloads pre-built Mathlib to avoid compilation`n"

$projectPath = "C:\AI-Local\tel\lean-formalization"
Set-Location $projectPath

# Check if lake is available
if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
    Write-Host "ERROR: lake not found in PATH" -ForegroundColor Red
    Write-Host "Make sure Lean is installed (elan)" -ForegroundColor Yellow
    exit 1
}

Write-Host "Current directory: $pwd`n" -ForegroundColor Yellow

# Step 1: Clean any partial builds
Write-Host "Step 1: Cleaning previous build artifacts..." -ForegroundColor Yellow
lake clean
Write-Host "✓ Clean complete`n" -ForegroundColor Green

# Step 2: Update dependencies
Write-Host "Step 2: Updating dependencies..." -ForegroundColor Yellow
lake update
if ($LASTEXITCODE -ne 0) {
    Write-Host "⚠️  Update had issues but continuing...`n" -ForegroundColor Yellow
}

# Step 3: Get Mathlib cache
Write-Host "Step 3: Downloading Mathlib cache..." -ForegroundColor Yellow
Write-Host "(This may take several minutes depending on your connection)`n"

# Try using cache get command
lake exe cache get

if ($LASTEXITCODE -eq 0) {
    Write-Host "`n✅ Mathlib cache downloaded successfully!" -ForegroundColor Green
    
    Write-Host "`nStep 4: Building your project only..." -ForegroundColor Yellow
    lake build CondensedTEL
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "`n✅ Build successful!" -ForegroundColor Green
        Write-Host "`nYour project built without compiling Mathlib from source."
        Write-Host "This avoided the Windows command line limit issue."
    } else {
        Write-Host "`n⚠️  Build failed. Check output above for errors." -ForegroundColor Red
        Write-Host "You may have circular import issues to fix first." -ForegroundColor Yellow
    }
} else {
    Write-Host "`n⚠️  Cache download failed or not available" -ForegroundColor Yellow
    Write-Host "This could mean:"
    Write-Host "  1. No cache exists for your Mathlib version"
    Write-Host "  2. Network connectivity issues"
    Write-Host "  3. Cache server is down"
    Write-Host "`nRecommendation: Use WSL2 instead (run setup-wsl-lean.ps1)" -ForegroundColor Cyan
}

Write-Host "`n===== Done =====" -ForegroundColor Cyan
