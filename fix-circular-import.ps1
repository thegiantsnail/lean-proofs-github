#!/usr/bin/env pwsh
# Fix circular import between UIObservationSite and PullbackLemmas

Write-Host "===== Fixing Circular Import Issue =====" -ForegroundColor Cyan

$projectPath = "C:\AI-Local\tel\lean-formalization\CondensedTEL"

Write-Host "`nCircular dependency detected:" -ForegroundColor Yellow
Write-Host "  UIObservationSite.lean imports PullbackLemmas.lean"
Write-Host "  PullbackLemmas.lean imports UIObservationSite.lean"
Write-Host "`nThis must be fixed before building will work.`n"

Write-Host "Solution Options:" -ForegroundColor Cyan

Write-Host "`n1. RECOMMENDED: Move common definitions to shared module" -ForegroundColor Green
Write-Host "   - Create CondensedTEL/SiteStructure.lean with shared types"
Write-Host "   - Both files import SiteStructure instead of each other"

Write-Host "`n2. QUICK FIX: Remove PullbackLemmas import from UIObservationSite" -ForegroundColor Yellow
Write-Host "   - If PullbackLemmas only provides helper lemmas"
Write-Host "   - UIObservationSite might not need to import it"

Write-Host "`n3. RESTRUCTURE: Inline lemmas where needed" -ForegroundColor Yellow
Write-Host "   - Move lemmas from PullbackLemmas into UIObservationSite"
Write-Host "   - Delete PullbackLemmas if it becomes unnecessary"

Write-Host "`nWould you like me to attempt automatic fix? (Y/N): " -ForegroundColor Cyan -NoNewline
$response = Read-Host

if ($response -eq 'Y' -or $response -eq 'y') {
    Write-Host "`nAttempting fix: Removing PullbackLemmas import from UIObservationSite..." -ForegroundColor Yellow
    
    $uiFile = Join-Path $projectPath "UIObservationSite.lean"
    $content = Get-Content $uiFile -Raw
    
    # Backup original
    $backup = $uiFile + ".backup"
    Copy-Item $uiFile $backup
    Write-Host "Backup created: $backup" -ForegroundColor Gray
    
    # Remove the import
    $newContent = $content -replace "import CondensedTEL\.PullbackLemmas\s*\n", ""
    Set-Content -Path $uiFile -Value $newContent
    
    Write-Host "✓ Import removed from UIObservationSite.lean" -ForegroundColor Green
    Write-Host "`nTesting build..." -ForegroundColor Yellow
    
    Set-Location (Join-Path $projectPath "..")
    lake build CondensedTEL.UIObservationSite 2>&1 | Tee-Object -Variable buildResult
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "`n✅ Fix successful! File builds without circular import." -ForegroundColor Green
        Remove-Item $backup
    } else {
        Write-Host "`n⚠️  Fix incomplete. UIObservationSite needs definitions from PullbackLemmas." -ForegroundColor Yellow
        Write-Host "Restoring original file..." -ForegroundColor Yellow
        Move-Item $backup $uiFile -Force
        Write-Host "`nYou'll need to manually restructure the code:" -ForegroundColor Red
        Write-Host "  1. Extract shared definitions to a new file"
        Write-Host "  2. Have both files import the shared module"
    }
} else {
    Write-Host "`nNo changes made. Please manually fix the circular import." -ForegroundColor Yellow
    Write-Host "`nManual fix steps:"
    Write-Host "  1. Review what UIObservationSite.lean needs from PullbackLemmas.lean"
    Write-Host "  2. Review what PullbackLemmas.lean needs from UIObservationSite.lean"
    Write-Host "  3. Extract shared definitions to a common module"
    Write-Host "  4. Update both files to import the common module"
}

Write-Host "`n===== Done =====" -ForegroundColor Cyan
