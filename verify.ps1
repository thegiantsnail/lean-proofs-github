# Verification Script for Lean Proofs
# Run this before uploading to GitHub

Write-Host "=== Universal Equivalence Pattern - Pre-Upload Verification ===" -ForegroundColor Cyan
Write-Host ""

# Check file presence
Write-Host "Checking file presence..." -ForegroundColor Yellow
$files_ok = $true

$files = @("README.md", "lakefile.lean", "lean-toolchain", 
           "UniversalEquivalencePattern.lean", "Theorem1_FrameDeterministic.lean",
           "Theorem2_ThinTreeDeterminism.lean", "Theorem3_LanglandsTheorem.lean",
           "Theorem4_ProgramSemantics.lean")

foreach ($f in $files) {
    if (Test-Path $f) {
        Write-Host "OK $f" -ForegroundColor Green
    } else {
        Write-Host "MISSING $f" -ForegroundColor Red
        $files_ok = $false
    }
}

Write-Host ""
Write-Host "Counting lines in theorem files..." -ForegroundColor Yellow

$files_to_check = @(
    @{Name="UniversalEquivalencePattern.lean"; Expected=412},
    @{Name="Theorem1_FrameDeterministic.lean"; Expected=397},
    @{Name="Theorem2_ThinTreeDeterminism.lean"; Expected=386},
    @{Name="Theorem3_LanglandsTheorem.lean"; Expected=297},
    @{Name="Theorem4_ProgramSemantics.lean"; Expected=202}
)

foreach ($item in $files_to_check) {
    if (Test-Path $item.Name) {
        $lines = (Get-Content $item.Name | Measure-Object -Line).Lines
        $exp = $item.Expected
        Write-Host "$($item.Name): $lines lines (expected $exp)" -ForegroundColor Cyan
    }
}

Write-Host ""
Write-Host "Scanning for sorry statements..." -ForegroundColor Yellow

$sorry_total = 0
foreach ($item in $files_to_check) {
    if (Test-Path $item.Name) {
        $content = Get-Content $item.Name -Raw
        $count = ([regex]::Matches($content, "sorry")).Count
        $sorry_total += $count
        if ($count -eq 0) {
            Write-Host "$($item.Name): 0 sorry" -ForegroundColor Green
        } else {
            Write-Host "$($item.Name): $count sorry" -ForegroundColor Yellow
        }
    }
}

Write-Host ""
Write-Host "Total sorry: $sorry_total (expected 3 in examples)" -ForegroundColor Cyan

Write-Host ""
Write-Host "=== Summary ===" -ForegroundColor Cyan
if ($files_ok) {
    Write-Host "Ready for GitHub upload!" -ForegroundColor Green
    Write-Host ""
    Write-Host "Next: Review GITHUB_UPLOAD_INSTRUCTIONS.md" -ForegroundColor White
} else {
    Write-Host "Some files missing!" -ForegroundColor Red
}
Write-Host ""
