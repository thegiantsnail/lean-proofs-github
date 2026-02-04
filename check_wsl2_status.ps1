# Quick WSL2 Build Status Check
# Run this periodically to see progress

Write-Host "`n=== WSL2 Hodge Build Status ===`n" -ForegroundColor Cyan

# Check if build is running
$buildProcess = wsl bash -c "ps aux | grep -E 'lake|lean' | grep -v grep | wc -l"
if ($buildProcess -gt 0) {
    Write-Host "🔄 Build is RUNNING ($buildProcess processes)" -ForegroundColor Yellow
} else {
    Write-Host "✅ Build processes complete" -ForegroundColor Green
}

Write-Host "`n📁 Generated .olean files:" -ForegroundColor White
wsl bash -c "cd /mnt/c/AI-Local/tel/lean-formalization && ls -lh .lake/build/lib/CondensedTEL/*.olean 2>/dev/null | awk '{print \$9, \$5}' | sed 's|.*CondensedTEL/||'"

Write-Host "`n📊 File count:" -ForegroundColor White
$olean_count = wsl bash -c "cd /mnt/c/AI-Local/tel/lean-formalization && ls .lake/build/lib/CondensedTEL/*.olean 2>/dev/null | wc -l"
Write-Host "   $olean_count .olean files (target: 6+)"

Write-Host "`n🎯 Critical files status:" -ForegroundColor White
wsl bash -c @"
cd /mnt/c/AI-Local/tel/lean-formalization
for file in ChainComplex UniversalEquivalencePattern CFGChainComplex HodgeDecomposition HodgeTELBridge; do
    if [ -f ".lake/build/lib/CondensedTEL/\$file.olean" ]; then
        echo "   ✅ \$file.olean"
    else
        echo "   ⏳ \$file.olean (building...)"
    fi
done
"@

Write-Host "`n📝 Latest build log (last 10 lines):" -ForegroundColor White
wsl bash -c "cd /mnt/c/AI-Local/tel/lean-formalization && tail -10 wsl2_complete_build.log 2>/dev/null || echo '   Log file not yet created'"

Write-Host "`n================================`n"
