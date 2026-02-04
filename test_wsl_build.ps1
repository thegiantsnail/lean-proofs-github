# Test WSL2 Lean Build
Write-Host "=== Testing WSL2 Build Environment ===" -ForegroundColor Cyan

Write-Host "`n1. Checking WSL2 Lean installation..."
wsl bash -c "source ~/.profile && which lake && lake --version"

Write-Host "`n2. Building CFGChainComplex in WSL2..."
wsl bash -c "source ~/.profile && cd /mnt/c/AI-Local/tel/lean-formalization && timeout 300 lake build CondensedTEL.CFGChainComplex 2>&1 | tail -30"

Write-Host "`n3. Checking for .olean file generation..."
wsl bash -c "ls -lh /mnt/c/AI-Local/tel/lean-formalization/.lake/build/lib/CondensedTEL/CFGChainComplex.olean 2>&1"

Write-Host "`n4. Building HodgeDecomposition in WSL2..."
wsl bash -c "source ~/.profile && cd /mnt/c/AI-Local/tel/lean-formalization && timeout 300 lake build CondensedTEL.HodgeDecomposition 2>&1 | tail -30"

Write-Host "`n5. Checking for .olean file..."
wsl bash -c "ls -lh /mnt/c/AI-Local/tel/lean-formalization/.lake/build/lib/CondensedTEL/HodgeDecomposition.olean 2>&1"

Write-Host "`n6. Building HodgeTELBridge in WSL2..."
wsl bash -c "source ~/.profile && cd /mnt/c/AI-Local/tel/lean-formalization && timeout 300 lake build CondensedTEL.HodgeTELBridge 2>&1 | tail -30"

Write-Host "`n7. Final check - all Hodge .olean files..."
wsl bash -c "ls -lh /mnt/c/AI-Local/tel/lean-formalization/.lake/build/lib/CondensedTEL/{CFGChainComplex,HodgeDecomposition,HodgeTELBridge}.olean 2>&1"

Write-Host "`n=== Test Complete ===" -ForegroundColor Green
