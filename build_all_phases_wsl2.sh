#!/bin/bash
set -e

cd /mnt/c/AI-Local/tel/lean-formalization

echo "=== Building All Hodge Phases in WSL2 ==="
echo ""

echo "[1/5] Building UniversalEquivalencePattern..."
lake build CondensedTEL.UniversalEquivalencePattern
echo "✅ Meta-theorem Complete"
echo ""

echo "[2/5] Building ChainComplex..."
lake build CondensedTEL.ChainComplex
echo "✅ Phase 1 Complete"
echo ""

echo "[3/5] Building CFGChainComplex..."
lake build CondensedTEL.CFGChainComplex
echo "✅ Phase 2 Complete"
echo ""

echo "[4/5] Building HodgeDecomposition..."
lake build CondensedTEL.HodgeDecomposition
echo "✅ Phase 3 Complete"
echo ""

echo "[5/5] Building HodgeTELBridge..."
lake build CondensedTEL.HodgeTELBridge
echo "✅ Phase 4 Complete"
echo ""

echo "=== All Phases Built Successfully ==="
echo ""
echo "Generated .olean files:"
ls -lh .lake/build/lib/CondensedTEL/{UniversalEquivalencePattern,ChainComplex,CFGChainComplex,HodgeDecomposition,HodgeTELBridge}.olean 2>/dev/null || echo "Listing .olean files..."
find .lake/build/lib/CondensedTEL -name "*.olean" -exec ls -lh {} \;
