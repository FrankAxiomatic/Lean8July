#!/bin/bash

# Quantum Mechanics Formalization Verification Script
# Based on systematic verification protocol from tasks.md

TARGET_FILE=${1:-"strategy3_infrastructure.lean"}

echo "=== QUANTUM MECHANICS VERIFICATION PROTOCOL ==="
echo "Target file: $TARGET_FILE"
echo ""

echo "=== STEP 1: SORRY COUNT ==="
SORRY_COUNT=$(lake env lean "$TARGET_FILE" 2>&1 | grep -c "declaration uses 'sorry'")
echo "Sorry count: $SORRY_COUNT"

echo ""
echo "=== STEP 2: ERROR COUNT ==="
ERROR_COUNT=$(lake env lean "$TARGET_FILE" 2>&1 | grep -c "error")
echo "Error count: $ERROR_COUNT"

echo ""
echo "=== STEP 3: AXIOM COUNT ==="
AXIOM_COUNT=$(grep -c "axiom" "$TARGET_FILE")
echo "Axiom count: $AXIOM_COUNT"

echo ""
echo "=== STEP 4: BUILD STATUS ==="
if lake env lean "$TARGET_FILE" > /dev/null 2>&1; then
    echo "Build status: SUCCESS ✅"
else
    echo "Build status: FAILED ❌"
fi

echo ""
echo "=== SUMMARY ==="
echo "- Sorry count: $SORRY_COUNT (target: 0)"
echo "- Error count: $ERROR_COUNT (target: 0)"
echo "- Axiom count: $AXIOM_COUNT (target: ≤2 comments only)"

if [[ $SORRY_COUNT -eq 0 && $ERROR_COUNT -eq 0 && $AXIOM_COUNT -le 2 ]]; then
    echo ""
    echo "🎉 VERIFICATION PASSED! Ready for advanced development."
else
    echo ""
    echo "⚠️  VERIFICATION FAILED. Continue systematic fixes following tasks.md guidance."
fi

echo ""
echo "=== DETAILED ERROR ANALYSIS (if errors present) ==="
if [[ $ERROR_COUNT -gt 0 ]]; then
    echo "First 10 errors:"
    lake env lean "$TARGET_FILE" 2>&1 | grep -A1 "error:" | head -20
fi 