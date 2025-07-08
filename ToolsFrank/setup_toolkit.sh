#!/bin/bash

# ToolsFrank Setup Script
# Quantum Mechanics Formalization Toolkit

echo "🔧 ToolsFrank - Quantum Mechanics Formalization Toolkit Setup"
echo "=============================================================="

# Check if we're in the right directory
if [[ ! -f "README.md" || ! -f "verification_script.sh" ]]; then
    echo "❌ Error: Please run this script from the ToolsFrank directory"
    exit 1
fi

echo ""
echo "📋 Checking prerequisites..."

# Check for Python3
if command -v python3 &> /dev/null; then
    echo "✅ Python3 found: $(python3 --version)"
else
    echo "❌ Python3 not found. Please install Python3."
    exit 1
fi

# Check for Lean
if command -v lean &> /dev/null; then
    echo "✅ Lean found: $(lean --version)"
else
    echo "❌ Lean not found. Please install Lean 4."
    exit 1
fi

# Check for Lake
if command -v lake &> /dev/null; then
    echo "✅ Lake found"
else
    echo "❌ Lake not found. Please install Lake (Lean build system)."
    exit 1
fi

echo ""
echo "🐍 Setting up Python environment..."

# Install Python requirements
if [[ -f "requirements_opus.txt" ]]; then
    echo "Installing Python dependencies..."
    pip3 install -r requirements_opus.txt
    if [[ $? -eq 0 ]]; then
        echo "✅ Python dependencies installed"
    else
        echo "⚠️  Warning: Some Python dependencies may not have installed correctly"
    fi
else
    echo "⚠️  requirements_opus.txt not found"
fi

echo ""
echo "🔧 Setting up verification tools..."

# Make scripts executable
chmod +x verification_script.sh
echo "✅ Verification script made executable"

echo ""
echo "📚 Toolkit Contents:"
echo "- verification_script.sh: Automated verification"
echo "- VERIFICATION_TEMPLATE.md: Manual verification guide" 
echo "- tasks.md: Systematic task guidance"
echo "- opus_consultation_template.md: Expert consultation template"
echo "- Python automation scripts for Opus consultation"
echo "- Archive of successful consultations and solutions"

echo ""
echo "🚀 Quick Start:"
echo "1. For verification: ./verification_script.sh ../your_file.lean"
echo "2. For consultation: python3 automated_claude_consultation.py"
echo "3. Read tasks.md for systematic guidance"
echo "4. Use opus_consultation_template.md for expert help"

echo ""
echo "📖 Documentation:"
echo "- README.md: Complete toolkit documentation"
echo "- README_opus_consultation_system.md: Consultation system details"

echo ""
echo "🎯 Success Metrics to Track:"
echo "- Sorry Count: 0 (target)"
echo "- Error Count: 0 (target)"  
echo "- Axiom Count: ≤2 (only comments allowed)"
echo "- Build Status: SUCCESS"

echo ""
echo "✅ ToolsFrank setup complete!"
echo ""
echo "💡 Tip: Start with './verification_script.sh ../your_file.lean' to check current status"
echo "📋 Then consult 'tasks.md' for systematic guidance on improvements"
echo ""
echo "🤝 For expert help: Use 'opus_consultation_template.md' to structure consultations" 