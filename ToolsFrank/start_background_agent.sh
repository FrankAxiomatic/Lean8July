#!/bin/bash

# Quantum Background Agent Startup Script
# Starts the background agent with memory MCP integration

echo "🚀 Starting Quantum Background Agent with Memory MCP..."
echo "=============================================================="

# Check if we're in the right directory
if [[ ! -f "quantum_background_agent.py" ]]; then
    echo "❌ Error: Please run this script from the ToolsFrank directory"
    exit 1
fi

# Check for virtual environment
if [[ ! -d "quantum_agent_env" ]]; then
    echo "❌ Error: Virtual environment not found. Run setup first."
    exit 1
fi

# Activate virtual environment
echo "🐍 Activating Python environment..."
source quantum_agent_env/bin/activate

# Check for API key
if [[ -z "$ANTHROPIC_API_KEY" ]]; then
    echo "⚠️  Warning: ANTHROPIC_API_KEY not set. Expert consultation will be disabled."
    echo "   Set with: export ANTHROPIC_API_KEY=your_api_key"
fi

# Create log directory
mkdir -p logs

echo ""
echo "🔧 Configuration:"
echo "- Project Directory: $(readlink -f ..)"
echo "- Memory File: agent_memory.json"
echo "- Log File: quantum_agent.log"
echo "- Status Reports: quantum_status_report.md"

echo ""
echo "📊 Background Agent Features:"
echo "✅ Memory MCP integration (persistent across sessions)"
echo "✅ File monitoring (automatic verification on changes)"  
echo "✅ Automated verification (using ToolsFrank system)"
echo "✅ Expert consultation (Claude Opus integration)"
echo "✅ Status reporting (every 15 minutes)"
echo "✅ Issue analysis (automatic failure analysis)"

echo ""
echo "🎯 Success Metrics Tracking:"
echo "- Sorry Count: Target 0"
echo "- Error Count: Target 0"
echo "- Axiom Count: Target ≤2"
echo "- Build Status: Target SUCCESS"

echo ""
echo "🚀 Starting background agent..."
echo "   Press Ctrl+C to stop"
echo ""

# Start the background agent
python3 quantum_background_agent.py 