# Claude Opus Consultation System for Lean Theorem Development

This system provides templates and automation tools for getting targeted, high-quality advice from Claude Opus on specific Lean theorem challenges.

## 🎯 **QUICK START**

### **For the Current No-Cloning Theorem Issue**:
```bash
python3 prepare_opus_consultation.py prepare "No-Cloning Theorem" strategy3_infrastructure.lean 443
```

This will create a consultation request file that you can copy-paste directly to Claude Opus, including:
- Full file context (564 lines)
- Specific error location highlighting  
- Mathematical background on the Wootters-Zurek proof
- Targeted questions about quantum linearity

### **For Future Theorem Issues**:
```bash
python3 prepare_opus_consultation.py prepare "Bell Inequalities" your_file.lean 123
```

## 📁 **FILE STRUCTURE**

```
├── claude_opus_advice_template.md           # Original general template
├── claude_opus_consultation_no_cloning.md   # Specific request for current issue
├── claude_opus_theorem_consultant.md        # Comprehensive template system
├── prepare_opus_consultation.py             # Automation script
└── README_opus_consultation_system.md       # This file
```

## 🔧 **SYSTEM COMPONENTS**

### **1. Automated Request Preparation** (`prepare_opus_consultation.py`)

**Features**:
- Automatically detects issue type (compilation error, proof gap, optimization, research)
- Includes full file context with line number highlighting
- Calculates file sizes for context window optimization
- Interactive prompts for specific details
- Generates properly formatted consultation requests

**Usage Examples**:
```bash
# Prepare consultation for specific theorem issue
python3 prepare_opus_consultation.py prepare "Schmidt Decomposition" quantum_info.lean 89

# Analyze file for consultation readiness  
python3 prepare_opus_consultation.py analyze strategy3_infrastructure.lean

# Get help
python3 prepare_opus_consultation.py
```

### **2. Template System** (`claude_opus_theorem_consultant.md`)

**Four Specialized Templates**:

**A. Compilation Errors** - For syntax errors, type mismatches, unsolved goals
**B. Mathematical Proof Gaps** - For strategy and mathematical insight needs  
**C. Lean Implementation Optimization** - For improving working but inefficient proofs
**D. Research-Level Mathematics** - For novel results and complex frameworks

### **3. Context Window Optimization**

**Smart File Handling**:
- Files < 50KB: Include complete content
- Files > 50KB: Focus on relevant sections with summaries
- Multiple files: Prioritize main file, list others

**Context Prioritization**:
1. Full file content (Priority 1)
2. Mathematical background (Priority 2)  
3. Attempted solutions (Priority 3)
4. Specific implementation questions (Priority 4)

## 🚀 **USAGE WORKFLOW**

### **Step 1: Identify Your Issue Type**

| Issue Type | Description | When to Use |
|------------|-------------|-------------|
| **A** | Compilation Error | Lean gives syntax/type errors |
| **B** | Mathematical Proof Gap | Need strategy/mathematical insight |
| **C** | Optimization | Working proof needs improvement |
| **D** | Research Level | Novel results, complex frameworks |

### **Step 2: Prepare Request**

**Automated Approach**:
```bash
./prepare_opus_consultation.py prepare "Your Theorem" file.lean line_number
```

**Manual Approach**:
1. Copy appropriate template from `claude_opus_theorem_consultant.md`
2. Fill in all sections systematically
3. Include complete file context

### **Step 3: Submit to Claude Opus**

**Best Practices**:
- Copy entire prepared request to Claude Opus
- Mention you're using the full context window intentionally
- Be ready to implement suggestions immediately
- Ask follow-up questions if clarification needed

### **Step 4: Document Results**

Create a record of the consultation:
```bash
# Save Opus response
echo "# Claude Opus Response - [Theorem Name]" > opus_response_[date].md
```

## 📋 **CURRENT CONSULTATION STATUS**

### **Ready for Immediate Use**:

**No-Cloning Theorem** (`claude_opus_consultation_no_cloning.md`):
- ✅ Complete request prepared
- ✅ Full 564-line file context included
- ✅ Specific mathematical gap identified (quantum linearity at line 443)
- ✅ Targeted questions about Wootters-Zurek proof approach
- **Action**: Copy content to Claude Opus for immediate consultation

### **Future Consultations Planned**:
- Bell Inequalities (CHSH violation proof)
- Schmidt Decomposition (existence theorem)
- Quantum Error Correction (3-qubit code)
- Von Neumann Entropy (density matrix formalism)

## 🎯 **OPTIMIZATION STRATEGIES**

### **Context Window Maximization**:

**For Large Projects**:
1. **Primary file**: Include complete content
2. **Related files**: Summarize key definitions
3. **Background**: Include relevant mathematical theory
4. **Focus**: Highlight specific problematic areas

**For Complex Issues**:
1. **Break into sub-problems**: Address each component separately
2. **Sequential consultations**: Build on previous Opus responses
3. **Cross-reference**: Link related consultation requests

### **Question Quality Guidelines**:

**❌ Avoid Vague Questions**:
- "How do I prove this theorem?"
- "My proof doesn't work"
- "Help with quantum mechanics"

**✅ Use Specific, Targeted Questions**:
- "What's the most direct way to prove linearity forces coefficient X = 0?"
- "Line 443 gives 'unsolved goal ⊢ False' - which tactic resolves this specific goal state?"
- "Should I formalize quantum operation linearity as a separate lemma or use coefficient analysis directly?"

## 🔍 **TROUBLESHOOTING**

### **Common Issues**:

**File Too Large for Context Window**:
```bash
# Check file size first
./prepare_opus_consultation.py analyze large_file.lean

# If too large, focus on problematic section
./prepare_opus_consultation.py prepare "Issue Name" large_file.lean 123
```

**Multiple Related Issues**:
- Create separate consultation for each major issue
- Reference previous consultations in new requests
- Build systematically from simpler to complex problems

**Unclear Error Messages**:
- Include exact Lean output
- Provide goal state from InfoView
- Add context about what you expected vs. what happened

## 📚 **TEMPLATE CUSTOMIZATION**

### **Adding New Issue Types**:

Edit `prepare_opus_consultation.py`:
```python
def detect_issue_type(self, error_message: str = "", description: str = "") -> str:
    # Add new classification logic
    if "your_keyword" in text:
        return "E"  # New issue type
```

### **Project-Specific Templates**:

Create specialized templates for your research area:
- Quantum mechanics formalization
- Category theory development  
- Algebraic geometry projects
- Logic and foundations

### **Integration with Development Workflow**:

```bash
# Add to your Lean development script
alias opus_help='./prepare_opus_consultation.py prepare'
alias opus_check='./prepare_opus_consultation.py analyze'

# Quick consultation preparation
opus_help "Current Issue" current_file.lean $(current_line_number)
```

## 🎓 **BEST PRACTICES LEARNED**

### **Effective Consultation Patterns**:

1. **Start with Broad Context**: Include complete mathematical framework
2. **Focus on Specific Gap**: Identify exact missing piece  
3. **Provide Attempted Solutions**: Show what you've tried
4. **Ask Implementation Questions**: Get concrete Lean 4 tactics
5. **Plan Integration**: Consider how solution fits broader project

### **Common Success Factors**:

- **Complete Context**: Never summarize - include full file content
- **Specific Questions**: Target exact technical gaps
- **Mathematical Background**: Include relevant theory/literature
- **Ready Implementation**: Be prepared to act on suggestions immediately
- **Follow-up Strategy**: Plan next steps based on Opus response

---

## 🚀 **GET STARTED NOW**

For your current no-cloning theorem issue:

1. **Open**: `claude_opus_consultation_no_cloning.md`
2. **Copy**: Complete content to Claude Opus
3. **Submit**: Request analysis and solution
4. **Implement**: Apply suggestions to `strategy3_infrastructure.lean`
5. **Document**: Save response for future reference

This system is designed to maximize the value of Claude Opus consultations while building a knowledge base for systematic Lean theorem development. 