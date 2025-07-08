# OPUS CONSULTATION TEMPLATE

## Consultation Request Format

### Basic Information
- **Date**: [YYYY-MM-DD]
- **Project**: [Project Name]
- **Issue Type**: [Mathematical/Technical/Architectural]
- **Priority**: [High/Medium/Low]

### Problem Description
**Current State**: [Describe what is currently happening]

**Expected State**: [Describe what should be happening]

**Constraint Violations**: [List any constraint violations if applicable]

### Technical Details

#### Code Context
```lean
[Include relevant Lean 4 code that shows the issue]
```

#### Error Messages
```
[Include exact error messages from Lean 4]
```

#### Verification Results
- Sorry Count: [number]
- Error Count: [number]  
- Axiom Count: [number]
- Build Status: [SUCCESS/FAILED]

### Previous Attempts
1. **Approach 1**: [Description] → [Result]
2. **Approach 2**: [Description] → [Result]
3. **Approach 3**: [Description] → [Result]

### Specific Questions
1. [Specific question about the mathematical approach]
2. [Question about implementation strategy]
3. [Question about constraint compliance]

### Expert Guidance Needed
- [ ] Mathematical theorem proving strategy
- [ ] Lean 4 syntax and best practices
- [ ] Architectural design decisions
- [ ] Performance optimization
- [ ] Literature review and references

---

## Response Processing Checklist

### After Receiving Opus Response
- [ ] Read and understand the complete response
- [ ] Extract specific implementation steps
- [ ] Identify new approaches or techniques
- [ ] Note any mathematical insights
- [ ] Plan systematic implementation
- [ ] Test incrementally with verification script
- [ ] Update documentation with learnings

### Implementation Priority
1. **Immediate fixes** (compilation errors, constraint violations)
2. **Mathematical correctness** (proof completeness, theorem validity)
3. **Architectural improvements** (clean design, maintainability)
4. **Performance optimization** (if applicable)

### Success Metrics
- [ ] Verification script passes all checks
- [ ] New approach shows measurable progress
- [ ] Mathematical rigor maintained
- [ ] Constraints still satisfied
- [ ] Documentation updated

---

## Example Successful Consultation Patterns

### Pattern 1: Complex Number Arithmetic Issues
**Problem**: Lean 4 identifier `star_I` not available
**Solution**: Use `Complex.conj_I` with systematic simp list integration
**Key Insight**: Manual proof construction less reliable than simp automation

### Pattern 2: Axiom Constraint Violations  
**Problem**: Unauthorized axiom addition
**Solution**: Replace with theorem derived from existing postulates
**Key Insight**: Foundation-first development, derive don't assume

### Pattern 3: Mathematical Goal Resolution
**Problem**: Unsolved goals in complex proofs
**Solution**: Break into smaller lemmas, use helper theorems
**Key Insight**: Incremental proof construction with verification at each step

---

## Quick Reference Commands

### Verification
```bash
./verification_script.sh [filename]
```

### Opus Consultation
```bash
python3 automated_claude_consultation.py
```

### Error Analysis
```bash
lake env lean strategy3_infrastructure.lean 2>&1 | grep -A1 "error:" | head -10
```

### Axiom Check
```bash
grep -n "axiom" strategy3_infrastructure.lean
``` 