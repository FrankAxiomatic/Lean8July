#!/usr/bin/env python3
"""
Claude Opus Consultation Manager
Manages the complete workflow: generating requests, tracking responses, and building knowledge base.
"""

import os
import sys
import re
from pathlib import Path
from typing import Optional, Dict, List
from datetime import datetime

class OpusConsultationManager:
    """Complete management system for Claude Opus consultations."""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.lean_files = list(self.project_root.glob("*.lean"))
        self.consultations_dir = self.project_root / "opus_consultations"
        self.consultations_dir.mkdir(exist_ok=True)
        
    def detect_issue_type(self, error_message: str = "", description: str = "", line_content: str = "") -> str:
        """Automatically detect the type of consultation needed."""
        text = (error_message + " " + description + " " + line_content).lower()
        
        if any(keyword in text for keyword in ["error", "unsolved goals", "syntax", "type mismatch", "false"]):
            return "A"  # Compilation Error
        elif any(keyword in text for keyword in ["proof strategy", "mathematical approach", "how to prove", "theorem", "cloning"]):
            return "B"  # Mathematical Proof Gap
        elif any(keyword in text for keyword in ["optimize", "simplify", "better tactics", "refactor"]):
            return "C"  # Lean Implementation Optimization
        elif any(keyword in text for keyword in ["novel", "research", "new result", "publication"]):
            return "D"  # Research-Level Mathematics
        else:
            return "B"  # Default to proof strategy
    
    def read_file_with_line_numbers(self, filepath: Path, highlight_line: Optional[int] = None) -> str:
        """Read file and optionally highlight a specific line."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            result = []
            for i, line in enumerate(lines, 1):
                prefix = f"{i:4d}: "
                if highlight_line and i == highlight_line:
                    prefix = f">>> {i:4d}: "  # Highlight the problem line
                result.append(prefix + line.rstrip())
            
            return "\n".join(result)
        except Exception as e:
            return f"Error reading file {filepath}: {e}"
    
    def extract_error_context(self, filepath: Path, line_number: int, context_lines: int = 10) -> Dict[str, str]:
        """Extract code context around an error line."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            start = max(0, line_number - context_lines - 1)
            end = min(len(lines), line_number + context_lines)
            
            context = []
            for i in range(start, end):
                prefix = ">>> " if i == line_number - 1 else "    "
                context.append(f"{prefix}{i+1:4d}: {lines[i].rstrip()}")
            
            return {
                "context": "\n".join(context),
                "line_content": lines[line_number - 1].strip() if line_number <= len(lines) else "",
                "total_lines": len(lines)
            }
        except Exception as e:
            return {"context": f"Error: {e}", "line_content": "", "total_lines": 0}
    
    def get_file_size_info(self, filepath: Path) -> Dict[str, any]:
        """Get file size information for context window planning."""
        try:
            size_bytes = filepath.stat().st_size
            size_kb = size_bytes / 1024
            
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = len(f.readlines())
            
            return {
                "size_kb": round(size_kb, 1),
                "size_bytes": size_bytes,
                "lines": lines,
                "can_include_full": size_kb < 50  # 50KB threshold
            }
        except Exception as e:
            return {"size_kb": 0, "size_bytes": 0, "lines": 0, "can_include_full": False}
    
    def generate_consultation_id(self, theorem_name: str) -> str:
        """Generate unique consultation ID."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        clean_name = theorem_name.lower().replace(" ", "_").replace("-", "_")
        return f"{clean_name}_{timestamp}"
    
    def create_consultation_request(self,
                                   theorem_name: str,
                                   main_file: str,
                                   problem_line: Optional[int] = None,
                                   consultation_id: str = None) -> Dict[str, str]:
        """Generate a complete consultation request with auto-filled content."""
        
        if consultation_id is None:
            consultation_id = self.generate_consultation_id(theorem_name)
        
        main_file_path = Path(main_file)
        if not main_file_path.exists():
            return {"error": f"File {main_file} not found."}
        
        file_info = self.get_file_size_info(main_file_path)
        
        # Extract context around the problem line for auto-detection
        line_context = ""
        if problem_line:
            context_info = self.extract_error_context(main_file_path, problem_line)
            line_context = context_info.get("line_content", "")
        
        # Auto-detect issue type
        issue_type = self.detect_issue_type("", "", line_context)
        
        # Template selection
        templates = {
            "A": "Compilation Error",
            "B": "Mathematical Proof Gap", 
            "C": "Lean Implementation Optimization",
            "D": "Research-Level Mathematics"
        }
        
        template_name = templates.get(issue_type, "Mathematical Proof Gap")
        
        # Auto-fill descriptions for known issues
        description = ""
        error_message = ""
        attempted_solutions = []
        specific_questions = []
        
        if theorem_name == "No-Cloning Theorem":
            description = "Unsolved goal ⊢ False in no-cloning theorem proof. Need to prove quantum linearity forces (clone ketPlus).c01 = 0 to create contradiction with established coefficient value of 1/2."
            error_message = "unsolved goals\n⊢ False"
            attempted_solutions = [
                "Used simp tactic - didn't provide the linearity argument needed",
                "Attempted manual coefficient analysis but missing the quantum mechanics linearity principle",
                "Established contradictory coefficient values but need to prove linearity requirement"
            ]
            specific_questions = [
                "What's the most direct way to prove that quantum linearity forces (clone ketPlus).c01 = 0?",
                "Should I formalize quantum operation linearity as a separate lemma or use the superposition structure directly?",
                "How can I best use the makeSuperposition structure and coefficient analysis for this proof?",
                "Is the coefficient contradiction approach sufficient or do I need a more general linearity framework?"
            ]
        
        # Generate the consultation request content
        content = f"""# Claude Opus Consultation Request - {theorem_name}

**Consultation ID**: `{consultation_id}`
**Generated**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## Context
I'm working on a complete formalization of quantum mechanics in Lean 4, building purely from quantum postulates. This consultation focuses on a specific issue with the {theorem_name} theorem.

## Specific Issue
**Location**: Line {problem_line or "TBD"} in `{main_file}`
**Issue Type**: {template_name}
**Problem**: {description or "TBD"}
**Current Status**: {error_message or "TBD"}

## Current Implementation State

### File Information
- **Size**: {file_info['size_kb']} KB ({file_info['lines']} lines)
- **Full Context**: {'✅ Can include complete file' if file_info['can_include_full'] else '⚠️ Large file - may need summarization'}

### What Works Successfully
- {len(self.lean_files)} Lean files in project
- Complete 6-postulate quantum mechanics formalization
- All major verification theorems completed
- Complex conjugation challenges resolved
- Bell states and entanglement theory implemented

### The Exact Mathematical/Technical Gap
{description}

"""

        # Add error context if problem line specified
        if problem_line:
            context = self.extract_error_context(main_file_path, problem_line)
            content += f"""**Error Context** (lines around {problem_line}):
```lean
{context['context']}
```

**Problem Line Content**: `{context['line_content']}`

"""

        # Add error message section
        if error_message:
            content += f"""## Error Details
**Lean Error Message**:
```
{error_message}
```

"""

        # Add attempted solutions
        if attempted_solutions:
            content += "## Attempted Solutions\n"
            for i, solution in enumerate(attempted_solutions, 1):
                content += f"{i}. {solution}\n"
            content += "\n"

        # Add specific questions
        content += "## Specific Questions for Claude Opus\n\n"
        if specific_questions:
            for i, question in enumerate(specific_questions, 1):
                content += f"{i}. **Question {i}**: {question}\n\n"

        # Add mathematical background for no-cloning theorem
        if "cloning" in theorem_name.lower():
            content += """## Mathematical Theory Background

### Wootters-Zurek Insight (1982)
The proof relies on the fact that `ketPlus = (ket0 + ket1)/√2`, so quantum mechanical linearity requires:
```
clone(ketPlus) = clone((ket0 + ket1)/√2) = (clone(ket0) + clone(ket1))/√2
```

Looking at the `c01` coefficient:
```
(clone ketPlus).c01 = ((clone ket0).c01 + (clone ket1).c01)/√2 = (0 + 0)/√2 = 0
```

But perfect cloning forces `(clone ketPlus).c01 = 1/2`, giving the contradiction.

### Available Infrastructure
```lean
-- Established coefficient values
h_zero_eq : (clone ket0).c01 = 0
h_ket1_eq : (clone ket1).c01 = 0  
h_half_eq : (clone ketPlus).c01 = (1 : ℂ) / 2

-- ketPlus definition
ketPlus = makeSuperposition 1 1 (by norm_num)
-- where makeSuperposition creates normalized (a|0⟩ + b|1⟩)/‖a|0⟩ + b|1⟩‖

-- Tensor product structure
TwoQubitVec with components c00, c01, c10, c11
```

"""

        content += f"""## Desired Outcome
A complete, working solution for {theorem_name} that eliminates any compilation errors and advances the overall quantum mechanics formalization.

## Research/Project Context
This is part of a complete quantum mechanics formalization in Lean 4, building systematically toward major results like Bell inequalities, quantum cryptography, and quantum information theory.

---

## Full File Context

**File**: `{main_file}` ({file_info['size_kb']} KB)

```lean
{self.read_file_with_line_numbers(main_file_path, problem_line)}
```

---

## Instructions for Claude Opus

1. **Analyze the full file context** to understand the mathematical framework
2. **Focus on the specific issue** at line {problem_line or "[TBD]"}
3. **Provide concrete Lean 4 code** that resolves the issue
4. **Explain the mathematical reasoning** behind the solution
5. **Consider integration** with the existing codebase

**Context Window Usage**: This request is designed to maximize your context window. The complete file content provides full mathematical context for accurate analysis.

---

## Response Instructions

Please save your response in the file `opus_response_{consultation_id}.md` with the following structure:

```markdown
# Claude Opus Response - {theorem_name}

**Consultation ID**: {consultation_id}
**Response Date**: [DATE]

## Analysis
[Your analysis of the problem]

## Solution
[Complete Lean 4 code solution]

## Explanation
[Mathematical reasoning and implementation details]

## Integration Notes
[How this fits with the existing codebase]
```
"""

        return {
            "consultation_id": consultation_id,
            "content": content,
            "request_filename": f"opus_request_{consultation_id}.md",
            "response_filename": f"opus_response_{consultation_id}.md"
        }
    
    def save_consultation_request(self, consultation_data: Dict[str, str]) -> str:
        """Save the consultation request to files."""
        try:
            # Save request to opus_advice.md (main file)
            main_file = self.project_root / "opus_advice.md"
            with open(main_file, 'w', encoding='utf-8') as f:
                f.write(consultation_data["content"])
            
            # Also save to consultations directory with unique name
            consultation_file = self.consultations_dir / consultation_data["request_filename"]
            with open(consultation_file, 'w', encoding='utf-8') as f:
                f.write(consultation_data["content"])
            
            # Create placeholder response file
            response_file = self.consultations_dir / consultation_data["response_filename"]
            if not response_file.exists():
                placeholder_content = f"""# Claude Opus Response - [PENDING]

**Consultation ID**: {consultation_data["consultation_id"]}
**Response Date**: [PENDING - COPY OPUS RESPONSE HERE]

## Analysis
[Waiting for Claude Opus analysis...]

## Solution
[Waiting for Lean 4 code solution...]

## Explanation
[Waiting for mathematical reasoning...]

## Integration Notes
[Waiting for integration guidance...]

---

**Instructions**: Copy Claude Opus's complete response above, replacing this placeholder content.
"""
                with open(response_file, 'w', encoding='utf-8') as f:
                    f.write(placeholder_content)
            
            return f"""✅ Consultation request saved successfully!

📁 Files created:
- opus_advice.md (main consultation file - copy this to Claude Opus)
- {consultation_file} (archived copy)
- {response_file} (placeholder for Opus response)

🚀 Next steps:
1. Copy contents of opus_advice.md to Claude Opus
2. Paste Opus response into {response_file}
3. Apply the suggested solution to your Lean files
"""
        except Exception as e:
            return f"Error saving consultation: {e}"
    
    def create_response_template(self, consultation_id: str, theorem_name: str) -> str:
        """Create a template for saving Claude Opus responses."""
        return f"""# Claude Opus Response - {theorem_name}

**Consultation ID**: {consultation_id}
**Response Date**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## Analysis
[Copy Claude Opus analysis here]

## Solution
```lean
[Copy Lean 4 code solution here]
```

## Explanation
[Copy mathematical reasoning here]

## Integration Notes
[Copy integration guidance here]

## Follow-up Questions
[Any additional questions that arose]

---

**Status**: ✅ Response received and saved
**Applied to codebase**: [ ] Yes / [ ] No / [ ] Partially
**Results**: [Brief description of outcome after applying solution]
"""

def main():
    """Command-line interface for the consultation manager."""
    if len(sys.argv) < 2:
        print("""Usage: python3 opus_consultation_manager.py <command> [options]

Commands:
  request <theorem_name> <file> [line_number] - Generate consultation request
  response <consultation_id> - Create response template
  list - List all consultations
  
Examples:
  python3 opus_consultation_manager.py request "No-Cloning Theorem" strategy3_infrastructure.lean 443
  python3 opus_consultation_manager.py response no_cloning_theorem_20240706_224800
  python3 opus_consultation_manager.py list
""")
        return
    
    command = sys.argv[1]
    manager = OpusConsultationManager()
    
    if command == "request":
        if len(sys.argv) < 4:
            print("Error: request command requires theorem_name and file")
            return
        
        theorem_name = sys.argv[2]
        main_file = sys.argv[3]
        problem_line = int(sys.argv[4]) if len(sys.argv) > 4 else None
        
        print(f"Generating consultation request for: {theorem_name}")
        print(f"File: {main_file}, Line: {problem_line or 'Auto-detected'}")
        
        consultation_data = manager.create_consultation_request(
            theorem_name=theorem_name,
            main_file=main_file,
            problem_line=problem_line
        )
        
        if "error" in consultation_data:
            print(f"Error: {consultation_data['error']}")
            return
        
        result = manager.save_consultation_request(consultation_data)
        print(result)
        
    elif command == "response":
        if len(sys.argv) < 3:
            print("Error: response command requires consultation_id")
            return
        
        consultation_id = sys.argv[2]
        theorem_name = "Unknown"  # Could extract from consultation_id if needed
        
        template = manager.create_response_template(consultation_id, theorem_name)
        response_file = manager.consultations_dir / f"opus_response_{consultation_id}.md"
        
        with open(response_file, 'w', encoding='utf-8') as f:
            f.write(template)
        
        print(f"Response template created: {response_file}")
        print("Copy Claude Opus response into this file.")
        
    elif command == "list":
        consultations = list(manager.consultations_dir.glob("opus_request_*.md"))
        if not consultations:
            print("No consultations found.")
            return
        
        print("📋 Consultation History:")
        for req_file in sorted(consultations):
            consultation_id = req_file.stem.replace("opus_request_", "")
            resp_file = manager.consultations_dir / f"opus_response_{consultation_id}.md"
            status = "✅ Complete" if resp_file.exists() and "PENDING" not in resp_file.read_text() else "⏳ Pending"
            print(f"  - {consultation_id}: {status}")
    
    else:
        print(f"Unknown command: {command}")

if __name__ == "__main__":
    main() 