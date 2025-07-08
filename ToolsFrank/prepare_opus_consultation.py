#!/usr/bin/env python3
"""
Claude Opus Consultation Request Preparer
Automates the creation of consultation requests for Lean theorem issues.
"""

import os
import sys
import re
from pathlib import Path
from typing import Optional, Dict, List

class OpusConsultationPreparer:
    """Prepares consultation requests for Claude Opus with full context."""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.lean_files = list(self.project_root.glob("*.lean"))
        
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
    
    def prepare_consultation_request(self,
                                   theorem_name: str,
                                   issue_type: str,
                                   main_file: str,
                                   problem_line: Optional[int] = None,
                                   error_message: str = "",
                                   description: str = "",
                                   attempted_solutions: List[str] = None,
                                   specific_questions: List[str] = None,
                                   auto_mode: bool = False) -> str:
        """Generate a complete consultation request."""
        
        main_file_path = Path(main_file)
        if not main_file_path.exists():
            return f"Error: File {main_file} not found."
        
        file_info = self.get_file_size_info(main_file_path)
        
        # Extract context around the problem line for auto-detection
        line_context = ""
        if problem_line:
            context_info = self.extract_error_context(main_file_path, problem_line)
            line_context = context_info.get("line_content", "")
        
        # Auto-detect issue type if not provided or if auto mode
        if issue_type == "auto" or auto_mode:
            issue_type = self.detect_issue_type(error_message, description, line_context)
        
        # Template selection
        templates = {
            "A": "Compilation Error",
            "B": "Mathematical Proof Gap", 
            "C": "Lean Implementation Optimization",
            "D": "Research-Level Mathematics"
        }
        
        template_name = templates.get(issue_type, "Mathematical Proof Gap")
        
        # Auto-fill descriptions for known issues
        if auto_mode and theorem_name == "No-Cloning Theorem":
            if not description:
                description = "Unsolved goal ⊢ False in no-cloning theorem proof. Need to prove quantum linearity forces (clone ketPlus).c01 = 0 to create contradiction with established coefficient value of 1/2."
            if not error_message:
                error_message = "unsolved goals\n⊢ False"
            if not attempted_solutions:
                attempted_solutions = [
                    "Used simp tactic - didn't provide the linearity argument needed",
                    "Attempted manual coefficient analysis but missing the quantum mechanics linearity principle",
                    "Established contradictory coefficient values but need to prove linearity requirement"
                ]
            if not specific_questions:
                specific_questions = [
                    "What's the most direct way to prove that quantum linearity forces (clone ketPlus).c01 = 0?",
                    "Should I formalize quantum operation linearity as a separate lemma or use the superposition structure directly?",
                    "How can I best use the makeSuperposition structure and coefficient analysis for this proof?",
                    "Is the coefficient contradiction approach sufficient or do I need a more general linearity framework?"
                ]
        
        # Prepare content
        content = f"""# Claude Opus Consultation Request - {theorem_name}

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
        else:
            content += """1. **Primary Question**: [SPECIFIC QUESTION ABOUT THE MAIN ISSUE]

2. **Alternative Approaches**: [SHOULD I CONSIDER DIFFERENT STRATEGIES?]

3. **Lean 4 Implementation**: [WHICH TACTICS/LEMMAS WOULD BE MOST EFFECTIVE?]

4. **Broader Strategy**: [HOW DOES THIS FIT INTO THE OVERALL APPROACH?]

"""

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

"""

        # Add additional files if relevant
        other_files = [f for f in self.lean_files if f.name != main_file_path.name]
        if other_files:
            content += "\n**Additional Project Files**:\n"
            for file in other_files[:3]:  # Limit to first 3 files
                content += f"- `{file.name}` ({self.get_file_size_info(file)['size_kb']} KB)\n"
            if len(other_files) > 3:
                content += f"- ... and {len(other_files) - 3} more files\n"

        content += f"""

---

## Instructions for Claude Opus

1. **Analyze the full file context** to understand the mathematical framework
2. **Focus on the specific issue** at line {problem_line or "[TBD]"}
3. **Provide concrete Lean 4 code** that resolves the issue
4. **Explain the mathematical reasoning** behind the solution
5. **Consider integration** with the existing codebase

**Context Window Usage**: This request is designed to maximize your context window. The complete file content provides full mathematical context for accurate analysis.
"""

        return content
    
    def save_consultation_request(self, content: str, filename: str = None) -> str:
        """Save the consultation request to a file."""
        if filename is None:
            filename = "opus_advice.md"
        
        filepath = self.project_root / filename
        
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return f"Consultation request saved to: {filepath}"
        except Exception as e:
            return f"Error saving file: {e}"

def main():
    """Command-line interface for the consultation preparer."""
    if len(sys.argv) < 2:
        print("""Usage: python3 prepare_opus_consultation.py <command> [options]

Commands:
  prepare <theorem_name> <file> [line_number] [--auto] - Prepare consultation request
  analyze <file> - Analyze file for consultation readiness
  
Examples:
  python3 prepare_opus_consultation.py prepare "No-Cloning Theorem" strategy3_infrastructure.lean 443 --auto
  python3 prepare_opus_consultation.py prepare "Bell Inequalities" strategy3_infrastructure.lean 123
  python3 prepare_opus_consultation.py analyze strategy3_infrastructure.lean
""")
        return
    
    command = sys.argv[1]
    preparer = OpusConsultationPreparer()
    
    if command == "prepare":
        if len(sys.argv) < 4:
            print("Error: prepare command requires theorem_name and file")
            return
        
        theorem_name = sys.argv[2]
        main_file = sys.argv[3]
        problem_line = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != "--auto" else None
        
        # Check for auto mode
        auto_mode = "--auto" in sys.argv
        
        if auto_mode:
            print(f"Auto mode: Preparing consultation request for: {theorem_name}")
            print(f"File: {main_file}, Line: {problem_line or 'Auto-detected'}")
            
            content = preparer.prepare_consultation_request(
                theorem_name=theorem_name,
                issue_type="auto",
                main_file=main_file,
                problem_line=problem_line,
                auto_mode=True
            )
            
            result = preparer.save_consultation_request(content, "opus_advice.md")
            print(f"\n{result}")
            print(f"Ready to copy opus_advice.md content to Claude Opus!")
            
        else:
            # Interactive mode
            print(f"Preparing consultation request for: {theorem_name}")
            print(f"File: {main_file}, Line: {problem_line or 'Not specified'}")
            print()
            
            issue_type = input("Issue type (A/B/C/D/auto): ").strip() or "auto"
            description = input("Problem description: ").strip()
            error_message = input("Error message (if any): ").strip()
            
            attempted_solutions = []
            print("\nAttempted solutions (press Enter to finish):")
            while True:
                solution = input(f"Solution {len(attempted_solutions) + 1}: ").strip()
                if not solution:
                    break
                attempted_solutions.append(solution)
            
            specific_questions = []
            print("\nSpecific questions for Claude Opus (press Enter to finish):")
            while True:
                question = input(f"Question {len(specific_questions) + 1}: ").strip()
                if not question:
                    break
                specific_questions.append(question)
            
            content = preparer.prepare_consultation_request(
                theorem_name=theorem_name,
                issue_type=issue_type,
                main_file=main_file,
                problem_line=problem_line,
                error_message=error_message,
                description=description,
                attempted_solutions=attempted_solutions if attempted_solutions else None,
                specific_questions=specific_questions if specific_questions else None
            )
            
            filename = f"opus_{theorem_name.lower().replace(' ', '_').replace('-', '_')}_consultation.md"
            result = preparer.save_consultation_request(content, filename)
            print(f"\n{result}")
        
    elif command == "analyze":
        if len(sys.argv) < 3:
            print("Error: analyze command requires file")
            return
        
        main_file = sys.argv[2]
        file_path = Path(main_file)
        
        if not file_path.exists():
            print(f"Error: File {main_file} not found.")
            return
        
        info = preparer.get_file_size_info(file_path)
        print(f"File Analysis: {main_file}")
        print(f"Size: {info['size_kb']} KB ({info['lines']} lines)")
        print(f"Can include full context: {'✅ Yes' if info['can_include_full'] else '⚠️ No - too large'}")
        
        if not info['can_include_full']:
            print("\nRecommendations for large files:")
            print("- Focus on the specific problematic section")
            print("- Include only relevant imports and definitions")
            print("- Consider splitting into multiple consultations")
    
    else:
        print(f"Unknown command: {command}")

if __name__ == "__main__":
    main() 