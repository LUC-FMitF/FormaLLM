#!/usr/bin/env python3
"""
SANY Syntax Parsing Metrics Collection
---------------------------------------

Extracts and logs:
  - Parse success/failure status
  - Error count and categorization
  - Error types (SyntaxError, TypeError, UndefinedError, etc.)
  - Parse timing information
  - Recoverable error detection

Uses MLflow for metric persistence and CSV export for analysis.

Inspired by TLA+ Foundation Examples validation approach.

Author: Brian Ortiz
License: MIT
"""

import re
from pathlib import Path
from typing import Dict, Optional, List
from dataclasses import dataclass
import mlflow


@dataclass
class SyntaxMetrics:
    """
    Metrics extracted from SANY parser output.
    
    SANY stops at first fatal error (architectural limitation).
    Therefore: error_count ≤ 1, and we only see first error per spec.

    """
    model_name: str
    parse_status: str  
    first_error_line: int  # Line number of first error (0 if none)
    first_error_type: str  # SyntaxError, TypeError, UndefinedError, etc.
    error_location_category: str  # "early" (0-10), "mid" (10-50), "late" (50+), "none"
    error_types_found: List[str]  # All error types found on first error line
    first_error_message: Optional[str]

    @property
    def error_in_early_lines(self) -> bool:
        """True if first error is in early lines (0-10) - descriptive only."""
        return self.first_error_line < 10 and self.first_error_line > 0

    @property
    def error_in_module_header(self) -> bool:
        """True if error is in typical module def area (0-20) - descriptive only."""
        return self.first_error_line < 20 and self.first_error_line > 0



class SANYMetricsCollector:
    """Collects and processes SANY validation metrics."""

    @staticmethod
    def extract_metrics(model_name: str, sany_log_path: Path) -> SyntaxMetrics:
        """
        Extract syntax metrics from SANY log file.
        
        Args:
            model_name: Identifier for the specification
            sany_log_path: Path to SANY output log
            
        Returns:
            SyntaxMetrics dataclass with FIRST ERROR ONLY (SANY stops at first):
            - parse_status: str ("PASSED" or "FAILED")
            - first_error_line: int (line number of first error, 0 if none)
            - first_error_type: str (SyntaxError, TypeError, etc.)
            - error_location_category: str ("early", "mid", "late", or "none")
            - error_types_found: list of error types on first error
            - first_error_message: str (first error message encountered)
        
        IMPORTANT: Due to SANY architectural limitation, we see only first error.
        All specs show ≤1 error count. Cannot assess total errors or error density.
        """
        if not sany_log_path.exists():
            return SyntaxMetrics(
                model_name=model_name,
                parse_status="UNKNOWN",
                first_error_line=0,
                first_error_type="NoLog",
                error_location_category="none",
                error_types_found=[],
                first_error_message="SANY log file not found"
            )
        
        log_content = sany_log_path.read_text()
        
        # Check for successful parse: "Parsing completed" indicates success
        # and absence of error keywords indicates no issues
        has_errors = any(keyword in log_content for keyword in ["error", "Error", "ERROR", "Fatal", "Abort", "***Parse Error***"])
        parse_success = "Parsing completed" in log_content and not has_errors
        
        # Extract errors with improved patterns that avoid stack trace artifacts
        errors = []
        seen_lines = set()
        
        # SANY output structure:
        #   1. Error description (***Parse Error***, Lexical error, etc.)
        #   2. Residual stack trace (module definitions starting at lines X, Y, Z)
        #   3. Fatal error message
        # SANY LIMITATION: Parser stops at first fatal error; cannot continue parsing.
        # Therefore, error_count represents only the first fatal error(s) encountered.
        error_section = log_content
        if "Fatal errors while parsing" in log_content:
            error_section = log_content.split("Fatal errors while parsing")[0]
        if "Residual stack trace" in error_section:
            error_section = error_section.split("Residual stack trace")[0]
        
        # Pattern 1: SANY "line N, column C" format (actual parse errors)
        line_pattern = r"line\s+(\d+),\s*column\s+\d+"
        line_matches = re.finditer(line_pattern, error_section)
        for match in line_matches:
            line_num = int(match.group(1))
            if line_num not in seen_lines:
                seen_lines.add(line_num)
                # Get context around the match to extract error message
                start_pos = max(0, match.start() - 50)
                end_pos = min(len(error_section), match.end() + 150)
                context = error_section[start_pos:end_pos]
                errors.append((line_num, context))
        
        # Pattern 2: Lexical error format - multiple variations
        # Matches: "Lexical error at line N, column C"
        #          "Lexical {error: ... around line N"
        #          "Lexical error at line N"
        lexical_pattern = r"[Ll]exical\s+(?:\{)?error.*?(?:line|around line)\s+(\d+)"
        lexical_matches = re.finditer(lexical_pattern, error_section, re.DOTALL)
        for match in lexical_matches:
            line_num = int(match.group(1))
            if line_num not in seen_lines:
                seen_lines.add(line_num)
                start_pos = max(0, match.start())
                end_pos = min(len(error_section), match.end() + 150)
                context = error_section[start_pos:end_pos]
                errors.append((line_num, context))
        
        # Pattern 3: Traditional format with colon-separated error
        colon_pattern = r"line\s+(\d+):\s*(error|Error|ERROR):\s*(.*?)(?:\n|$)"
        colon_matches = re.findall(colon_pattern, error_section, re.IGNORECASE)
        for line_num_str, error_keyword, error_msg in colon_matches:
            line_num = int(line_num_str)
            if line_num not in seen_lines:
                seen_lines.add(line_num)
                errors.append((line_num, error_msg))
        
        # Remove duplicates and sort by line number
        errors = list({(e[0], e[1]) for e in errors})
        errors.sort(key=lambda x: x[0])
        
        error_count = len(errors)
        error_lines = []
        max_error_line = 0
        first_error_message = None
        first_error_type = "NoError"
        error_types_set = set()
        
        if errors:
            # Get first error (SANY only shows first fatal error)
            first_line_num, first_context = errors[0]
            max_error_line = first_line_num
            error_lines.append(first_line_num)
            
            # Extract error message from context
            error_context_str = str(first_context)
            first_error_message = error_context_str[:200].strip()
            
            # Categorize error type using FULL LOG for context
            # (not just the error line context)
            first_error_type = SANYMetricsCollector._categorize_error(log_content)
            error_types_set.add(first_error_type)
        
        # Determine error location category
        if max_error_line == 0:
            error_location_category = "none"
        elif max_error_line < 10:
            error_location_category = "early"
        elif max_error_line < 50:
            error_location_category = "mid"
        else:
            error_location_category = "late"
        
        # Parse status: FAILED if errors found
        parse_status = "FAILED" if error_count > 0 else "PASSED"
        
        # Get all error types found (for reporting)
        error_types_list = list(error_types_set) if error_types_set else []
        
        return SyntaxMetrics(
            model_name=model_name,
            parse_status=parse_status,
            first_error_line=max_error_line,  # Only first error per SANY limitation
            first_error_type=first_error_type,
            error_location_category=error_location_category,
            error_types_found=error_types_list,
            first_error_message=first_error_message
        )

    @staticmethod
    def _categorize_error(error_msg: str) -> str:
        """
        Categorize SANY error message into specific type.
        
        Extracts specific error types:
        - Parse vs Lexical errors
        - Character-specific lexical issues  
        - Module body vs other parse issues
        """
        msg_str = str(error_msg)
        
        # === PARSE ERRORS ===
        if "***Parse Error***" in msg_str:
            if 'Was expecting "==== or more Module body"' in msg_str:
                return "Parse Error: Bad Module Body"
            elif "Was expecting" in msg_str:
                return "Parse Error: Unexpected Token"
            else:
                return "Parse Error: Other"
        
        # === LEXICAL ERRORS - Specific characters ===
        elif "Lexical error" in msg_str or "Lexical {error" in msg_str:
            # Backtick character (common in LLM-generated specs using code blocks)
            if 'Encountered: "`"' in msg_str:
                return "Lexical Error: Backtick Character"
            # Invalid Unicode (en-dash instead of em-dash)
            elif 'Encountered: "\u2013"' in msg_str or "Encountered: \"\u2013\"" in msg_str:
                return "Lexical Error: Invalid Unicode (En Dash)"
            # Question mark (syntax error)
            elif 'Encountered: "?"' in msg_str:
                return "Lexical Error: Question Mark"
            # Newline character (parsing line when should not)
            elif 'Encountered: "\n"' in msg_str:
                return "Lexical Error: Newline in Expression"
            # Semicolon (not valid in TLA+)
            elif 'Encountered: ";"' in msg_str:
                return "Lexical Error: Semicolon"
            # Space after question mark (parameter parsing issue)
            elif 'after : "?"' in msg_str and 'Encountered: " "' in msg_str:
                return "Lexical Error: Space After Question"
            # Unclosed comment (EOF before comment closed)
            elif "EOF reached" in msg_str and "comment" in msg_str.lower():
                return "Lexical Error: Unclosed Comment"
            else:
                return "Lexical Error: Other"
        
        # === SEMANTIC/TYPE ERRORS ===
        elif "type" in msg_str.lower() or "mismatch" in msg_str.lower():
            return "Semantic Error: Type Mismatch"
        elif "undefined" in msg_str.lower() or "not found" in msg_str.lower():
            return "Semantic Error: Undefined Operator"
        elif "duplicate" in msg_str.lower():
            return "Semantic Error: Duplicate Definition"
        
        else:
            return "Unknown Error"

    @staticmethod
    def log_to_mlflow(metrics: SyntaxMetrics) -> None:
        """
        Log syntax metrics to MLflow run (FACTUAL DATA).
        
        Args:
            metrics: SyntaxMetrics dataclass to log
        """
        mlflow.log_param("model_name", metrics.model_name)
        mlflow.log_param("parse_status", metrics.parse_status)
        mlflow.log_param("error_location_category", metrics.error_location_category)
        
        mlflow.log_metric("first_error_line", metrics.first_error_line)
        mlflow.log_param("first_error_type", metrics.first_error_type)
        
        if metrics.error_types_found:
            mlflow.log_param("error_types_found", ",".join(metrics.error_types_found))
        
        if metrics.first_error_message:
            mlflow.log_text(metrics.first_error_message, "first_error.txt")

    @staticmethod
    def export_csv_header() -> list:
        """Return CSV header for syntax metrics (FACTUAL DATA ONLY)."""
        return [
            "model_name",
            "parse_status",
            "first_error_line",
            "first_error_type",
            "error_location_category",
            "error_types_found",
            "first_error_message"
        ]

    @staticmethod
    def to_csv_row(metrics: SyntaxMetrics) -> dict:
        """Convert metrics to CSV row dictionary (factual data only)."""
        return {
            "model_name": metrics.model_name,
            "parse_status": metrics.parse_status,
            "first_error_line": metrics.first_error_line,
            "first_error_type": metrics.first_error_type,
            "error_location_category": metrics.error_location_category,
            "error_types_found": ",".join(metrics.error_types_found),
            "first_error_message": metrics.first_error_message or ""
        }
