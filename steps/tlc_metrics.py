#!/usr/bin/env python3
"""
TLC Model Checker Metrics Collection
------------------------------------

Extracts and logs comprehensive TLC model checking metrics:
  - Execution status (PASS/FAIL/ERROR/SEMANTIC_ERROR)
  - Semantic error analysis and categorization
  - Performance metrics (states, execution time)
  - State space analysis (depth, outdegree statistics)
  - Error location and type classification
  - TLC configuration and version information

Uses MLflow for metric persistence and CSV export for analysis.

Author: Brian Ortiz
License: MIT
"""

import re
from pathlib import Path
from typing import Dict, Optional, List, Tuple
from dataclasses import dataclass
import mlflow


@dataclass
class TLCMetrics:
    """
    Comprehensive metrics extracted from TLC model checker output.
    
    Covers both successful runs and various failure modes:
    - Semantic errors during parsing/analysis phase
    - Model checking failures during state exploration
    - Performance characteristics of successful runs
    """
    model_name: str
    execution_status: str  # PASS, FAIL, ERROR, SEMANTIC_ERROR, TIMEOUT, UNKNOWN
    
    # TLC Configuration
    tlc_version: Optional[str]
    workers: int
    memory_heap_mb: int
    
    # Execution Metrics
    execution_time_seconds: float
    return_code: int
    
    # Semantic Error Analysis
    semantic_error_count: int
    first_semantic_error_line: int
    first_semantic_error_type: str
    semantic_errors: List[Tuple[int, str]]  # (line, error_message)
    
    # State Space Metrics (for successful runs)
    states_generated: int
    distinct_states: int
    states_left_on_queue: int
    state_graph_depth: int
    average_outdegree: float
    min_outdegree: int
    max_outdegree: int
    
    # Temporal Properties
    has_temporal_properties: bool
    temporal_properties_result: Optional[str]
    
    # Error Details
    error_category: str  # "none", "semantic", "model_checking", "timeout", "crash"
    error_message: Optional[str]
    
    @property
    def success_rate_indicator(self) -> float:
        """Numeric indicator for success (1.0 = PASS, 0.0 = any failure)."""
        return 1.0 if self.execution_status == "PASS" else 0.0
    
    @property
    def has_semantic_issues(self) -> bool:
        """True if semantic errors were found during analysis."""
        return self.semantic_error_count > 0
    
    @property
    def state_space_coverage(self) -> str:
        """Descriptive coverage based on states explored."""
        if self.distinct_states == 0:
            return "none"
        elif self.distinct_states < 10:
            return "minimal"
        elif self.distinct_states < 100:
            return "moderate"
        elif self.distinct_states < 1000:
            return "substantial"
        else:
            return "extensive"


class TLCMetricsCollector:
    """Collects and processes TLC model checker metrics."""

    @staticmethod
    def extract_metrics(model_name: str, tlc_log_path: Path, return_code: int) -> TLCMetrics:
        """
        Extract comprehensive TLC metrics from log file.
        
        Args:
            model_name: Identifier for the specification
            tlc_log_path: Path to TLC output log
            return_code: Process return code from TLC execution
            
        Returns:
            TLCMetrics dataclass with comprehensive execution analysis
        """
        if not tlc_log_path.exists():
            return TLCMetrics(
                model_name=model_name,
                execution_status="UNKNOWN",
                tlc_version=None,
                workers=0,
                memory_heap_mb=0,
                execution_time_seconds=0.0,
                return_code=return_code,
                semantic_error_count=0,
                first_semantic_error_line=0,
                first_semantic_error_type="NoLog",
                semantic_errors=[],
                states_generated=0,
                distinct_states=0,
                states_left_on_queue=0,
                state_graph_depth=0,
                average_outdegree=0.0,
                min_outdegree=0,
                max_outdegree=0,
                has_temporal_properties=False,
                temporal_properties_result=None,
                error_category="unknown",
                error_message="TLC log file not found"
            )
        
        log_content = tlc_log_path.read_text()
        
        # Extract TLC configuration
        tlc_version = TLCMetricsCollector._extract_tlc_version(log_content)
        workers, memory_heap_mb = TLCMetricsCollector._extract_config(log_content)
        
        # Extract execution time
        execution_time = TLCMetricsCollector._extract_execution_time(log_content)
        
        # Extract semantic errors
        semantic_errors = TLCMetricsCollector._extract_semantic_errors(log_content)
        semantic_error_count = len(semantic_errors)
        first_semantic_error_line = semantic_errors[0][0] if semantic_errors else 0
        first_semantic_error_type = TLCMetricsCollector._categorize_semantic_error(
            semantic_errors[0][1] if semantic_errors else ""
        )
        
        # Extract state space metrics
        state_metrics = TLCMetricsCollector._extract_state_metrics(log_content)
        
        # Extract temporal properties info
        has_temporal_properties, temporal_result = TLCMetricsCollector._extract_temporal_info(log_content)
        
        # Determine execution status and error category
        execution_status, error_category, error_message = TLCMetricsCollector._determine_status(
            log_content, return_code, semantic_error_count
        )
        
        return TLCMetrics(
            model_name=model_name,
            execution_status=execution_status,
            tlc_version=tlc_version,
            workers=workers,
            memory_heap_mb=memory_heap_mb,
            execution_time_seconds=execution_time,
            return_code=return_code,
            semantic_error_count=semantic_error_count,
            first_semantic_error_line=first_semantic_error_line,
            first_semantic_error_type=first_semantic_error_type,
            semantic_errors=semantic_errors,
            states_generated=state_metrics.get("states_generated", 0),
            distinct_states=state_metrics.get("distinct_states", 0),
            states_left_on_queue=state_metrics.get("states_left_on_queue", 0),
            state_graph_depth=state_metrics.get("state_graph_depth", 0),
            average_outdegree=state_metrics.get("average_outdegree", 0.0),
            min_outdegree=state_metrics.get("min_outdegree", 0),
            max_outdegree=state_metrics.get("max_outdegree", 0),
            has_temporal_properties=has_temporal_properties,
            temporal_properties_result=temporal_result,
            error_category=error_category,
            error_message=error_message
        )

    @staticmethod
    def _extract_tlc_version(log_content: str) -> Optional[str]:
        """Extract TLC version from log header."""
        version_match = re.search(r"TLC2 Version ([\d.]+)", log_content)
        return version_match.group(1) if version_match else None

    @staticmethod
    def _extract_config(log_content: str) -> Tuple[int, int]:
        """Extract TLC configuration (workers, memory)."""
        workers = 0
        memory_mb = 0
        
        # Extract workers: "with 112 workers on 112 cores"
        workers_match = re.search(r"with (\d+) workers", log_content)
        if workers_match:
            workers = int(workers_match.group(1))
        
        # Extract memory: "with 30688MB heap"
        memory_match = re.search(r"with (\d+)MB heap", log_content)
        if memory_match:
            memory_mb = int(memory_match.group(1))
        
        return workers, memory_mb

    @staticmethod
    def _extract_execution_time(log_content: str) -> float:
        """Extract total execution time from TLC output."""
        # Pattern: "Finished in XXs at" or "Finished in XXmXXs at"
        time_match = re.search(r"Finished in (\d+)(?:m(\d+))?s at", log_content)
        if time_match:
            if time_match.group(2):
                minutes = int(time_match.group(1))
                seconds = int(time_match.group(2))
                total_seconds = minutes * 60 + seconds
            else:
                total_seconds = int(time_match.group(1))
            return float(total_seconds)
        return 0.0

    @staticmethod
    def _extract_semantic_errors(log_content: str) -> List[Tuple[int, str]]:
        """Extract semantic errors with line numbers and messages."""
        errors = []
        
        # Look for "Semantic errors:" section
        if "Semantic errors:" not in log_content:
            return errors
        
        # Extract error count: "*** Errors: 1"
        error_section_start = log_content.find("Semantic errors:")
        error_section = log_content[error_section_start:]
        
        # Find the end of error section (before "Starting..." or file end)
        section_end = len(error_section)
        for marker in ["Starting...", "Error: Parsing or semantic analysis failed"]:
            pos = error_section.find(marker)
            if pos != -1:
                section_end = min(section_end, pos)
        
        error_section = error_section[:section_end]
        
        # Extract individual errors: "line X, col Y to line A, col B of module ModuleName"
        error_pattern = r"line (\d+), col \d+ to line \d+, col \d+ of module \S+\s*\n\s*(.+?)(?=\n\s*\n|$)"
        matches = re.findall(error_pattern, error_section, re.DOTALL)
        
        for line_num_str, error_msg in matches:
            line_num = int(line_num_str)
            # Clean up error message (remove extra whitespace)
            clean_msg = re.sub(r'\s+', ' ', error_msg.strip())
            errors.append((line_num, clean_msg))
        
        return errors

    @staticmethod
    def _categorize_semantic_error(error_msg: str) -> str:
        """Categorize semantic error into specific type."""
        if not error_msg:
            return "NoError"
        
        msg_lower = error_msg.lower()
        
        # Unknown operator errors
        if "unknown operator" in msg_lower:
            return "Semantic Error: Unknown Operator"
        # Type mismatch errors
        elif "requires" in msg_lower and "argument" in msg_lower:
            return "Semantic Error: Argument Count Mismatch"
        # Duplicate definition
        elif "duplicate" in msg_lower or "already defined" in msg_lower:
            return "Semantic Error: Duplicate Definition"
        # Module not found
        elif "module" in msg_lower and ("not found" in msg_lower or "cannot" in msg_lower):
            return "Semantic Error: Module Not Found"
        # Type errors
        elif "type" in msg_lower or "mismatch" in msg_lower:
            return "Semantic Error: Type Mismatch"
        # Undefined reference
        elif "undefined" in msg_lower or "undeclared" in msg_lower:
            return "Semantic Error: Undefined Reference"
        else:
            return "Semantic Error: Other"

    @staticmethod
    def _extract_state_metrics(log_content: str) -> Dict:
        """Extract state space exploration metrics."""
        metrics = {
            "states_generated": 0,
            "distinct_states": 0,
            "states_left_on_queue": 0,
            "state_graph_depth": 0,
            "average_outdegree": 0.0,
            "min_outdegree": 0,
            "max_outdegree": 0
        }
        
        # "58 states generated, 13 distinct states found, 0 states left on queue."
        states_match = re.search(r"(\d+) states generated, (\d+) distinct states found, (\d+) states left on queue", log_content)
        if states_match:
            metrics["states_generated"] = int(states_match.group(1))
            metrics["distinct_states"] = int(states_match.group(2))
            metrics["states_left_on_queue"] = int(states_match.group(3))
        
        # "The depth of the complete state graph search is 4."
        depth_match = re.search(r"The depth of the complete state graph search is (\d+)", log_content)
        if depth_match:
            metrics["state_graph_depth"] = int(depth_match.group(1))
        
        # "The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 3)"
        outdegree_match = re.search(r"The average outdegree of the complete state graph is ([\d.]+) \(minimum is (\d+), the maximum (\d+)\)", log_content)
        if outdegree_match:
            metrics["average_outdegree"] = float(outdegree_match.group(1))
            metrics["min_outdegree"] = int(outdegree_match.group(2))
            metrics["max_outdegree"] = int(outdegree_match.group(3))
        
        return metrics

    @staticmethod
    def _extract_temporal_info(log_content: str) -> Tuple[bool, Optional[str]]:
        """Extract temporal properties information."""
        has_temporal = "temporal" in log_content.lower()
        
        if "Checking temporal properties" in log_content:
            if "Finished checking temporal properties" in log_content:
                return True, "completed"
            else:
                return True, "started"
        elif "Implied-temporal checking" in log_content:
            return True, "implied_temporal"
        
        return has_temporal, None

    @staticmethod
    def _determine_status(log_content: str, return_code: int, semantic_error_count: int) -> Tuple[str, str, Optional[str]]:
        """Determine execution status, error category, and error message."""
        
        # Check for successful completion
        if "Model checking completed. No error has been found." in log_content:
            return "PASS", "none", None
        
        # Check for semantic errors
        if semantic_error_count > 0 or "Semantic errors:" in log_content:
            error_msg = "Semantic analysis failed"
            if "Error: Parsing or semantic analysis failed." in log_content:
                error_msg = "Parsing or semantic analysis failed"
            return "SEMANTIC_ERROR", "semantic", error_msg
        
        # Check for TLC internal errors
        if "TLC threw an error" in log_content or "TLC encountered an unexpected exception" in log_content:
            return "ERROR", "tlc_internal", "TLC internal error"
        
        # Check for timeout
        if "timeout" in log_content.lower() or return_code == 124:
            return "TIMEOUT", "timeout", "Execution timeout"
        
        # Check for model checking failure (assertion violations, etc.)
        if "Error:" in log_content or return_code != 0:
            return "FAIL", "model_checking", "Model checking failed"
        
        # Default case
        return "UNKNOWN", "unknown", f"Unknown status (return code: {return_code})"

    @staticmethod
    def log_to_mlflow(metrics: TLCMetrics) -> None:
        """Log TLC metrics to MLflow run."""
        mlflow.log_param("tlc_execution_status", metrics.execution_status)
        mlflow.log_param("tlc_error_category", metrics.error_category)
        mlflow.log_param("tlc_version", metrics.tlc_version or "unknown")
        
        # Configuration metrics
        mlflow.log_metric("tlc_workers", metrics.workers)
        mlflow.log_metric("tlc_memory_heap_mb", metrics.memory_heap_mb)
        mlflow.log_metric("tlc_execution_time_seconds", metrics.execution_time_seconds)
        mlflow.log_metric("tlc_return_code", metrics.return_code)
        
        # Semantic error metrics
        mlflow.log_metric("tlc_semantic_error_count", metrics.semantic_error_count)
        if metrics.semantic_error_count > 0:
            mlflow.log_param("tlc_first_semantic_error_type", metrics.first_semantic_error_type)
            mlflow.log_metric("tlc_first_semantic_error_line", metrics.first_semantic_error_line)
        
        # State space metrics (for successful runs)
        if metrics.execution_status == "PASS":
            mlflow.log_metric("tlc_states_generated", metrics.states_generated)
            mlflow.log_metric("tlc_distinct_states", metrics.distinct_states)
            mlflow.log_metric("tlc_state_graph_depth", metrics.state_graph_depth)
            mlflow.log_metric("tlc_average_outdegree", metrics.average_outdegree)
            mlflow.log_param("tlc_state_space_coverage", metrics.state_space_coverage)
        
        # Temporal properties
        if metrics.has_temporal_properties:
            mlflow.log_param("tlc_temporal_properties", metrics.temporal_properties_result or "detected")
        
        # Success indicator
        mlflow.log_metric("tlc_success_indicator", metrics.success_rate_indicator)
        
        # Error details
        if metrics.error_message:
            mlflow.log_text(metrics.error_message, "tlc_error_message.txt")

    @staticmethod
    def export_csv_header() -> List[str]:
        """Return CSV header for TLC metrics."""
        return [
            "model_name",
            "execution_status",
            "tlc_version",
            "workers",
            "memory_heap_mb",
            "execution_time_seconds",
            "return_code",
            "semantic_error_count",
            "first_semantic_error_line",
            "first_semantic_error_type",
            "states_generated",
            "distinct_states",
            "states_left_on_queue",
            "state_graph_depth",
            "average_outdegree",
            "min_outdegree",
            "max_outdegree",
            "has_temporal_properties",
            "temporal_properties_result",
            "error_category",
            "error_message",
            "success_rate_indicator",
            "state_space_coverage"
        ]

    @staticmethod
    def to_csv_row(metrics: TLCMetrics) -> Dict:
        """Convert TLC metrics to CSV row dictionary."""
        return {
            "model_name": metrics.model_name,
            "execution_status": metrics.execution_status,
            "tlc_version": metrics.tlc_version or "",
            "workers": metrics.workers,
            "memory_heap_mb": metrics.memory_heap_mb,
            "execution_time_seconds": metrics.execution_time_seconds,
            "return_code": metrics.return_code,
            "semantic_error_count": metrics.semantic_error_count,
            "first_semantic_error_line": metrics.first_semantic_error_line,
            "first_semantic_error_type": metrics.first_semantic_error_type,
            "states_generated": metrics.states_generated,
            "distinct_states": metrics.distinct_states,
            "states_left_on_queue": metrics.states_left_on_queue,
            "state_graph_depth": metrics.state_graph_depth,
            "average_outdegree": metrics.average_outdegree,
            "min_outdegree": metrics.min_outdegree,
            "max_outdegree": metrics.max_outdegree,
            "has_temporal_properties": metrics.has_temporal_properties,
            "temporal_properties_result": metrics.temporal_properties_result or "",
            "error_category": metrics.error_category,
            "error_message": metrics.error_message or "",
            "success_rate_indicator": metrics.success_rate_indicator,
            "state_space_coverage": metrics.state_space_coverage
        }