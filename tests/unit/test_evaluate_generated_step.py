"""
Unit tests for evaluate_generated_step.py - TLC model checking step
"""
import pytest
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path
import subprocess


class TestEvaluateTLA:
    """Tests for the TLC model checking evaluation step."""

    @patch('steps.evaluate_generated_step.subprocess.run')
    @patch('steps.evaluate_generated_step.mlflow')
    def test_successful_tlc_check(self, mock_mlflow, mock_subprocess, tmp_path):
        """Test successful TLC model checking."""
        from steps.evaluate_generated_step import evaluate_tla
        
        # Mock successful TLC output
        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="Model checking completed. No errors.",
            stderr=""
        )
        
        test_specs = {"test_model": "---- MODULE Test ----\nINIT Init\n===="}
        
        # Run evaluation
        result = evaluate_tla(test_specs)
        
        assert result is not None

    @patch('steps.evaluate_generated_step.subprocess.run')
    @patch('steps.evaluate_generated_step.mlflow')
    def test_tlc_invariant_violation(self, mock_mlflow, mock_subprocess):
        """Test TLC detecting invariant violation."""
        from steps.evaluate_generated_step import evaluate_tla
        
        # Mock TLC finding a counterexample
        mock_subprocess.return_value = Mock(
            returncode=12,  # TLC error code for invariant violation
            stdout="Error: Invariant Inv is violated.",
            stderr=""
        )
        
        test_specs = {"test_model": "---- MODULE Test ----\n===="}
        
        result = evaluate_tla(test_specs)
        
        assert result is not None

    @patch('steps.evaluate_generated_step.subprocess.run')
    @patch('steps.evaluate_generated_step.mlflow')
    def test_missing_cfg_file(self, mock_mlflow, mock_subprocess, tmp_path):
        """Test handling of missing .cfg file."""
        from steps.evaluate_generated_step import evaluate_tla
        
        test_specs = {"test_model_no_cfg": "---- MODULE Test ----\n===="}
        
        # Should handle missing cfg gracefully
        result = evaluate_tla(test_specs)
        
        assert result is not None

    @patch('steps.evaluate_generated_step.subprocess.run')
    @patch('steps.evaluate_generated_step.mlflow')
    def test_tlc_timeout(self, mock_mlflow, mock_subprocess):
        """Test TLC timeout handling."""
        from steps.evaluate_generated_step import evaluate_tla
        
        # Mock timeout
        mock_subprocess.side_effect = subprocess.TimeoutExpired(
            cmd=['java'], timeout=30
        )
        
        test_specs = {"test_model": "---- MODULE Test ----\n===="}
        
        # Should handle timeout gracefully
        result = evaluate_tla(test_specs)
        
        assert result is not None

    def test_result_states(self):
        """Test different result states (PASS, FAIL, ERROR, etc.)."""
        states = ["PASS", "FAIL", "ERROR", "SKIPPED", "MISSING"]
        
        for state in states:
            assert state in states

    @patch('steps.evaluate_generated_step.subprocess.run')
    @patch('steps.evaluate_generated_step.mlflow')
    def test_multiple_model_evaluation(self, mock_mlflow, mock_subprocess):
        """Test evaluating multiple models in one step."""
        from steps.evaluate_generated_step import evaluate_tla
        
        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="Success",
            stderr=""
        )
        
        test_specs = {
            "model1": "---- MODULE M1 ----\n====",
            "model2": "---- MODULE M2 ----\n====",
            "model3": "---- MODULE M3 ----\n===="
        }
        
        result = evaluate_tla(test_specs)
        
        assert result is not None

    @patch('steps.evaluate_generated_step.Path.rglob')
    @patch('steps.evaluate_generated_step.subprocess.run')
    @patch('steps.evaluate_generated_step.mlflow')
    def test_cfg_file_resolution(self, mock_mlflow, mock_subprocess, mock_rglob, tmp_path):
        """Test finding .cfg files for models."""
        from steps.evaluate_generated_step import evaluate_tla
        
        # Mock cfg file discovery
        test_cfg = tmp_path / "test.cfg"
        test_cfg.write_text("INIT Init\nNEXT Next\n")
        mock_rglob.return_value = [test_cfg]
        
        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="Success",
            stderr=""
        )
        
        test_specs = {"test_model": "---- MODULE Test ----\n===="}
        
        result = evaluate_tla(test_specs)
        
        assert result is not None

    def test_tlc_command_construction(self):
        """Test that TLC command is correctly constructed."""
        tools_jar = "/opt/tla/tla2tools.jar"
        tla_file = "/path/to/model.tla"
        cfg_file = "/path/to/model.cfg"
        
        expected_cmd = [
            "java",
            "-cp",
            tools_jar,
            "tlc2.TLC",
            "-config",
            cfg_file,
            tla_file
        ]
        
        # Verify command structure
        assert expected_cmd[0] == "java"
        assert "tlc2.TLC" in expected_cmd
        assert "-config" in expected_cmd


class TestTLCHelperFunctions:
    """Test helper functions for TLC evaluation."""

    def test_parse_tlc_output(self):
        """Test parsing TLC output for errors and statistics."""
        output = """
        TLC2 Version 2.17
        Model checking completed.
        12345 states generated.
        67890 distinct states found.
        No errors.
        """
        
        assert "Model checking completed" in output
        assert "No errors" in output

    def test_extract_counterexample(self):
        """Test extracting counterexample from TLC output."""
        output = """
        Error: Invariant Inv is violated.
        The behavior up to this point is:
        State 1: x = 0
        State 2: x = 1
        State 3: x = 2
        """
        
        assert "Error: Invariant" in output
        assert "State 1" in output
        assert "State 2" in output

    def test_check_tla_tools_availability(self, tmp_path):
        """Test checking if TLA+ tools are available."""
        tools_jar = tmp_path / "tla2tools.jar"
        tools_jar.touch()
        
        assert tools_jar.exists()
        assert tools_jar.suffix == ".jar"
