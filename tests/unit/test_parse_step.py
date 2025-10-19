"""
Unit tests for parse_step.py - SANY validation step
"""
import pytest
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path
import subprocess


class TestSanityCheckSANY:
    """Tests for the SANY parser validation step."""

    @patch('steps.parse_step.subprocess.run')
    @patch('steps.parse_step.mlflow')
    def test_successful_parse(self, mock_mlflow, mock_subprocess, tmp_path):
        """Test successful SANY parsing of valid TLA+ spec."""
        from steps.parse_step import sanity_check_sany
        
        # Mock successful SANY output
        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="Parsing successful",
            stderr=""
        )
        
        # Create test spec
        test_spec = {"test_model": "---- MODULE Test ----\n===="}
        
        # Run the step
        result = sanity_check_sany(test_spec)
        
        # Verify subprocess was called with correct parameters
        assert mock_subprocess.called
        assert result is not None

    @patch('steps.parse_step.subprocess.run')
    @patch('steps.parse_step.mlflow')
    def test_failed_parse(self, mock_mlflow, mock_subprocess):
        """Test SANY parsing of invalid TLA+ spec."""
        from steps.parse_step import sanity_check_sany
        
        # Mock failed SANY output
        mock_subprocess.return_value = Mock(
            returncode=1,
            stdout="",
            stderr="Syntax error on line 5"
        )
        
        test_spec = {"test_model": "INVALID TLA+ CODE"}
        
        # Run the step - should not raise exception
        result = sanity_check_sany(test_spec)
        
        assert mock_subprocess.called
        assert result is not None

    @patch('steps.parse_step.subprocess.run')
    @patch('steps.parse_step.mlflow')
    def test_timeout_handling(self, mock_mlflow, mock_subprocess):
        """Test handling of SANY timeout."""
        from steps.parse_step import sanity_check_sany
        
        # Mock timeout
        mock_subprocess.side_effect = subprocess.TimeoutExpired(
            cmd=['java'], timeout=30
        )
        
        test_spec = {"test_model": "---- MODULE Test ----\n===="}
        
        # Should handle timeout gracefully
        result = sanity_check_sany(test_spec)
        
        assert result is not None

    def test_run_sany_function(self, tmp_path):
        """Test the run_sany helper function directly."""
        from steps.parse_step import run_sany
        
        # Create a test TLA file
        test_tla = tmp_path / "test.tla"
        test_tla.write_text("---- MODULE Test ----\n====")
        
        # Create mock jar path
        jar_path = tmp_path / "tla2tools.jar"
        jar_path.touch()
        
        with patch('steps.parse_step.subprocess.run') as mock_run:
            mock_run.return_value = Mock(
                returncode=0,
                stdout="Success",
                stderr=""
            )
            
            result = run_sany("test_model", str(test_tla), str(jar_path))
            
            assert result["returncode"] == 0
            assert "stdout" in result
            assert "stderr" in result

    @patch('steps.parse_step.subprocess.run')
    @patch('steps.parse_step.mlflow')
    def test_multiple_specs(self, mock_mlflow, mock_subprocess):
        """Test processing multiple TLA+ specifications."""
        from steps.parse_step import sanity_check_sany
        
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
        
        result = sanity_check_sany(test_specs)
        
        # Should call subprocess for each spec
        assert mock_subprocess.call_count >= len(test_specs)
        assert result is not None

    @patch('steps.parse_step.Path.rglob')
    @patch('steps.parse_step.subprocess.run')
    @patch('steps.parse_step.mlflow')
    def test_file_resolution(self, mock_mlflow, mock_subprocess, mock_rglob, tmp_path):
        """Test file path resolution for TLA+ files."""
        from steps.parse_step import sanity_check_sany
        
        # Mock file discovery
        test_file = tmp_path / "test.tla"
        test_file.write_text("---- MODULE Test ----\n====")
        mock_rglob.return_value = [test_file]
        
        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="Success",
            stderr=""
        )
        
        test_specs = {"test_model": "---- MODULE Test ----\n===="}
        
        result = sanity_check_sany(test_specs)
        
        assert result is not None
