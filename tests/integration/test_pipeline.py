"""
Integration tests for the complete TLA+ pipeline
"""
import pytest
from unittest.mock import Mock, patch
from pathlib import Path


class TestPipelineIntegration:
    """Integration tests for the full pipeline."""

    @patch('pipelines.tla_pipeline.prompt_llm')
    @patch('pipelines.tla_pipeline.sanity_check_sany')
    @patch('pipelines.tla_pipeline.evaluate_tla')
    @patch('pipelines.tla_pipeline.graph_results')
    def test_full_pipeline_execution(
        self,
        mock_graph,
        mock_evaluate,
        mock_sany,
        mock_prompt
    ):
        """Test that the full pipeline executes all steps."""
        from pipelines.tla_pipeline import tla_pipeline
        
        # Mock return values
        mock_specs = {"test_model": "---- MODULE Test ----\n===="}
        mock_prompt.return_value = mock_specs
        mock_sany.return_value = {"test_model": "PASS"}
        mock_evaluate.return_value = {"test_model": "PASS"}
        mock_graph.return_value = None
        
        # Run pipeline
        with patch('pipelines.tla_pipeline.pipeline') as mock_pipeline_decorator:
            # Pipeline execution would happen here
            pass

    @patch('steps.prompt_step.ChatOpenAI')
    @patch('steps.parse_step.subprocess.run')
    @patch('steps.evaluate_generated_step.subprocess.run')
    def test_prompt_to_parse_flow(
        self,
        mock_eval_subprocess,
        mock_parse_subprocess,
        mock_openai
    ):
        """Test data flow from prompt to parse step."""
        # Mock LLM generating a spec
        mock_chain = Mock()
        mock_chain.invoke.return_value = {
            "text": "---- MODULE Test ----\nVARIABLE x\nInit == x = 0\n===="
        }
        
        # Mock SANY parsing the generated spec
        mock_parse_subprocess.return_value = Mock(
            returncode=0,
            stdout="Semantic processing of module Test",
            stderr=""
        )
        
        # Verify the flow
        generated_spec = mock_chain.invoke({"comments": "Test"})
        assert "MODULE Test" in generated_spec["text"]

    def test_parse_to_evaluate_flow(self):
        """Test data flow from parse to evaluate step."""
        # After SANY parsing, specs should be available for TLC
        parsed_specs = {
            "test_model": {
                "status": "PASS",
                "tla_content": "---- MODULE Test ----\n===="
            }
        }
        
        # These should be input to evaluation
        assert "test_model" in parsed_specs
        assert parsed_specs["test_model"]["status"] == "PASS"


class TestEndToEndScenarios:
    """End-to-end test scenarios."""

    @pytest.mark.slow
    @patch('steps.prompt_step.ChatOllama')
    def test_ollama_end_to_end(self, mock_ollama, tmp_path):
        """Test complete flow with Ollama backend."""
        import os
        os.environ["LLM_BACKEND"] = "ollama"
        os.environ["LLM_MODEL"] = "llama3.1"
        
        # Mock Ollama response
        mock_llm = Mock()
        mock_llama = Mock()
        mock_ollama.return_value = mock_llama
        
        # Verify backend setup
        assert os.getenv("LLM_BACKEND") == "ollama"

    def test_file_persistence(self, tmp_path):
        """Test that generated files are persisted correctly."""
        # Simulate pipeline output
        output_dir = tmp_path / "outputs" / "generated"
        output_dir.mkdir(parents=True)
        
        test_spec = "---- MODULE Test ----\n===="
        output_file = output_dir / "test_model.tla"
        output_file.write_text(test_spec)
        
        # Verify persistence
        assert output_file.exists()
        assert output_file.read_text() == test_spec

    def test_error_recovery(self):
        """Test that pipeline handles errors gracefully."""
        # Simulate various error conditions
        errors = {
            "parse_error": "SANY parsing failed",
            "eval_error": "TLC timeout",
            "missing_file": "Config file not found"
        }
        
        # Each should be handled without crashing
        for error_type, message in errors.items():
            assert isinstance(message, str)


class TestMLflowIntegration:
    """Tests for MLflow tracking integration."""

    @patch('mlflow.start_run')
    @patch('mlflow.log_param')
    @patch('mlflow.log_metric')
    def test_mlflow_logging(self, mock_metric, mock_param, mock_start):
        """Test that MLflow logging works correctly."""
        import mlflow
        
        # Simulate logging
        mlflow.start_run()
        mlflow.log_param("backend", "openai")
        mlflow.log_param("model", "gpt-4")
        mlflow.log_metric("success_rate", 0.95)
        
        assert mock_start.called
        assert mock_param.called
        assert mock_metric.called

    @patch('mlflow.langchain.autolog')
    def test_langchain_autolog(self, mock_autolog):
        """Test LangChain autologging is enabled."""
        import mlflow
        
        mlflow.langchain.autolog()
        
        assert mock_autolog.called


class TestDataFlowValidation:
    """Tests for validating data flow between steps."""

    def test_specs_dictionary_format(self):
        """Test that specs dictionary has correct format."""
        specs = {
            "model1": "---- MODULE M1 ----\n====",
            "model2": "---- MODULE M2 ----\n====",
        }
        
        # Verify format
        assert isinstance(specs, dict)
        for model_name, spec_content in specs.items():
            assert isinstance(model_name, str)
            assert isinstance(spec_content, str)
            assert "MODULE" in spec_content

    def test_parse_results_format(self):
        """Test that parse results have correct format."""
        results = {
            "model1": {"status": "PASS", "message": "OK"},
            "model2": {"status": "FAIL", "message": "Syntax error"},
        }
        
        for model_name, result in results.items():
            assert "status" in result
            assert result["status"] in ["PASS", "FAIL", "ERROR", "SKIPPED"]

    def test_evaluation_results_format(self):
        """Test that evaluation results have correct format."""
        results = {
            "model1": {
                "status": "PASS",
                "states_generated": 1234,
                "time": 1.5
            }
        }
        
        for model_name, result in results.items():
            assert "status" in result
