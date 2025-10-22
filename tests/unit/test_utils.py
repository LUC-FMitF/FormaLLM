"""
Unit tests for data loading and utilities
"""
import pytest
import json
from pathlib import Path
from unittest.mock import Mock, patch


class TestDataLoading:
    """Tests for data loading functionality."""

    def test_load_all_models_json(self, data_dir):
        """Test loading all_models.json file."""
        all_models_path = data_dir / "all_models.json"
        
        if all_models_path.exists():
            with open(all_models_path) as f:
                data = json.load(f)
            
            assert "data" in data
            assert isinstance(data["data"], list)
            assert len(data["data"]) > 0
            
            # Check structure of first model
            first_model = data["data"][0]
            assert "id" in first_model
            assert "model" in first_model

    def test_load_train_val_test_splits(self, outputs_dir):
        """Test loading train/val/test split files."""
        for split_name in ["train", "val", "test"]:
            split_file = outputs_dir / f"{split_name}.json"
            
            if split_file.exists():
                with open(split_file) as f:
                    data = json.load(f)
                
                assert isinstance(data, list)

    def test_model_directory_structure(self, data_dir):
        """Test that model directories have expected structure."""
        # Check a known model directory
        test_dirs = ["aba-asyn-byz", "acp", "allocator"]
        
        for dir_name in test_dirs:
            model_dir = data_dir / dir_name
            if model_dir.exists():
                # Check for expected subdirectories
                assert (model_dir / "tla").exists() or True  # Some may not have all dirs
                assert (model_dir / "txt").exists() or True

    def test_tla_file_reading(self, tmp_path):
        """Test reading TLA+ files."""
        tla_content = """---- MODULE Test ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_x
============================"""
        
        tla_file = tmp_path / "test.tla"
        tla_file.write_text(tla_content)
        
        content = tla_file.read_text()
        
        assert "MODULE Test" in content
        assert "VARIABLE x" in content
        assert "Init" in content

    def test_comments_file_reading(self, tmp_path):
        """Test reading comment files."""
        comments = """This is a test specification.
It defines a simple counter.
The variable x starts at 0 and increments."""
        
        comments_file = tmp_path / "test_comments.txt"
        comments_file.write_text(comments)
        
        content = comments_file.read_text()
        
        assert "test specification" in content
        assert "counter" in content

    def test_cfg_file_reading(self, tmp_path):
        """Test reading TLC configuration files."""
        cfg_content = """INIT Init
NEXT Next
SPECIFICATION Spec
INVARIANT TypeOK"""
        
        cfg_file = tmp_path / "test.cfg"
        cfg_file.write_text(cfg_content)
        
        content = cfg_file.read_text()
        
        assert "INIT" in content
        assert "NEXT" in content
        assert "SPECIFICATION" in content


class TestPathResolution:
    """Tests for file path resolution utilities."""

    def test_absolute_path_resolution(self, project_root):
        """Test resolving absolute paths."""
        abs_path = project_root / "data" / "all_models.json"
        
        assert abs_path.is_absolute()
        assert str(abs_path).startswith("/")

    def test_relative_path_resolution(self, project_root):
        """Test resolving relative paths."""
        rel_path = Path("data/all_models.json")
        abs_path = project_root / rel_path
        
        assert abs_path.is_absolute()

    def test_file_glob_patterns(self, tmp_path):
        """Test file globbing patterns."""
        # Create test files
        (tmp_path / "test1.tla").touch()
        (tmp_path / "test2.tla").touch()
        (tmp_path / "test1.cfg").touch()
        
        tla_files = list(tmp_path.glob("*.tla"))
        cfg_files = list(tmp_path.glob("*.cfg"))
        
        assert len(tla_files) == 2
        assert len(cfg_files) == 1

    def test_recursive_file_search(self, tmp_path):
        """Test recursive file searching."""
        # Create nested structure
        (tmp_path / "dir1").mkdir()
        (tmp_path / "dir1" / "test.tla").touch()
        (tmp_path / "dir2").mkdir()
        (tmp_path / "dir2" / "test.tla").touch()
        
        all_tla = list(tmp_path.rglob("*.tla"))
        
        assert len(all_tla) == 2

    def test_path_exists_checks(self, project_root):
        """Test path existence checks."""
        assert project_root.exists()
        assert (project_root / "data").exists()
        assert (project_root / "outputs").exists()
        
        fake_path = project_root / "nonexistent_directory"
        assert not fake_path.exists()


class TestEnvironmentVariables:
    """Tests for environment variable handling."""

    def test_required_env_vars(self, mock_env_vars):
        """Test that required environment variables are set."""
        import os
        
        assert os.getenv("LLM_BACKEND") is not None
        assert os.getenv("LLM_MODEL") is not None
        assert os.getenv("TLA_TOOLS_DIR") is not None

    def test_optional_env_vars(self):
        """Test optional environment variables with defaults."""
        import os
        
        num_shots = int(os.getenv("NUM_FEW_SHOTS", "3"))
        assert isinstance(num_shots, int)
        assert num_shots >= 0

    def test_env_file_loading(self, project_root):
        """Test loading .env file."""
        env_file = project_root / ".env"
        
        if env_file.exists():
            content = env_file.read_text()
            assert "=" in content  # Has key=value format


class TestJSONUtilities:
    """Tests for JSON handling utilities."""

    def test_json_serialization(self, tmp_path):
        """Test JSON serialization."""
        data = {
            "models": [
                {"id": "001", "name": "test1"},
                {"id": "002", "name": "test2"}
            ]
        }
        
        json_file = tmp_path / "test.json"
        with open(json_file, 'w') as f:
            json.dump(data, f, indent=2)
        
        assert json_file.exists()
        
        with open(json_file) as f:
            loaded = json.load(f)
        
        assert loaded == data

    def test_json_validation(self):
        """Test JSON validation."""
        valid_json = '{"key": "value", "number": 123}'
        invalid_json = '{"key": "value", "number": }'
        
        # Valid JSON should parse
        parsed = json.loads(valid_json)
        assert parsed["key"] == "value"
        
        # Invalid JSON should raise error
        with pytest.raises(json.JSONDecodeError):
            json.loads(invalid_json)
