# Testing Guide for FormaLLM

This guide covers testing practices, running tests, and contributing test code to FormaLLM.

## Table of Contents

- [Quick Start](#quick-start)
- [Test Structure](#test-structure)
- [Running Tests](#running-tests)
- [Writing Tests](#writing-tests)
- [Test Categories](#test-categories)
- [Continuous Integration](#continuous-integration)
- [Best Practices](#best-practices)

## Quick Start

### Setup Testing Environment

```bash
# Run the setup script
./setup.sh --test

# Or manually:
source venv/bin/activate
pip install -r requirements.txt
```

### Run All Tests

```bash
pytest tests/
```

### Run Specific Test Categories

```bash
# Run only unit tests
pytest tests/unit/

# Run only integration tests  
pytest tests/integration/

# Run a specific test file
pytest tests/unit/test_parse_step.py

# Run a specific test
pytest tests/unit/test_parse_step.py::TestSanityCheckSANY::test_successful_parse
```

## Test Structure

The test suite is organized as follows:

```
tests/
├── __init__.py              # Test package initialization
├── conftest.py              # Shared pytest fixtures
├── unit/                    # Unit tests
│   ├── test_parse_step.py
│   ├── test_prompt_step.py
│   ├── test_evaluate_generated_step.py
│   └── test_utils.py
├── integration/             # Integration tests
│   └── test_pipeline.py
└── fixtures/                # Test data and fixtures
    ├── simple_counter.tla
    ├── simple_counter.cfg
    ├── simple_counter_comments.txt
    └── test_models.json
```

## Running Tests

### Basic Commands

```bash
# Run all tests with verbose output
pytest tests/ -v

# Run with coverage report
pytest tests/ --cov=steps --cov=pipelines --cov-report=html

# Run and show print statements
pytest tests/ -s

# Run fast tests only (skip slow tests)
pytest tests/ -m "not slow"

# Run tests matching a pattern
pytest tests/ -k "parse"
```

### Test Markers

Tests can be marked with custom markers for selective execution:

```bash
# Run only unit tests
pytest tests/ -m unit

# Run only integration tests
pytest tests/ -m integration

# Skip tests requiring TLA+ tools
pytest tests/ -m "not requires_tla"

# Skip tests requiring LLM API
pytest tests/ -m "not requires_llm"

# Skip tests requiring Ollama
pytest tests/ -m "not requires_ollama"
```

### Viewing Test Results

```bash
# Generate HTML coverage report
pytest tests/ --cov=steps --cov=pipelines --cov-report=html
open htmlcov/index.html  # macOS
xdg-open htmlcov/index.html  # Linux

# Show slowest tests
pytest tests/ --durations=10

# Show test summary
pytest tests/ -ra
```

## Writing Tests

### Unit Test Example

```python
"""
Unit tests for a new step
"""
import pytest
from unittest.mock import Mock, patch


class TestNewStep:
    """Tests for the new step."""

    @patch('steps.new_step.some_dependency')
    def test_basic_functionality(self, mock_dep):
        """Test basic functionality of the step."""
        from steps.new_step import new_function
        
        # Setup mocks
        mock_dep.return_value = "expected_value"
        
        # Run test
        result = new_function("input")
        
        # Assertions
        assert result == "expected_value"
        assert mock_dep.called

    def test_error_handling(self):
        """Test that errors are handled gracefully."""
        from steps.new_step import new_function
        
        with pytest.raises(ValueError):
            new_function(None)
```

### Integration Test Example

```python
"""
Integration tests for multi-step workflows
"""
import pytest
from unittest.mock import patch


class TestWorkflow:
    """Tests for complete workflows."""

    @patch('steps.step1.external_call')
    @patch('steps.step2.external_call')
    def test_full_workflow(self, mock_step2, mock_step1):
        """Test complete workflow execution."""
        # Setup
        mock_step1.return_value = {"data": "from_step1"}
        mock_step2.return_value = {"data": "from_step2"}
        
        # Execute workflow
        from pipelines.my_pipeline import run_pipeline
        result = run_pipeline()
        
        # Verify
        assert result is not None
        assert mock_step1.called
        assert mock_step2.called
```

### Using Fixtures

Fixtures are defined in `tests/conftest.py` and can be used in any test:

```python
def test_with_fixtures(project_root, sample_tla_spec):
    """Test using shared fixtures."""
    # project_root is automatically provided
    assert project_root.exists()
    
    # sample_tla_spec provides test data
    assert "MODULE" in sample_tla_spec
```

### Creating New Fixtures

Add fixtures to `tests/conftest.py`:

```python
@pytest.fixture
def my_custom_fixture():
    """Provide custom test data."""
    return {
        "key": "value",
        "data": [1, 2, 3]
    }
```

## Test Categories

### Unit Tests

**Location**: `tests/unit/`  
**Purpose**: Test individual functions and methods in isolation  
**Characteristics**:
- Fast execution
- Mock external dependencies
- Test single units of code
- No file I/O or network calls

**Files**:
- `test_parse_step.py` - SANY parser validation
- `test_prompt_step.py` - LLM prompting logic
- `test_evaluate_generated_step.py` - TLC model checking
- `test_utils.py` - Utility functions and helpers

### Integration Tests

**Location**: `tests/integration/`  
**Purpose**: Test interactions between multiple components  
**Characteristics**:
- Slower execution
- May use real file I/O
- Test data flow between steps
- Verify complete workflows

**Files**:
- `test_pipeline.py` - Complete pipeline execution

### Test Fixtures

**Location**: `tests/fixtures/`  
**Purpose**: Provide test data and sample files  
**Contents**:
- Sample TLA+ specifications
- Test configuration files
- Example comments
- Test metadata

## Test Coverage

### Measuring Coverage

```bash
# Run tests with coverage
pytest tests/ --cov=steps --cov=pipelines

# Generate detailed HTML report
pytest tests/ --cov=steps --cov=pipelines --cov-report=html

# Show missing lines
pytest tests/ --cov=steps --cov=pipelines --cov-report=term-missing
```

### Coverage Goals

- **Minimum**: 70% overall coverage
- **Target**: 85% overall coverage
- **Critical paths**: 95%+ coverage
  - Pipeline steps
  - TLA+ tool integration
  - Error handling

## Continuous Integration

### Pre-commit Checks

Before committing, run:

```bash
# Run all tests
pytest tests/

# Run fast tests only
pytest tests/ -m "not slow"

# Check code style (if configured)
flake8 steps/ pipelines/
black --check steps/ pipelines/
```

### CI Pipeline

The project uses automated testing in CI:

1. **Unit tests** - Run on every commit
2. **Integration tests** - Run on pull requests
3. **Coverage reports** - Generated for main branch
4. **Code quality** - Linting and style checks

## Best Practices

### DO

✅ **Write descriptive test names**
```python
def test_sany_parser_handles_invalid_syntax():
    """Clear what's being tested"""
```

✅ **Use fixtures for common setup**
```python
def test_with_fixture(sample_tla_spec):
    """Reuse test data"""
```

✅ **Test error conditions**
```python
def test_handles_missing_file():
    """Test error paths"""
```

✅ **Mock external dependencies**
```python
@patch('steps.parse_step.subprocess.run')
def test_with_mock(mock_subprocess):
    """Isolate from external systems"""
```

✅ **Keep tests independent**
```python
# Each test should run independently
def test_feature_a(): pass
def test_feature_b(): pass
```

### DON'T

❌ **Don't test implementation details**
```python
# Bad - tests internal structure
def test_internal_variable_name():
    assert obj._internal_var == "value"
```

❌ **Don't use sleep() in tests**
```python
# Bad - makes tests slow
import time
time.sleep(5)
```

❌ **Don't write tests that depend on order**
```python
# Bad - tests should be independent
def test_step_1(): pass  # Sets global state
def test_step_2(): pass  # Depends on step_1
```

❌ **Don't skip error checking**
```python
# Bad - no assertions
def test_function():
    function_call()  # Missing assert
```

❌ **Don't test external services directly**
```python
# Bad - don't call real APIs in tests
def test_openai_api():
    response = openai.ChatCompletion.create(...)
```

## Debugging Tests

### Running Tests in Debug Mode

```bash
# Run with Python debugger
pytest tests/ --pdb

# Drop into debugger on failure
pytest tests/ -x --pdb

# Show local variables on failure
pytest tests/ -l

# Increase verbosity
pytest tests/ -vv
```

### Using Print Statements

```bash
# Show print output
pytest tests/ -s

# Capture disabled for specific test
pytest tests/unit/test_parse_step.py::test_name -s
```

### Inspecting Fixtures

```bash
# Show available fixtures
pytest --fixtures

# Show fixture setup
pytest tests/ -v --setup-show
```

## Adding New Tests

### Checklist for New Tests

1. ✅ Choose appropriate test category (unit/integration)
2. ✅ Create test file following naming convention
3. ✅ Import necessary modules and fixtures
4. ✅ Write test with descriptive name
5. ✅ Add docstring explaining test purpose
6. ✅ Use appropriate mocking for external dependencies
7. ✅ Include assertions to verify behavior
8. ✅ Test both success and error cases
9. ✅ Run test locally to verify it passes
10. ✅ Check test coverage for new code

### Example: Adding a Test for New Step

```python
# tests/unit/test_new_step.py
"""
Unit tests for new_step.py
"""
import pytest
from unittest.mock import Mock, patch


class TestNewStep:
    """Tests for the new pipeline step."""

    @patch('steps.new_step.external_dependency')
    @patch('steps.new_step.mlflow')
    def test_successful_execution(self, mock_mlflow, mock_dep):
        """Test successful execution of new step."""
        from steps.new_step import new_step_function
        
        # Setup mocks
        mock_dep.return_value = "expected_result"
        
        # Execute
        result = new_step_function({"input": "data"})
        
        # Verify
        assert result is not None
        assert mock_dep.called
        
    def test_error_handling(self):
        """Test error handling in new step."""
        from steps.new_step import new_step_function
        
        # Should handle errors gracefully
        result = new_step_function({})
        assert result is not None
```

## Troubleshooting

### Common Issues

**Issue**: Tests can't find modules
```bash
# Solution: Ensure you're in venv and installed packages
source venv/bin/activate
pip install -e .
```

**Issue**: TLA+ tools not found
```bash
# Solution: Set TLA_TOOLS_DIR in .env
export TLA_TOOLS_DIR=/opt/tla
```

**Issue**: MLflow errors
```bash
# Solution: Set correct tracking URI
export MLFLOW_TRACKING_URI=file:///path/to/mlruns
```

**Issue**: Slow tests
```bash
# Solution: Run only fast tests
pytest tests/ -m "not slow"
```

## Resources

- [Pytest Documentation](https://docs.pytest.org/)
- [Python Mock Documentation](https://docs.python.org/3/library/unittest.mock.html)
- [Testing Best Practices](https://docs.python-guide.org/writing/tests/)
- [FormaLLM README](README.md)

## Contributing

When contributing tests:

1. Follow the existing test structure
2. Add tests for new features
3. Ensure tests pass locally
4. Update this document if needed
5. Include tests in pull requests

For questions or issues, open a GitHub issue or discussion.
