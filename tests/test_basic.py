"""Basic tests for numpyspec package."""

def test_package_import():
    """Test that numpyspec package can be imported."""
    import numpyspec
    assert hasattr(numpyspec, 'main')

def test_hf_utils_import():
    """Test that hf_utils module can be imported."""
    from numpyspec.hf_utils import load_model, generate
    assert callable(load_model)
    assert callable(generate)