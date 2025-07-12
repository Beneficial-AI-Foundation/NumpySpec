/-!
{
  "name": "numpy.testing.break_cycles",
  "category": "Testing Utilities",
  "description": "Break reference cycles",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.break_cycles.html",
  "doc": "Break reference cycles.\n\nDo a full garbage collection and assure that all temporary objects are freed. It is not advisable to use this in unit tests because it is not reliable. It only frees tracked objects which are those that are part of a Python object's reference cycle detector. NumPy dtype objects are not tracked.",
  "code": "def break_cycles():\n    \"\"\"\n    Break reference cycles.\n\n    Calling this function a few times may break some reference cycles. We use\n    it on teardown with the \`assert_no_gc_cycles\` context manager.\n\n    \"\"\"\n    gc.collect()\n    gc.collect()\n    gc.collect()"
}
-/

-- TODO: Implement break_cycles
