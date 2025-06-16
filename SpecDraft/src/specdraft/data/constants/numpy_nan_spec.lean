def numpy_nan (_ : Unit) : {x : Float // x = (0 : Float) / 0} :=
  ⟨(0 : Float) / 0, rfl⟩