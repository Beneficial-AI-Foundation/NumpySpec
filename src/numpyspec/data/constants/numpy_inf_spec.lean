def numpy_inf (_ : Unit) : {x : Float // x = (1 : Float) / 0} :=
  ⟨(1 : Float) / 0, rfl⟩