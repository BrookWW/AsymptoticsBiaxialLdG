module

public import Thesis.MeasureGeometry.PlanarCoareaGluing
public import Thesis.MeasureGeometry.PlanarRegularCoarea

/-! Weighted scalar C¹ coarea on the Euclidean plane. -/

public section

namespace Thesis

/-- The actual Hausdorff lengths of the fibers satisfy the scalar coarea
formula with every nonnegative measurable weight on the level value. -/
theorem planarScalarCoarea : External.PlanarScalarCoarea :=
  planarScalarCoarea_of_local_regular_charts
    (fun hU f hf _ hx hD => exists_regular_planar_coarea_chart hU f hf hx hD)

end Thesis
