module

public import Thesis.Upstream.InteriorPoissonRepresentative
public import Thesis.Upstream.PoissonRegularitySuccessor

/-! Interior linear Poisson regularity on the original weak tensor graph. -/

public section

namespace Thesis

/-- The bounded-forcing representative and the local higher-derivative
estimate in the two forms used by the semilinear bootstrap. -/
theorem interiorPoissonRegularity : InteriorPoissonRegularity where
  continuousRepresentative hΩ hu hEq := hEq.exists_continuousRepresentative_of_bounded hΩ hu
  contDiffOn_succ := interiorPoissonRegularity_contDiffOn_succ

end Thesis
