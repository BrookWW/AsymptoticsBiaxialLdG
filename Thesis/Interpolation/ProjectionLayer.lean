module

public import Thesis.Interpolation.ProjectionLayerAssembly
public import Thesis.MeasureGeometry.PlanarBoundaryLowerBound
public import Thesis.MeasureGeometry.PlanarSpectralCoarea

/-! The penalized projection layer with its independent analytic inputs. -/

public section

namespace Thesis

/-- The projection layer at the source scale, including the actual inner
vacuum trace and all three energy and mismatch estimates. -/
theorem hasPenalizedProjectionLayer (a : BulkCoefficients)
    (hCoarea : External.PlanarScalarCoarea)
    (hAngle : External.SquareBoundaryAngularSobolev) (hArc : External.SquareBoundaryAngularMeasure)
    (hPull : External.UnitSquareDiskSobolevPullback) (hPush : External.UnitSquareDiskSobolevPushforward)
    (hCircular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2)) :
    HasPenalizedProjectionLayer a :=
  hasPenalizedProjectionLayer_of_planarLogarithmicBound a hAngle hArc hPull hPush hCircular hP
    (hasUnitDiskNontrivialLogLowerBound hCoarea hCircular a)

end Thesis
