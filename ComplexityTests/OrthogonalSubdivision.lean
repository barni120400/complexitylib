import Complexity.Foundations.Geometry.Orthogonal.Subdivision

/-! Regression instances for signed unit subdivision and continuous support preservation. -/

open Cslib.Orthogonal

private def signedRoute : Route := [(-2, 1), (1, 1), (1, -1)]

private theorem signedRoute_orthogonal : IsOrthogonal signedRoute := by
  norm_num [signedRoute, IsOrthogonal, AxisAligned, List.consecutivePairs, Prod.mk.injEq]

example : subdivide [] = [] := rfl

example : subdivide [(3, -4)] = [(3, -4)] := rfl

example : subdivide signedRoute =
    [(-2, 1), (-1, 1), (0, 1), (1, 1), (1, 0), (1, -1)] := by decide

example : segmentWalk (1, -1) (1, 2) = [(1, -1), (1, 0), (1, 1), (1, 2)] := by decide

example : segmentWalk (2, 0) (-1, 0) = [(2, 0), (1, 0), (0, 0), (-1, 0)] := by decide

example : (subdivide signedRoute).length = 6 := by decide

example : wireLength (subdivide signedRoute) = 5 := by decide

example : (subdivide signedRoute).head? = some (-2, 1) := by decide

example : (subdivide signedRoute).getLast? = some (1, -1) := by decide

example : support (subdivide signedRoute) = support signedRoute :=
  support_subdivide signedRoute_orthogonal

example : ∀ e ∈ (subdivide signedRoute).consecutivePairs, length e.1 e.2 = 1 :=
  fun _ he => subdivide_unit signedRoute_orthogonal he

example : IsOrthogonal (subdivide signedRoute) := subdivide_orthogonal signedRoute_orthogonal
