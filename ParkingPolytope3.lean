import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The dimension-three case of Hill–Luo–Trinh–Vindas-Meléndez, Conjecture 8.1.
The input is their lattice-point polynomial (Example 5.12). -/

noncomputable section

namespace ParkingPolytope3

def latticePolynomial (a b c : ℝ) : ℝ :=
  a^3 + 3*a^2*b + 3*a^2*c + 3*a*b^2 + 6*a*b*c + (3/2)*a*c^2 +
    (5/6)*b^3 + 2*b^2*c + b*c^2 + (1/6)*c^3 -
    (3/2)*a*c - (1/2)*b^2 - 2*b*c - (1/2)*c^2 - b/3 + c/3

/-- The first magic coefficient at shifted parameters `(x+1,y+1,z+1)`. -/
def magic1 (x y z : ℝ) : ℝ := 3*x + (8/3)*y + (11/6)*z + 3/2

def magic2 (x y z : ℝ) : ℝ :=
  3*x^2 + 6*x*y + (9/2)*x*z + (9/2)*x + (5/2)*y^2 + 4*y*z +
    (11/3)*y + z^2 + (7/3)*z + 3/2

def magic3 (x y z : ℝ) : ℝ :=
  x^3 + 3*x^2*y + 3*x^2*z + 3*x^2 + 3*x*y^2 + 6*x*y*z + 6*x*y +
    (3/2)*x*z^2 + (9/2)*x*z + 3*x + (5/6)*y^3 + 2*y^2*z + 2*y^2 +
    y*z^2 + 2*y*z + (7/6)*y + (1/6)*z^3 + (1/2)*z^2 + (1/3)*z

theorem magic_expansion (x y z t : ℝ) :
    latticePolynomial (1+t*x) (t*(y+1)) (t*(z+1)) =
      (t+1)^3 + magic1 x y z*t*(t+1)^2 + magic2 x y z*t^2*(t+1) + magic3 x y z*t^3 := by
  unfold latticePolynomial magic1 magic2 magic3
  ring

theorem magic_nonneg (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ magic1 x y z ∧ 0 ≤ magic2 x y z ∧ 0 ≤ magic3 x y z := by
  unfold magic1 magic2 magic3
  constructor
  · positivity
  constructor <;> positivity

/-- Every positive length-three parameter triple has a nonnegative expansion
in the basis used in Conjecture 8.1. -/
theorem dimension_three (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ ∀ t : ℝ,
      latticePolynomial (1+t*(a-1)) (t*b) (t*c) =
        (t+1)^3 + u*t*(t+1)^2 + v*t^2*(t+1) + w*t^3 := by
  obtain ⟨hu, hv, hw⟩ := magic_nonneg (a-1) (b-1) (c-1) (sub_nonneg.mpr ha)
    (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)
  refine ⟨_, _, _, hu, hv, hw, ?_⟩
  intro t
  simpa only [sub_add_cancel] using magic_expansion (a-1) (b-1) (c-1) t

#print axioms dimension_three

end ParkingPolytope3
