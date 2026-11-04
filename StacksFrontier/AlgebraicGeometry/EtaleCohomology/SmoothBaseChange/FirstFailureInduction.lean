module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.DegreeZero
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The induction on the degree in the second proof of smooth base change

The second proof of the smooth base change theorem (Stacks, Theorem 0EYU) proves `BC(f, n, q)`
by induction on `q`. The case `q = 0` is Stacks 0EYS. If `BC(f, n, q)` holds and `BC(f, n, q + 1)`
fails, Stacks 0F08 produces a diagram over an affine integral normal scheme with algebraically
closed function field and an algebraically closed field over it, in which `R^{q+1} h_*(ℤ/dℤ)`
does not vanish for some `d ∣ n`. So it suffices to show that no such diagram exists.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.baseChangeAllDegrees_of_not_normalFailureDiagram` —
  for a smooth `f`, `BC(f, n, q)` holds in every degree as soon as no normalized counterexample
  of Stacks 0F08 exists in positive degree.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **The base case `BC(f, n, 0)`** for a smooth morphism: every base change of `f` is smooth,
hence flat, locally of finite presentation and with geometrically reduced fibres, and Stacks 0EYS
applies. -/
theorem baseChangeHolds_zero_of_smooth (h0EYS : FlatReducedFibresBaseChange.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (n : ℤ) : BaseChangeHolds f n 0 := by
  intro S' X' T Y s p f' hp g h e sq _ _ F _ q hq
  obtain rfl : q = 0 := by omega
  have : Smooth f' := MorphismProperty.of_isPullback hp ‹Smooth f›
  have : GeometricallyReduced f' := geometricallyReduced_of_smooth f'
  exact isIso_higherBaseChangeMapAb_zero_of_flat h0EYS f' h e g sq F

/-- **The induction of the second proof of smooth base change.** For a smooth `f : X ⟶ S` and an
integer `n`, if there is no normalized counterexample of Stacks 0F08 in any positive degree, then
`BC(f, n, q)` holds in every degree: the base case is Stacks 0EYS, and a first failure in degree
`q + 1` would give a normalized counterexample in degree `q + 1` by Stacks 0F08. -/
theorem baseChangeAllDegrees_of_not_normalFailureDiagram (h0EYS : FlatReducedFibresBaseChange.{u})
    (h0F08 : FirstFailureNormalization.{u}) {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (n : ℤ)
    (hvan : ∀ r : ℕ, 1 ≤ r → ¬ FirstFailureDiagram.NormalFailureDiagram f n r) :
    BaseChangeAllDegrees f n := by
  have hnat : ∀ q : ℕ, BaseChangeHolds f n (q : ℤ) := by
    intro q
    induction q with
    | zero => exact baseChangeHolds_zero_of_smooth h0EYS f n
    | succ q ih =>
      by_contra hq
      refine hvan (q + 1) (by omega) (h0F08 f n q ih ?_)
      rwa [Nat.cast_succ] at hq
  intro q₀
  rcases lt_or_ge q₀ 0 with hneg | hnonneg
  · intro S' X' T Y s p f' hp g h e sq _ _ F _ q hq
    omega
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    exact hnat m

end Stacks.EtaleCohomology.SmoothBaseChange

end
