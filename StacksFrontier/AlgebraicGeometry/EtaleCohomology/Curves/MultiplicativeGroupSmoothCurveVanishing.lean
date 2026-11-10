module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageMultiplicative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Higher vanishing for the multiplicative group on a smooth curve

Let `X` be a smooth curve over an algebraically closed field `k`, with generic point
`j : η = Spec k(X) ⟶ X`. This file proves, at exactly these hypotheses,

* `H^p_étale(X, j_* 𝐆_{m,η}) = 0` for every `p ≥ 1` (Stacks 03RK), and
* `H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2` (Stacks 03RM).

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_smoothCurve`:
  **Stacks 03RK**.
* `subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`:
  **Stacks 03RM**.

## Implementation notes

Both are the general statements of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing` with
their inputs supplied:

* Stacks 03RJ, `R^q j_* 𝐆_{m,η} = 0` for `q ≥ 1`, is
  `Stacks.EtaleCohomology.`
  `isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one`,
  whose transcendence-degree premise at the function field of a curve is
  `AlgebraicGeometry.trdeg_functionField_eq_one`;
* Stacks 03RG, `H^q_étale(η, 𝐆_m) = 0` for `q ≥ 1`, is
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_functionField`;
* Stacks 03RI, the short exact sequence
  `0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} i_{x,*} 𝐙 → 0`, is
  `Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`;
* Stacks 03RL, the vanishing of the positive-degree cohomology of `⨁_{x ∈ X_0} i_{x,*} 𝐙`, is
  used inside `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve`.

The proof of Stacks 03RM is then the long exact sequence of the sequence of Stacks 03RI: the
segment `H^{q-1}(X, ⨁_x i_{x,*} 𝐙) → H^q(X, 𝐆_m) → H^q(X, j_* 𝐆_{m,η})` has both outer groups
zero for `q ≥ 2`.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ)
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Stacks Project, Tag 03RK.** Let `X` be a smooth curve over an algebraically closed field
`k`, let `η = Spec k(X)` be its generic point and `j : η ⟶ X` the inclusion. Then

`H^p_étale(X, j_* 𝐆_{m,η}) = 0` for every `p ≥ 1`.

This is `Stacks.EtaleCohomology.subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf`,
the collapse of the Leray spectral sequence to its edge isomorphism, with Stacks 03RJ and
Stacks 03RG proved. -/
@[stacks 03RK]
theorem subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_smoothCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [Smooth g] (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((genericPointDirectImage.{u, u + 1} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) p) :=
  subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf g p hp

/-- **Stacks Project, Tag 03RM.** Let `X` be a smooth curve over an algebraically closed field
`k`. Then

`H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2`.

The long exact sequence of the fundamental exact sequence of Stacks 03RI,
`Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`, places `H^q(X, 𝐆_m)` between
`H^{q-1}(X, ⨁_{x ∈ X_0} i_{x,*} 𝐙)`, zero by Stacks 03RL, and `H^q(X, j_* 𝐆_{m,η})`, zero by
Stacks 03RK; the latter rests on Stacks 03RJ and Stacks 03RG, supplied here. -/
@[stacks 03RM]
theorem subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) q) := by
  let := functionFieldAlgebra k g
  exact subsingleton_sheafH_multiplicativeSheaf_smoothCurve g
    (divisorSequenceSecondMapOfCurve.{u, u + 1} g)
    (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1} g)
    (shortExact_divisorSequenceOfCurve.{u} g)
    (isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one k
      (trdeg_functionField_eq_one k g))
    (fun q hq ↦ subsingleton_sheafH_multiplicativeSheaf_spec_functionField k g q hq) q hq

end Stacks.EtaleCohomology

end
