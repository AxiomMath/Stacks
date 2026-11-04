module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomial

/-!
# The Hilbert polynomial of a curve in projective space

Let `φ : X ⟶ ℙⁿ_k` be a closed immersion over a field `k`. The Hilbert polynomial of the coherent
sheaf `φ_* 𝒪_X` on `ℙⁿ_k` is computed on `X`: by the projection formula and the invariance of
cohomology under pushforward along a closed immersion,

`χ(ℙⁿ_k, (φ_* 𝒪_X)(d)) = χ(X, φ^* 𝒪(d))`.

When `X` is a proper scheme of dimension at most one this is `d · deg(φ^* 𝒪(1)) + χ(X, 𝒪_X)`,
the degree being additive in the tensor product ([Stacks, Tag 0AYX]) and `φ^* 𝒪(a + b) ≅
φ^* 𝒪(a) ⊗ φ^* 𝒪(b)`.

## Main results

* `AlgebraicGeometry.hilbertPolynomial_pushforward_unit_eq_finsum`: the Hilbert polynomial of
  `φ_* 𝒪_X` is the Euler characteristic of `φ^* 𝒪(d)` on `X`.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_twistOver`:
  `deg(φ^* 𝒪(d)) = d · deg(φ^* 𝒪(1))`.

The resulting Hilbert polynomial of a curve, `d · deg(φ^* 𝒪(1)) + χ(X, 𝒪_X)`, is
`AlgebraicGeometry.hilbertPolynomial_pushforward_unit_eq` in `./IdealSheafRegularity.lean`.

## References

* [Stacks Project, Tag 08AD](https://stacks.math.columbia.edu/tag/08AD)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistOverMulIso twistZeroIsoUnit)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion φ]

/-- **The Hilbert polynomial of `φ_* 𝒪_X` is the Euler characteristic of `φ^* 𝒪(d)` on `X`.**
`(φ_* 𝒪_X)(d) = φ_* 𝒪_X ⊗ 𝒪(d) ≅ φ_*(𝒪_X ⊗ φ^* 𝒪(d)) ≅ φ_*(φ^* 𝒪(d))` by the projection formula
at a closed immersion, and cohomology does not change under pushforward along a closed
immersion. -/
theorem hilbertPolynomial_pushforward_unit_eq_finsum
    [((Scheme.Modules.pushforward φ).obj (SheafOfModules.unit X.ringCatSheaf)).IsCoherent]
    (d : ℤ) :
    hilbertPolynomial k n ((Scheme.Modules.pushforward φ).obj
        (SheafOfModules.unit X.ringCatSheaf)) d =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k
        (φ ≫ (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)))
        ((Scheme.Modules.pullback φ).obj (twistOver n (Spec (.of k)) d)) i) : ℤ) := by
  unfold hilbertPolynomial
  refine finsum_congr fun i => ?_
  congr 2
  refine (finrank_cohomologyOverField_eq_of_iso k _
    (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso φ
      (SheafOfModules.unit X.ringCatSheaf) (twistOver n (Spec (.of k)) d)) i).trans ?_
  refine (finrank_cohomologyOverField_pushforward_of_isClosedImmersion k φ _ _ i).symm.trans ?_
  exact finrank_cohomologyOverField_eq_of_iso k _
    (SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace _) i

/-- **`deg(φ^* 𝒪(d)) = d · deg(φ^* 𝒪(1))`** for a morphism `φ` from a proper scheme of dimension
at most one over `k` to `ℙⁿ_k`. The degree is additive in the tensor product of invertible
modules ([Stacks, Tag 0AYX]), `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on `ℙⁿ_k` ([Stacks, Tag 01MU]), pullback
commutes with tensor products ([Stacks, Tag 01CD]) and `𝒪(0) ≅ 𝒪`; so `d ↦ deg(φ^* 𝒪(d))` is
additive. -/
theorem invertibleCurveDegree_pullback_twistOver {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [IsProper f] (hdim : topologicalKrullDim Y ≤ 1) (ψ : Y ⟶ projectiveSpaceOverRing n (.of k))
    (d : ℤ) :
    invertibleCurveDegree k f hdim
        ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) d)) =
      d * invertibleCurveDegree k f hdim
        ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) 1)) := by
  let D : ℤ → ℤ := fun a =>
    invertibleCurveDegree k f hdim ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) a))
  have hadd : ∀ a b : ℤ, D (a + b) = D a + D b := by
    intro a b
    have e : (Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) (a + b)) ≅
        Stacks.RelativeVeryAmple.tensorModules Y
          ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) a))
          ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) b)) :=
      (Scheme.Modules.pullback ψ).mapIso (twistOverMulIso n (Spec (.of k)) a b).symm ≪≫
        Stacks.RelativeVeryAmple.pullbackTensorModulesIso ψ _ _
    have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Stacks.RelativeVeryAmple.tensorModules Y
          ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) a))
          ((Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) b))) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
    exact (invertibleCurveDegree_eq_of_iso k f hdim e).trans
      (invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim _ _
        inferInstance inferInstance inferInstance)
  have h0 : D 0 = 0 := by
    have e : (Scheme.Modules.pullback ψ).obj (twistOver n (Spec (.of k)) 0) ≅
        SheafOfModules.unit Y.ringCatSheaf :=
      (Scheme.Modules.pullback ψ).mapIso (twistZeroIsoUnit n (Spec (.of k))) ≪≫
        Scheme.Modules.pullbackUnitIso ψ
    exact (invertibleCurveDegree_eq_of_iso k f hdim e).trans
      (invertibleCurveDegree_unit_eq_zero k f hdim)
  show D d = d * D 1
  induction d using Int.induction_on with
  | zero => rw [h0, zero_mul]
  | succ m ih => rw [hadd, ih, add_mul, one_mul]
  | pred m ih =>
    have h := hadd (-(m : ℤ) - 1) 1
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at h
    linarith

end AlgebraicGeometry

end
