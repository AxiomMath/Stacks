module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjOfPolynomialOneVariable
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.NoetherianModelClauses

/-!
# Higher direct images along a projective morphism to an affine Noetherian base are coherent

Let `R` be a Noetherian ring and let `g : Y ⟶ Spec R` be H-projective, that is, let there be a
closed immersion `i : Y ⟶ ℙⁿ_{Spec R}` over `Spec R` ([Stacks, Tag 01W8]). Then `R^q g_* 𝒢` is
coherent for every coherent `𝒢` and every `q`. This is the affine-base projective case of
[Stacks, Tag 02O4].

## Main results

* `Stacks.ProjCoherentCohomologyFinite.projCompare_inv_comp_projToSpecCoeff`: the comparison of
  the two models of `ℙⁿ_R` carries the `Proj`-model structure morphism to the base-change-model
  one.
* `Stacks.ProjCoherentCohomologyFinite.isIso_projToSpecCoeff_zero`: **`ℙ⁰_R ⟶ Spec R` is an
  isomorphism**, so `ℙ⁰_R` is affine.
* `Stacks.ProjCoherentCohomologyFinite.isCoherent_rightDerived_of_isProjectiveMorphism`:
  **the affine-base projective case of [Stacks, Tag 02O4]**, for every `n ≥ 0`.

## Implementation notes

The closed immersion into the base-change model of `ℙⁿ_R` is transported to the `Proj` model
along `Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`, and the relative Leray step
`Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isCoherent_rightDerived_pushforward_iff`
replaces `R^q (i ≫ f)_* 𝒢` by `R^q f_* (i_* 𝒢)`, with `i_* 𝒢` coherent by [Stacks, Tag 087T].
For `n = 0` the structure morphism `ℙ⁰_R ⟶ Spec R` is an isomorphism ([Stacks, Tag 01MI]), so the
higher direct images vanish ([Stacks, Tag 01XC]).

`projCompare_inv_comp_projToSpecCoeff` is proved in term mode: the comparison occurs under
`CategoryTheory.asIso`, whose `IsIso` argument depends on it, so `rw` with
`Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_fst` fails the motive check.

## References

* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01MI](https://stacks.math.columbia.edu/tag/01MI)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjCoherentCohomologyFinite

variable (R : Type u) [CommRing R]

/-! ### The two models, and the degenerate degree -/

/-- **The comparison of the two models of `ℙⁿ_R` is over `Spec R`.** Read backwards: the inverse
of `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare` carries the structure morphism of the
`Proj` model to that of the base-change model. -/
theorem projCompare_inv_comp_projToSpecCoeff (n : ℕ) :
    (asIso (projCompare R n)).inv ≫ projToSpecCoeff R n
      = projectiveSpaceOver n (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R) :=
  Eq.trans
    (congrArg (fun m => (asIso (projCompare R n)).inv ≫ m) (projCompare_fst R n).symm)
    ((asIso (projCompare R n)).inv_hom_id_assoc _)

/-- **`ℙ⁰_R ⟶ Spec R` is an isomorphism**, so projective `0`-space over `R` is affine. -/
theorem isIso_projToSpecCoeff_zero : IsIso (projToSpecCoeff R 0) := by
  have hhom : CommRingCat.ofHom ((GradedRing.projZeroRingHom'
        (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)).comp
      (algebraMap R (MvPolynomial (Fin (0 + 1)) R)))
      = Stacks.ProjectiveCohomology.polyDegreeZeroHom R 0 := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
    change ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)
        (MvPolynomial.C r)) 0 : MvPolynomial (Fin (0 + 1)) R) = MvPolynomial.C r
    exact DirectSum.decompose_of_mem_same _
      ((MvPolynomial.mem_homogeneousSubmodule 0 _).2 (MvPolynomial.isHomogeneous_C _ r))
  have h : projToSpecCoeff R 0 = Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) ≫
      Spec.map (Stacks.ProjectiveCohomology.polyDegreeZeroHom R 0) :=
    congrArg (fun φ => Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) ≫ Spec.map φ) hhom
  rw [h]
  have := AlgebraicGeometry.ProjectiveSpace.isIso_toSpecZero_oneVariable R
  infer_instance

/-! ### The affine-base projective case of [Stacks, Tag 02O4] -/

/-- **Higher direct images along a projective morphism to an affine Noetherian base are
coherent.** For `R` Noetherian and `g : Y ⟶ Spec R` H-projective, `R^q g_* 𝒢` is coherent for
every coherent `𝒢` and every `q`. -/
theorem isCoherent_rightDerived_of_isProjectiveMorphism [IsNoetherianRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : IsProjectiveMorphism g)
    (G : Y.Modules) (hG : G.IsCoherent) (q : ℕ) :
    (((Scheme.Modules.pushforward g).rightDerived q).obj G).IsCoherent := by
  obtain ⟨n, i, hi, hcomp⟩ := hg
  have hj : (i ≫ (asIso (projCompare R n)).inv) ≫ projToSpecCoeff R n = g := by
    rw [Category.assoc, projCompare_inv_comp_projToSpecCoeff R n]
    exact hcomp
  rw [← hj]
  refine (isCoherent_rightDerived_pushforward_iff
    (i ≫ (asIso (projCompare R n)).inv) (projToSpecCoeff R n) G q).1 ?_
  have hLN : IsLocallyNoetherian (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :=
    Stacks.AlgebraicGeometry.Proj.isLocallyNoetherian_proj _
  have hjG : ((Scheme.Modules.pushforward
      (i ≫ (asIso (projCompare R n)).inv)).obj G).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion _ G
  cases n with
  | succ m => exact forall_isCoherent_rightDerived_projectiveSpace R m _ hjG q
  | zero =>
    have := isIso_projToSpecCoeff_zero R
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · have hc : ((Scheme.Modules.pushforward (projToSpecCoeff R 0)).obj
          ((Scheme.Modules.pushforward (i ≫ (asIso (projCompare R 0)).inv)).obj G)).IsCoherent :=
        isCoherent_pushforward_of_isClosedImmersion _ _
      exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
        (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroObjIso
          (projToSpecCoeff R 0) _)
    · have hqc : ((Scheme.Modules.pushforward
          (i ≫ (asIso (projCompare R 0)).inv)).obj G).IsQuasicoherent :=
        isQuasicoherent_of_isCoherent _
      exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
        (Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward
          (projToSpecCoeff R 0) _ q hq)

end Stacks.ProjCoherentCohomologyFinite

end
