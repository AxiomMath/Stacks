module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ProperOverLocalBaseCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension

/-!
# The dualizing module of a proper scheme over a local base

Let `S = Spec(A)` with `A` a Noetherian local ring, let `ω_S^•` correspond to a normalized
dualizing complex `ω_A^•`, let `f : X ⟶ S` be proper and `ω_X^• = f^!ω_S^•`. Then the coherent
sheaf `ω_X = H^{-dim X}(ω_X^•)` is a dualizing module in the sense of [Stacks, Section 48.22]:
`ω_X^•` is a dualizing complex and `-dim X` is the least degree in which it has nonzero
cohomology. This is [Stacks, Tag 0AWI].

## Main results

* `Stacks.Duality.not_isZero_homology_neg_of_hasNormalizedStalks` — a complex with the local
  description `Stacks.Duality.HasNormalizedStalks` on a nonempty scheme of dimension `n` has
  nonzero cohomology in degree `-n`.
* `Stacks.Duality.isDualizingModuleOf_relativeDualizingModule` — [Stacks, Tag 0AWI].

## References

* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWH](https://stacks.math.columbia.edu/tag/0AWH)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

/-- **The cohomology in degree minus the dimension does not vanish.** If `K` has the local
description `Stacks.Duality.HasNormalizedStalks` on a nonempty Noetherian scheme of dimension `n`,
then `H^{-n}(K) ≠ 0`: a point `ξ` whose closure has dimension `n` has `dim 𝒪_{X,ξ} = 0`, so it lies
in the support of `H^{-n}(K)`. -/
theorem not_isZero_homology_neg_of_hasNormalizedStalks {X : Scheme.{u}} [IsNoetherian X]
    [Nonempty X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules} {n : ℕ}
    (hloc : HasNormalizedStalks K n) :
    ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj K) := by
  have hk : Order.krullDim X = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [← Stacks.ResolutionOfSurfaces.topologicalKrullDim_eq_krullDim, hloc.dim_eq]
    rfl
  rw [Order.krullDim_eq_iSup_height_of_nonempty, WithBot.coe_inj] at hk
  obtain ⟨ξ, hξ⟩ := ENat.exists_eq_iSup_of_lt_top (f := fun a : X => Order.height a)
    (by rw [hk]; exact ENat.natCast_lt_top n)
  rw [hk] at hξ
  have hcl : topologicalKrullDim (closure ({ξ} : Set X)) = (n : WithBot ℕ∞) := by
    rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height, hξ]
    rfl
  obtain ⟨L, e, h, -, he, hh, hle, -⟩ := hloc.exists_normalized ξ
  have hen : e = n := by
    rw [hcl] at he
    exact_mod_cast he.symm
  have hmem : ξ ∈ _root_.SheafOfModules.supp
      ((DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj K) := by
    rw [supp_homology_neg_eq_setOf hloc]
    change topologicalKrullDim (closure ({ξ} : Set X)) + ringKrullDim (X.presheaf.stalk ξ) = _
    have h0 : h = 0 := by omega
    rw [hcl, hh, h0]
    simp
  intro hz
  have hnt := (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ ξ).mp hmem
  have hsub : Subsingleton (moduleStalkAtPoint
      ((DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj K) ξ) :=
    (stalkLinearEquivSchemeStalk _ ξ).toEquiv.subsingleton_congr.mpr
      (ModuleCat.isZero_iff_subsingleton.mp ((schemeStalkModuleFunctor ξ).map_isZero hz))
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt

open ChartCompactification ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] [IsNoetherianRing Γ(S, ⊤)]
  [IsLocalRing Γ(S, ⊤)]

/-- **Stacks Project, Tag 0AWI (Example 48.22.1).** Let `S` be affine with
`A = Γ(S, ⊤)` a Noetherian local ring, `ω_S^•` modelled on `S` by a normalized dualizing complex
`ω_A^•`, `f : X ⟶ S` proper and `ω_X^• = f^!ω_S^• = a(ω_S^•)`. Then `ω_X = H^{-dim X}(ω_X^•)` is a
coherent sheaf, and, `X` being nonempty, a dualizing module: `ω_X^•` is a dualizing complex and
`-dim X` is the least degree in which it has nonzero cohomology. -/
@[stacks 0AWI]
theorem isDualizingModuleOf_relativeDualizingModule
    (f : X ⟶ S) [IsProper f] (ωS : quasiCoherentDerivedCategory S)
    (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ωS).IsCoherent ∧
      (Nonempty X → IsDualizingModuleOf
        (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS)
        (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          ωS).obj (-(natDim X : ℤ))) := by
  have := isNoetherian_of_isAffine_of_isNoetherianRing (S := S)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsProper (ftsHomToBase f).left := ‹IsProper f›
  have hdual : IsDualizingComplex ωS.obj := isDualizingComplex_of_isTildeModelOn_top hω.1 hmodel
  have hcharts := UpperShriekCharts.hasTopCharts f
    (upperShriekCharts (ftsHomToBase f) (properCompactification (ftsHomToBase f)) ωS
      (isBoundedBelow_of_isDualizingComplex _ hdual)) hmodel
  have hcharts' : HasTopCharts f ω (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj := fun U hU p =>
    isTildeModelOnAnyModel_of_iso ((ObjectProperty.ι _).mapIso
      ((upperShriekProperIso (ftsHomToBase f)).app ωS)) (hcharts U hU p)
  have hK := isDualizingComplex_of_hasTopCharts f hω.1 hcharts'
  have h0 := associatedShiftFunction_eq_zero_of_hasTopCharts f hω hcharts'
  refine ⟨isCoherent_homology_of_isDualizingComplex hK _, fun hX => ⟨hK, ?_, ?_, rfl⟩⟩
  · exact not_isZero_homology_neg_of_hasNormalizedStalks (hasNormalizedStalks_natDim hK h0).2
  · intro i hi
    by_contra hz
    have := (mem_Icc_of_not_isZero_homology_of_associatedShiftFunction_eq_zero hK h0 i hz).1
    omega

end Stacks.Duality

end
