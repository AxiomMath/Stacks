module

public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Unconditional
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# Component degrees of a module bounded below on proper subcurves

Let `X` be a proper reduced scheme of dimension one over a field `k` and `𝒩` an invertible
`𝒪_X`-module with `dim_k H¹(Y, 𝒪_Y) ≤ deg(𝒩|_Y)` for every proper subcurve `Y ⊊ X` — the
conclusion of [Stacks, Tag 0E3J] for the dualizing sheaf of a curve without rational tails. Then
`𝒩` has nonnegative degree on every irreducible component when `X` is reducible, and the degree
formula [Stacks, Tag 0AYW] turns this into the two consequences [Stacks, Tag 0E3K] draws in genus
`0` and `1`.

## Main results

* `AlgebraicGeometry.componentDegree_nonneg_of_subcurve_bound`: on a reducible `X`, every
  component degree of `𝒩` is nonnegative.
* `AlgebraicGeometry.irreducibleSpace_of_subcurve_bound`: if moreover `deg 𝒩 < 0`, then `X` is
  irreducible.
* `AlgebraicGeometry.isTrivial_of_subcurve_bound`: if `deg 𝒩 = 0` and `𝒩` has a nonzero global
  section, then `𝒩 ≅ 𝒪_X` ([Stacks, Tag 0E22] in the reducible case, [Stacks, Tag 0B40] in the
  integral case).

## References

* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0E3J](https://stacks.math.columbia.edu/tag/0E3J)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The subcurve bound of [Stacks, Tag 0E3J] for an invertible module `𝒩`: on every proper
reduced connected one-dimensional closed subscheme `Y ⊊ X`, `dim_k H¹(Y, 𝒪_Y) ≤ deg(𝒩|_Y)`. -/
def SubcurveBound [IsProper f] (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] : Prop :=
  ∀ (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
    (hY : topologicalKrullDim Y.subscheme = 1), Y ≠ ⊥ →
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι N hN
    (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
      (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) ≤
      invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
        ((Scheme.Modules.pullback Y.subschemeι).obj N)

/-- **On a reducible curve the subcurve bound makes every component degree nonnegative.** A
one-dimensional component `C = closure {ξ}` of a reducible `X`, with its reduced structure, is a
proper subcurve: it is integral, of dimension one, and not all of `X`. -/
theorem componentDegree_nonneg_of_subcurve_bound [IsProper f] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1]
    (hsub : SubcurveBound f N) (hred : ¬ IrreducibleSpace X) (ξ : genericPointsOne X) :
    0 ≤ componentDegree k f hdim N 1 ξ := by
  set Y := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ξ.1} : Set X), isClosed_closure⟩ : Closeds X) with hYdef
  have : IsIntegral Y.subscheme := isIntegral_reducedComponent X ξ
  have hYdim : topologicalKrullDim Y.subscheme = 1 := by
    have h : Y.subscheme ≃ₜ Set.range Y.subschemeι.base :=
      (IsPreimmersion.isEmbedding Y.subschemeι).toHomeomorph
    rw [IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph]
    have hrange : Set.range Y.subschemeι.base = closure ({ξ.1} : Set X) := by
      rw [Scheme.IdealSheafData.range_subschemeι, hYdef,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.setCongr hrange).isHomeomorph]
    exact (mem_genericPointsOne_iff.mp ξ.2).2
  have hYne : Y ≠ ⊥ := by
    intro h
    apply hred
    have hsupp : (Y.support : Set X) = Set.univ := by
      rw [h]
      rfl
    rw [hYdef, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hsupp
    have hc : closure ({ξ.1} : Set X) = Set.univ := hsupp
    refine (irreducibleSpace_def X).mpr ?_
    rw [Set.top_eq_univ, ← hc]
    exact isIrreducible_singleton.closure
  have := isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ N 1
  unfold componentDegree
  rw [← invertibleCurveDegree_eq_curveDegree]
  exact (Nat.cast_nonneg _).trans (hsub Y hYdim hYne)

/-- **A negative degree and the subcurve bound force irreducibility.** If `deg 𝒩 < 0` on a
proper reduced curve satisfying the subcurve bound, then `X` is irreducible: otherwise every
component degree is nonnegative and so is their sum, which is `deg 𝒩` by
[Stacks, Tag 0AYW]. -/
theorem irreducibleSpace_of_subcurve_bound [IsProper f] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hsub : SubcurveBound f N) (hneg : invertibleCurveDegree k f hdim N < 0) :
    IrreducibleSpace X := by
  by_contra hred
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 :=
    Stacks.ProjectiveFromSections.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule N
  have h := curveDegree_eq_finsum_componentDegree_of_isProper k f hdim N 1
  rw [← invertibleCurveDegree_eq_curveDegree] at h
  have hsum : 0 ≤ ∑ᶠ ξ : genericPointsOne X,
      (componentMultiplicity X ξ : ℤ) * componentDegree k f hdim N 1 ξ :=
    finsum_nonneg fun ξ => mul_nonneg (by positivity)
      (componentDegree_nonneg_of_subcurve_bound f hdim N hsub hred ξ)
  rw [← h] at hsum
  omega

/-- **A degree-zero module with a section, under the subcurve bound, is trivial.** Let `X` be a
proper reduced connected equidimensional scheme of dimension one over `k` and `𝒩` an invertible
module of degree `0` with a nonzero global section, satisfying the subcurve bound. Then
`𝒩 ≅ 𝒪_X`.

If `X` is irreducible it is integral and this is [Stacks, Tag 0B40] part (4). Otherwise every
component degree is nonnegative and they sum to `0` ([Stacks, Tag 0AYW]), so they all vanish, and
[Stacks, Tag 0E22] applies. -/
theorem isTrivial_of_subcurve_bound [IsProper f] [IsReduced X] [ConnectedSpace X]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1) (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hsub : SubcurveBound f N) (hdeg : invertibleCurveDegree k f hdim.le N = 0)
    (hsec : Nontrivial Γ(N, ⊤)) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.2 N := by
  by_cases hirr : IrreducibleSpace X
  · have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
    obtain ⟨σ, hσ⟩ := exists_ne (0 : Γ(N, ⊤))
    have hN' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN
    let sσ := (Stacks.NonvanishingSpelling.sectionsEquiv X N).symm σ
    have hs : sσ.eval (op ⊤) = σ :=
      (Stacks.NonvanishingSpelling.sectionsEquiv X N).apply_symm_apply σ
    exact isTrivial_of_invertibleCurveDegree_nonpos k f hdim.le N sσ (hs ▸ hσ) hdeg.le
  · have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 :=
      Stacks.ProjectiveFromSections.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule N
    have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
    have : Finite (genericPointsOne X) := (finite_genericPointsOne X).to_subtype
    let : Fintype (genericPointsOne X) := Fintype.ofFinite _
    have hsum := curveDegree_eq_finsum_componentDegree_of_isProper k f hdim.le N 1
    rw [← invertibleCurveDegree_eq_curveDegree, hdeg] at hsum
    simp only [componentMultiplicity_eq_one_of_isReduced, Nat.cast_one, one_mul,
      finsum_eq_sum_of_fintype] at hsum
    have hzero : ∀ ξ : genericPointsOne X, componentDegree k f hdim.le N 1 ξ = 0 :=
      fun ξ => (Finset.sum_eq_zero_iff_of_nonneg fun ξ _ =>
        componentDegree_nonneg_of_subcurve_bound f hdim.le N hsub hirr ξ).mp hsum.symm ξ
        (Finset.mem_univ _)
    refine (subsingleton_globalSections_or_isTrivial_of_invertibleCurveDegree_nonpos k f hequi
        hdim N ?_).resolve_left (not_subsingleton_iff_nontrivial.mpr hsec)
    intro C hC
    obtain ⟨ξ, rfl⟩ : ∃ ξ : X, closure ({ξ} : Set X) = C :=
      ⟨_, hC.1.isGenericPoint_genericPoint_closure.trans
        (isClosed_of_mem_irreducibleComponents C hC).closure_eq⟩
    have hξ1 : ξ ∈ genericPointsOne X :=
      mem_genericPointsOne_iff.mpr ⟨hC,
        Stacks.Curves.topologicalKrullDim_irreducibleComponent_eq_one f hequi hdim _ hC⟩
    have h0 := hzero ⟨ξ, hξ1⟩
    unfold componentDegree at h0
    have := isFiniteLocallyFreeOfRank_pullback_reducedComponentι ⟨ξ, hξ1⟩ N 1
    rw [← invertibleCurveDegree_eq_curveDegree] at h0
    exact h0.le

end AlgebraicGeometry

end
