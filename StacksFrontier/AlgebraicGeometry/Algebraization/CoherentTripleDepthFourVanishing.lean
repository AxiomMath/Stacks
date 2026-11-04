module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTriviality
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedGlobalSectionsFiniteness

/-!
# The Euler characteristic of an invertible coherent triple vanishes in depth four

Let `(A, 𝔪)` be a Noetherian local ring, `f ∈ 𝔪` a nonzerodivisor, and `(ℱ, ℱ₀, α)` an invertible
coherent triple. If `depth(A) ≥ 3` and the global sections of the closed-fibre member form a
finite `A`-module of depth at least three, then the Euler characteristic of the triple is zero.

In the situation of [Stacks, Tag 0FIX] the closed-fibre member is an invertible module on
`Spec(A/fA)`, so its global sections are `A/fA`, whose depth over `A` is at least three by
hypothesis (b) of that tag. So this is the vanishing that [Stacks, Tag 0FIX] needs, and it is
proved without the polynomiality of [Stacks, Tag 0F27]: the stronger depth hypothesis replaces
the whole dévissage.

## The argument

By the Euler characteristic formula of [Stacks, Tag 0F28] the Euler characteristic is the length
of the cokernel of the canonical map on global sections, so the claim is that this map is
surjective; and for the prepared extension given by the direct image of the punctured-spectrum
member, that is the surjectivity of the closed-fibre map
`M/fM → Γ(Spec(A/fA), ℱ₀)`, where `M = Γ(Spec A, ι_*ℱ)`.

That map is injective with a cokernel of finite length, both already known. `M` is a finite
`A`-module of depth at least two, and `H^2_𝔪(M)` is a finite `A`-module because `ℱ` is invertible
on the punctured spectrum: this is [Stacks, Tag 0BPY], in the form
`Stacks.Algebraization.finite_localCohomology_globalSections_of_isFiniteLocallyFree_restrict`.
The module-level statement
`Stacks.LocalCohomology.surjective_of_isFiniteLength_cokernel_of_finite_localCohomology` then
gives surjectivity.

## Main definitions

* `Stacks.Algebraization.closedFibreSectionsModule`: the global sections of the closed-fibre
  member of a coherent triple, as an `A`-module.

## Main results

* `Stacks.Algebraization.isFiniteLocallyFree_of_isInvertible_scheme`: an invertible module on a
  scheme is finite locally free.
* `Stacks.Algebraization.eulerCharacteristic_eq_zero_of_three_le_depth_closedFibreSections`

## References

* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 0FIX](https://stacks.math.columbia.edu/tag/0FIX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **An invertible module on a scheme is finite locally free**, being finite locally free of
rank one. -/
theorem isFiniteLocallyFree_of_isInvertible_scheme (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Scheme.Modules.IsFiniteLocallyFree L := by
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  exact (Scheme.Modules.isFiniteLocallyFree_iff L).mpr h2

/-- The global sections of the closed-fibre member of a coherent triple, as an `A`-module through
the surjection `A → A/fA`. This is the target of the closed-fibre map of every prepared
extension of the triple. -/
abbrev closedFibreSectionsModule (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (T : CoherentTriple A f) : ModuleCat.{u} A :=
  ModuleCat.of A
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj T.F₀)).carrier

/-- **The Euler characteristic of an invertible coherent triple vanishes when the global sections
of its closed-fibre member have depth at least three.** Let `(A, 𝔪)` be a Noetherian local ring
of depth at least three and `f ∈ 𝔪` a nonzerodivisor. For an invertible coherent triple whose
closed-fibre sections form a finite `A`-module of depth at least three, the Euler characteristic
is zero.

The canonical map on global sections is surjective: it is the closed-fibre map of the direct
image of the punctured-spectrum member, which is injective with a cokernel of finite length, and
`H^2_𝔪` of its source is finite by [Stacks, Tag 0BPY] since the punctured-spectrum member is
invertible. -/
theorem eulerCharacteristic_eq_zero_of_three_le_depth_closedFibreSections (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A)
    (hreg : IsRegular f) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    (hNfin : Module.Finite A (closedFibreSectionsModule A f T : Type u))
    (hdN : 3 ≤ Module.depth A (maximalIdeal A) (closedFibreSectionsModule A f T : Type u)) :
    T.eulerCharacteristic hf hreg = 0 := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  have hd2 : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    (show (2 : ℕ∞) ≤ 3 by decide).trans hdepth
  have hfinlen := finiteLength_cokernel_globalSectionsMap A f hf hreg T hdepth
  -- the Euler characteristic vanishes exactly when the canonical map on sections is surjective
  have hzero : T.eulerCharacteristic hf hreg = 0 ↔
      Function.Surjective (globalSectionsMap A f T) := by
    rw [CoherentTriple.eulerCharacteristic_eq_length_cokernel A f hf hreg T hdepth,
      Int.natCast_eq_zero]
    exact length_cokernel_toNat_eq_zero_iff_surjective _ hfinlen
  rw [hzero]
  obtain ⟨P, hP, -, hiff⟩ := exists_preparedExtension_length_cokernel_eq A f hf hreg T hdepth
  rw [hiff]
  -- the global sections of the prepared extension
  have hcP : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  have hqcP : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  have hftP : P.F'.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hMfin : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') :=
    finite_globalSections_of_isCoherent P.F' P.coherent
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app P.F') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.isIso_app_iff_of_iso
        (eqToIso hP)).mpr (isIso_unit_pushforward_puncturedSpectrum A T.F hd2)
  have hdM : 2 ≤ Module.depth A (maximalIdeal A)
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') :=
    two_le_depth_globalSections_of_isIso_unit A P.F' hunit
  have hregM : IsSMulRegular ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') f := by
    have hr' : IsSMulRegular Γ(P.F', ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) := by
      simpa using P.regular ⊤
    exact hr'
  -- `H^2_𝔪` of those sections is finite, the punctured-spectrum member being invertible
  have hrestr : P.F'.restrict (Stacks.Divisors.puncturedSpectrum A).ι ≅ T.F :=
    (Scheme.Modules.restrictFunctorIsoPullback
      (Stacks.Divisors.puncturedSpectrum A).ι).app P.F' ≪≫ P.alpha'
  have hFL : Scheme.Modules.IsFiniteLocallyFree
      (P.F'.restrict (Stacks.Divisors.puncturedSpectrum A).ι) :=
    Scheme.Modules.IsFiniteLocallyFree.of_iso hrestr.symm
      (isFiniteLocallyFree_of_isInvertible_scheme _ T.F)
  have hfin2 := finite_localCohomology_globalSections_of_isFiniteLocallyFree_restrict A P.F'
    hMfin hdepth hFL 2 le_rfl
  -- the closed-fibre map, read on `M/fM`
  let E := closedFibreSectionsEquivQuotSMulTop A f P.F'
  set φ : QuotSMulTop f ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') →ₗ[A]
      (closedFibreSectionsModule A f T : Type u) :=
    P.closedFibreMap.hom ∘ₗ E.symm.toLinearMap with hφdef
  have hinj : Function.Injective φ :=
    (injective_closedFibreMap_of_two_le_depth A f hf T P hMfin hdM).comp E.symm.injective
  have hrange : LinearMap.range φ = LinearMap.range P.closedFibreMap.hom := by
    rw [hφdef, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  -- the cokernel has finite length
  have hcoklen : Module.length A
      ((closedFibreSectionsModule A f T : Type u) ⧸ LinearMap.range P.closedFibreMap.hom) =
      Module.length A (cokernel P.closedFibreMap).carrier :=
    ((ModuleCat.cokernelIsoRangeQuotient P.closedFibreMap).toLinearEquiv).length_eq.symm
  have hQ : IsFiniteLength A ((closedFibreSectionsModule A f T : Type u) ⧸
      LinearMap.range φ) := by
    rw [hrange, ← Module.length_ne_top_iff, hcoklen, Module.length_ne_top_iff]
    exact cokernel_finiteLength A f T P
  -- the module-level surjectivity
  have hsurj :=
    Stacks.LocalCohomology.surjective_of_isFiniteLength_cokernel_of_finite_localCohomology
      A hf ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F')
      (closedFibreSectionsModule A f T) hregM hdM hfin2 hdN φ hinj hQ
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨E.symm x, hx⟩

end Stacks.Algebraization

end
