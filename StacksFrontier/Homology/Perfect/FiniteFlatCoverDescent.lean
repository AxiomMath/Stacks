module

public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.Local

/-!
# Perfectness descends along a finite flat covering of `Spec`

Let `A → A_i` (`i` in a finite set) be flat ring maps whose maps on spectra are jointly
surjective, and let `K` be a complex of `A`-modules. If every base change `K ⊗_A A_i` is perfect,
then `K` is perfect. The product `B = ∏ A_i` is faithfully flat over `A`, so this reduces to
Stacks 068T; and perfectness over `B` is checked on the localizations `B_{e_i} = A_i` at the
idempotents `e_i`, which span the unit ideal, by Stacks 066Y.

## Main results

* `StacksDraft.Perfect.isPerfect_Q_extendScalars_of_flat`: termwise base change along a flat map
  preserves perfectness.
* `StacksDraft.Perfect.isPerfect_of_extendScalars_of_faithfullyFlat_pi` and
  `StacksDraft.Perfect.isPerfect_of_extendScalars_of_flat_of_comap_surjective`: the descent.

## References

* [Stacks Project, Tag 068T](https://stacks.math.columbia.edu/tag/068T)
* [Stacks Project, Tag 066Y](https://stacks.math.columbia.edu/tag/066Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- **Termwise base change along a flat map preserves perfectness.** If `Y` represents a perfect
object of `D(S)` and `σ : S → T` is flat, then `Y ⊗_S T` represents a perfect object of
`D(T)`. -/
theorem isPerfect_Q_extendScalars_of_flat {S T : Type u} [CommRing S] [CommRing T]
    (σ : S →+* T) (hσ : σ.Flat) (Y : CochainComplex (ModuleCat.{u} S) ℤ)
    (hY : IsPerfect (DerivedCategory.Q.obj Y)) :
    IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} σ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y)) := by
  let F := ModuleCat.extendScalars.{u, u, u} σ
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat'.{u, u} σ hσ
  exact isPerfect_of_iso (F.mapDerivedCategoryFactors.app Y).symm
    (isPerfect_derivedExtensionScalars_of_comparison.{u, u, u} σ F.mapDerivedCategory
      F.mapDerivedCategoryFactors.hom (fun _ _ _ _ => inferInstance) _ hY)

/-- Termwise base change along two ring maps is base change along the composite. -/
def extendScalarsCompQIso {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) :=
  DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp.{u, u} f g).symm (ComplexShape.up ℤ)).symm.app K)

section Pi

variable {ι : Type u} [Finite ι] [DecidableEq ι] (S : ι → Type u) [∀ i, CommRing (S i)]

/-- The idempotent `e_i` of a finite product of rings. -/
private abbrev piIdempotent (i : ι) : (∀ j, S j) := Pi.single i 1

omit [Finite ι] in
private theorem isIdempotentElem_piIdempotent (i : ι) : IsIdempotentElem (piIdempotent S i) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [piIdempotent]
  · simp [piIdempotent, h]

private theorem span_range_piIdempotent : Ideal.span (Set.range (piIdempotent S)) = ⊤ := by
  have := Fintype.ofFinite ι
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : ∀ j, S j) = ∑ i, piIdempotent S i := by
    ext j
    simp [Finset.sum_apply]
  rw [h1]
  exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨i, rfl⟩

omit [Finite ι] in
/-- `A_i` is the localization of `∏ A_j` away from `e_i`. -/
private theorem isLocalization_away_piIdempotent (i : ι) :
    letI := (Pi.evalRingHom S i).toAlgebra
    IsLocalization.Away (piIdempotent S i) (S i) := by
  let := (Pi.evalRingHom S i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_piIdempotent S i)
    (fun x y => ?_) (fun x => ⟨Pi.single i x, by simp [RingHom.algebraMap_toAlgebra]⟩)
  simp only [RingHom.algebraMap_toAlgebra, Pi.evalRingHom_apply]
  refine ⟨fun h => ?_, fun h => by simpa [piIdempotent] using congrFun h i⟩
  ext j
  by_cases hj : j = i
  · subst hj
    simp [piIdempotent, h]
  · simp [piIdempotent, hj]

end Pi

/-- **Perfectness descends along a finite family whose product is faithfully flat.** Let
`f_i : A → A_i` (`i` in a finite set) be ring maps with `A → ∏ A_i` faithfully flat. If
`K ⊗_A A_i` is perfect for every `i`, then `K` is perfect. -/
theorem isPerfect_of_extendScalars_of_faithfullyFlat_pi {A : Type u} [CommRing A]
    {ι : Type u} [Finite ι] {S : ι → Type u} [∀ i, CommRing (S i)] (f : ∀ i, A →+* S i)
    (hφ : (RingHom.pi f).FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))) :
    IsPerfect (DerivedCategory.Q.obj K) := by
  classical
  let φ : A →+* ∀ i, S i := RingHom.pi f
  refine isPerfect_of_faithfullyFlat_baseChange.{u, u, u} φ hφ K ?_
  refine isPerfect_of_localizationSpan.{u, u} (piIdempotent S) (span_range_piIdempotent S) _
    fun i => ?_
  let := (Pi.evalRingHom S i).toAlgebra
  have := isLocalization_away_piIdempotent S i
  let σ : Localization.Away (piIdempotent S i) ≃+* S i :=
    (IsLocalization.algEquiv (Submonoid.powers (piIdempotent S i)) _ (S i)).toRingEquiv
  have hσ : (algebraMap (∀ j, S j) (Localization.Away (piIdempotent S i))).comp φ =
      σ.symm.toRingHom.comp (f i) := by
    ext r
    apply σ.injective
    change σ (algebraMap _ _ (φ r)) = σ (σ.symm (f i r))
    rw [RingEquiv.apply_symm_apply]
    exact (IsLocalization.algEquiv (Submonoid.powers (piIdempotent S i)) _ (S i)).commutes (φ r)
  have h2 := isPerfect_of_iso (extendScalarsCompQIso (f i) σ.symm.toRingHom K)
    (isPerfect_Q_extendScalars_of_flat σ.symm.toRingHom
      (RingHom.Flat.of_bijective σ.symm.bijective) _ (hK i))
  rw [← hσ] at h2
  have h3 := isPerfect_of_iso (extendScalarsCompQIso φ
    (algebraMap (∀ j, S j) (Localization.Away (piIdempotent S i))) K).symm h2
  let F := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (∀ j, S j) (Localization.Away (piIdempotent S i)))
  have : F.Additive := extendScalars_additive.{u, u} _
  have : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away (piIdempotent S i))
          (Submonoid.powers (piIdempotent S i))))
  exact isPerfect_of_iso (F.mapDerivedCategoryFactors.app _) h3

/-- **Perfectness descends along a finite flat covering of `Spec`.** Let `f_i : A → A_i`
(`i` in a finite set) be flat ring maps such that every prime of `A` is the contraction of a
prime of some `A_i`. If `K ⊗_A A_i` is perfect for every `i`, then `K` is perfect. -/
theorem isPerfect_of_extendScalars_of_flat_of_comap_surjective {A : Type u} [CommRing A]
    {ι : Type u} [Finite ι] {S : ι → Type u} [∀ i, CommRing (S i)] (f : ∀ i, A →+* S i)
    (hflat : ∀ i, (f i).Flat)
    (hcov : ∀ p : PrimeSpectrum A, ∃ i, ∃ q : PrimeSpectrum (S i), q.comap (f i) = p)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))) :
    IsPerfect (DerivedCategory.Q.obj K) := by
  have := Fintype.ofFinite ι
  refine isPerfect_of_extendScalars_of_faithfullyFlat_pi f ?_ K hK
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨?_, fun p => ?_⟩
  · let : ∀ i, Algebra A (S i) := fun i => (f i).toAlgebra
    have : ∀ i, Module.Flat A (S i) := hflat
    have : Module.Flat A (DirectSum ι S) := inferInstance
    exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A ι S).symm
  · obtain ⟨i, q, hq⟩ := hcov p
    exact ⟨q.comap (Pi.evalRingHom S i), by rw [← hq]; rfl⟩

end StacksDraft.Perfect

end
