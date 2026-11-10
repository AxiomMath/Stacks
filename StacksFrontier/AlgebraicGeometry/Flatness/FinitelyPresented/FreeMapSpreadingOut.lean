module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapAtGenericFibre
public import StacksFrontier.RingTheory.Flat.DevissageFlatTfae
public import StacksFrontier.RingTheory.Flat.DevissageLocalizeAtPrime
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Module.FinitePresentation.Locus

/-!
# A free map at a generic fibre: spreading out, and the six equivalent conditions

Let `R → S` be a flat ring map of finite presentation with geometrically integral fibres, let
`q ⊆ S` be a prime lying over `r ⊆ R`, write `p = rS` for the generic point of the fibre over `r`,
and let `alpha : S^{⊕ n} → N` be a map from a finite free module to a finitely presented
`S`-module which becomes an isomorphism over the residue field of `p`. Flatness of `N_q` over `R`
is equivalent to five further conditions, among them the existence of an `f ∈ R`, `f ∉ r`, such
that `alpha_f` is universally injective.

## Main results

* `Module.flat_localizedModule_freeMap_tfae`: the equivalence of the six conditions, as a
  `List.TFAE`.
* `Module.universallyInjective_localizedMap_of_flat_localizedModule`: if `N_q` is flat over `R`
  then `alpha_r` is universally injective as a map of `R`-modules.
* `Module.exists_universallyInjective_and_flat_coker_of_flat_localizedModule`: if `N_q` is flat
  over `R` then `alpha_f` is universally injective for some `f ∉ r` and `Coker(alpha)_g` is flat
  over `R` for some `g ∉ q`. Its two halves are
  `Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule` and
  `Module.exists_flat_localizedModule_away_coker_of_flat_localizedModule`.
* `Module.flat_localizedModule_coker_of_flat_localizedModule`: if `N_q` is flat over `R` then so
  is `Coker(alpha)_q`.
* `Module.universallyInjective_localizedMap_and_flat_coker_of_exists_away`,
  `Module.injective_localizedMap_of_universallyInjective_localizedMap`,
  `Module.bijective_localizedMap_map_of_injective_localizedMap`,
  `Module.injective_localizedMap_atPrime_of_bijective_localizedMap_map` and
  `Module.flat_localizedModule_of_injective_localizedMap_of_flat_coker`: the implications
  (2) ⟹ (3), (3) ⟹ (4), (4) ⟹ (5), (5) ⟹ (6) and (6) ⟹ (1) between the conditions of
  `Module.flat_localizedModule_freeMap_tfae`.
* `Algebra.mem_nonZeroDivisors_localization_of_notMem_map`: an element of `S` outside `p = rS`
  becomes a nonzerodivisor in the localization of `S` at `r`.
* `AlgebraicGeometry.geometricallyIntegral_spec_of_isLocalization`: geometrically integral
  fibres are preserved by localizing the base.
* `Module.flat_localizedModule_away_of_forall_flat_localizedModule_atPrime`: flatness over the
  base away from an element, from flatness at every prime of the corresponding basic open.
* `IsLocalizedModule.comp_atPrime_of_isLocalization`: localizing at `T` and then at a prime of
  `S[T⁻¹]` is localizing at the contraction of that prime.
* `Module.injective_rTensor_localizedMap_atPrime_of_under`: universal injectivity over `R` of
  the localization at a prime of `R` passes to the localization at a prime of `S` above it.
* `Module.universallyInjective_localizedModule_away_of_forall_primes`: universal injectivity of
  the localizations at all primes over a basic open `D(f)` gives universal injectivity of the
  localization away from `f`.
* `PrimeSpectrum.exists_notMem_forall_exists_mem_comap_of_isOpen`: for `R → S` flat of finite
  presentation, the image of an open subset of `Spec S` contains a basic open around each of its
  points.
* `LinearMap.bijective_rTensor_residueField_of_bijective_localizedMap`: a map whose localization
  at a prime is bijective stays bijective after base change to the residue field there.
* `Ideal.isPrime_map_of_geometricallyIntegral`: the extension `rS` of a prime `r` is prime, for a
  flat algebra with geometrically integral fibres.

## Implementation notes

Universal injectivity of a map of `A`-modules is spelled as a universally quantified
`Function.Injective (LinearMap.rTensor Q _)`, the test modules ranging over the smallest universe
containing `R`, `S` and `N`. The localizations `alpha_r` and `alpha_f` are taken at
multiplicative subsets of `R`: `alpha_r` is
`LocalizedModule.map r.primeCompl (alpha.restrictScalars R)` and `alpha_f` is
`LocalizedModule.map (Submonoid.powers f) (alpha.restrictScalars R)`. Universal injectivity is
asserted over `R`, which for a map of `R_f`-modules is the same as over `R_f`.

## References

* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
* [Stacks Project, Tag 05CM](https://stacks.math.columbia.edu/tag/05CM)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 00RC](https://stacks.math.columbia.edu/tag/00RC)
* [Stacks Project, Tag 05GF](https://stacks.math.columbia.edu/tag/05GF)
* [Stacks Project, Tag 00I1](https://stacks.math.columbia.edu/tag/00I1)
* [Stacks Project, Tag 00HM](https://stacks.math.columbia.edu/tag/00HM)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open Stacks.UniversalInjectivity.LocalizationCriteria
open scoped TensorProduct

universe u v w

/-- For a flat algebra `S` over `R` with geometrically integral fibres, the extension `rS` of a
prime `r` of `R` is prime. -/
public theorem Ideal.isPrime_map_of_geometricallyIntegral (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime] :
    (Ideal.map (algebraMap R S) r).IsPrime := by
  let : Algebra r.ResidueField (S ⊗[R] r.ResidueField) := Algebra.TensorProduct.rightAlgebra
  have hgi := Algebra.isGeometricallyIntegral_tensorProduct_residueField R S r
  have ht := (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct _ _).mp hgi
    r.ResidueField
  have hd : IsDomain (S ⊗[R] r.ResidueField) :=
    (Algebra.TensorProduct.rid r.ResidueField r.ResidueField
      (S ⊗[R] r.ResidueField)).symm.toRingEquiv.injective.isDomain _
  have hker : RingHom.ker (algebraMap S (S ⊗[R] r.ResidueField)) =
      Ideal.map (algebraMap R S) r := by
    rw [Algebra.ker_algebraMap_tensorProduct_left, Ideal.ker_algebraMap_residueField]
  exact hker ▸ RingHom.ker_isPrime _


/-- For an `R`-algebra `R'` and an `R'`-module `M`, an element of `M` lies in
`I.map (algebraMap R R') • ⊤` if and only if it lies in `I • ⊤`. -/
public theorem Ideal.mem_map_smul_top_iff {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
    (y : M) :
    y ∈ (I.map (algebraMap R R')) • (⊤ : Submodule R' M) ↔ y ∈ I • (⊤ : Submodule R M) := by
  rw [← Submodule.restrictScalars_top R R' M, ← Ideal.smul_restrictScalars,
    Submodule.restrictScalars_mem]


/-- The localization of the base at the contraction of `q` acts on `N_q` compatibly with `R`. -/
public instance isScalarTower_localizationAtPrime_under (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (N : Type w) [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] :
    IsScalarTower R (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl N) :=
  IsScalarTower.of_algebraMap_smul fun a z => by
    rw [← IsScalarTower.algebraMap_smul (Localization.AtPrime q)
      (algebraMap R (Localization.AtPrime (q.under R)) a) z,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]


private lemma injective_of_comm_square {A B C D : Type*} {u : A → B} {v : C → D}
    {p : A → C} {s : B → D} (hu : Function.Surjective u) (hv : Function.Injective v)
    (hp : Function.Injective p) (hcomm : ∀ a, s (u a) = v (p a)) : Function.Injective s := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := hu x
  obtain ⟨b, rfl⟩ := hu y
  rw [hcomm, hcomm] at hxy
  rw [hp (hv hxy)]

/-- Any two localizations of the same map at the same multiplicative set agree on injectivity
after `- ⊗_R Q`. -/
private lemma injective_rTensor_of_square
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (W : Submonoid S)
    {M M' P P' : Type*}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    [AddCommGroup P'] [Module S P'] [Module R P'] [IsScalarTower R S P']
    (γ : M →ₗ[S] P) [IsLocalizedModule W γ] (γ' : M' →ₗ[S] P') [IsLocalizedModule W γ']
    (α : M →ₗ[S] M') (β : P →ₗ[S] P') (hβ : β ∘ₗ γ = γ' ∘ₗ α)
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (hinj : Function.Injective
      (LinearMap.rTensor Q ((LocalizedModule.map W α).restrictScalars R))) :
    Function.Injective (LinearMap.rTensor Q (β.restrictScalars R)) := by
  have hsq : β ∘ₗ (IsLocalizedModule.linearEquiv W
        (LocalizedModule.mkLinearMap W M) γ).toLinearMap
      = (IsLocalizedModule.linearEquiv W (LocalizedModule.mkLinearMap W M')
        γ').toLinearMap ∘ₗ (LocalizedModule.map W α).restrictScalars S := by
    refine IsLocalizedModule.linearMap_ext W (LocalizedModule.mkLinearMap W M) γ' ?_
    ext m
    have h1 : (LocalizedModule.map W α) (LocalizedModule.mkLinearMap W M m)
        = LocalizedModule.mkLinearMap W M' (α m) := by
      simp [LocalizedModule.mkLinearMap_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, h1, IsLocalizedModule.linearEquiv_apply]
    exact LinearMap.congr_fun hβ m
  have hsqR : ∀ x, LinearMap.rTensor Q (β.restrictScalars R)
        (LinearMap.rTensor Q ((IsLocalizedModule.linearEquiv W
          (LocalizedModule.mkLinearMap W M) γ).restrictScalars R).toLinearMap x)
      = LinearMap.rTensor Q ((IsLocalizedModule.linearEquiv W
          (LocalizedModule.mkLinearMap W M') γ').restrictScalars R).toLinearMap
          (LinearMap.rTensor Q ((LocalizedModule.map W α).restrictScalars R) x) := by
    intro x
    have h2 : (β.restrictScalars R) ∘ₗ ((IsLocalizedModule.linearEquiv W
          (LocalizedModule.mkLinearMap W M) γ).restrictScalars R).toLinearMap
        = ((IsLocalizedModule.linearEquiv W (LocalizedModule.mkLinearMap W M')
          γ').restrictScalars R).toLinearMap ∘ₗ (LocalizedModule.map W α).restrictScalars R :=
      LinearMap.ext fun y => LinearMap.congr_fun hsq y
    have h3 := congrArg (LinearMap.rTensor Q) h2
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp] at h3
    exact LinearMap.congr_fun h3 x
  exact injective_of_comm_square
    (LinearMap.rTensor_surjective Q (((IsLocalizedModule.linearEquiv W
      (LocalizedModule.mkLinearMap W M) γ).restrictScalars R).surjective))
    ((LinearEquiv.rTensor Q ((IsLocalizedModule.linearEquiv W
      (LocalizedModule.mkLinearMap W M') γ').restrictScalars R)).injective)
    hinj hsqR

/-- A localization at a smaller multiplicative set factors through, and the factoring map is
itself a localization at the larger set. -/
private lemma isLocalizedModule_lift_of_le {S : Type*} [CommRing S] {W₁ W : Submonoid S}
    (hle : W₁ ≤ W) {M M₁ M₂ : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module S M₂]
    (f : M →ₗ[S] M₁) [IsLocalizedModule W₁ f] (h : M →ₗ[S] M₂) [IsLocalizedModule W h]
    (hu : ∀ x : W₁, IsUnit ((algebraMap S (Module.End S M₂)) (x : S))) :
    IsLocalizedModule W (IsLocalizedModule.lift W₁ f h hu) := by
  have hgf : ∀ m, IsLocalizedModule.lift W₁ f h hu (f m) = h m := fun m =>
    LinearMap.congr_fun (IsLocalizedModule.lift_comp W₁ f h hu) m
  refine ⟨IsLocalizedModule.map_units h, ?_, ?_⟩
  · intro y
    obtain ⟨⟨x, w⟩, hw⟩ := IsLocalizedModule.surj W h y
    exact ⟨⟨f x, w⟩, by simpa [hgf] using hw⟩
  · intro z₁ z₂ hz
    obtain ⟨⟨x₁, t₁⟩, ht₁⟩ := IsLocalizedModule.surj W₁ f z₁
    obtain ⟨⟨x₂, t₂⟩, ht₂⟩ := IsLocalizedModule.surj W₁ f z₂
    simp only [Submonoid.smul_def] at ht₁ ht₂
    have e₁ : h x₁ = (t₁ : S) • IsLocalizedModule.lift W₁ f h hu z₁ := by
      rw [← hgf x₁, ← ht₁, map_smul]
    have e₂ : h x₂ = (t₂ : S) • IsLocalizedModule.lift W₁ f h hu z₂ := by
      rw [← hgf x₂, ← ht₂, map_smul]
    have key : h ((t₂ : S) • x₁) = h ((t₁ : S) • x₂) := by
      rw [map_smul, map_smul, e₁, e₂, hz, smul_smul, smul_smul, mul_comm]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := W) (f := h) key
    refine ⟨⟨(c : S) * t₁ * t₂, mul_mem (mul_mem c.2 (hle t₁.2)) (hle t₂.2)⟩, ?_⟩
    have hfc : (c : S) • (t₂ : S) • f x₁ = (c : S) • (t₁ : S) • f x₂ := by
      simpa only [Submonoid.smul_def, map_smul] using congrArg f hc
    calc ((c : S) * t₁ * t₂) • z₁
        = (c : S) • (t₂ : S) • ((t₁ : S) • z₁) := by
          rw [smul_smul, smul_smul]; congr 1; ring
      _ = (c : S) • (t₂ : S) • f x₁ := by rw [ht₁]
      _ = (c : S) • (t₁ : S) • f x₂ := hfc
      _ = (c : S) • (t₁ : S) • ((t₂ : S) • z₂) := by rw [ht₂]
      _ = ((c : S) * t₁ * t₂) • z₂ := by rw [smul_smul, smul_smul, mul_assoc]

/-- Universal injectivity of a localization at `W₁ ⊆ R` passes to a localization at any
`W ⊆ S` containing the image of `W₁`. -/
private lemma injective_rTensor_localizedMap_of_algebraMapSubmonoid_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M M' : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (α : M →ₗ[S] M') (W₁ : Submonoid R) (W : Submonoid S)
    (hle : Algebra.algebraMapSubmonoid S W₁ ≤ W)
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (h : Function.Injective (LinearMap.rTensor Q
      ((LocalizedModule.map W₁ (α.restrictScalars R)).restrictScalars R))) :
    Function.Injective (LinearMap.rTensor Q
      ((LocalizedModule.map W α).restrictScalars R)) := by
  have i1 : IsLocalizedModule W₁
      ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M).restrictScalars R) :=
    IsLocalizedModule.restrictScalars _ _
  have i2 : IsLocalizedModule W₁
      ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M').restrictScalars R) :=
    IsLocalizedModule.restrictScalars _ _
  have hsq1 :
      ((LocalizedModule.map (Algebra.algebraMapSubmonoid S W₁) α).restrictScalars S
          ).restrictScalars R ∘ₗ
        (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M).restrictScalars R
      = ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M').restrictScalars R)
          ∘ₗ α.restrictScalars R := by
    ext m
    simp [LocalizedModule.mkLinearMap_apply]
  have step1 := injective_rTensor_of_square (R := R) (S := R) W₁
    ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M).restrictScalars R)
    ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M').restrictScalars R)
    (α.restrictScalars R)
    (((LocalizedModule.map (Algebra.algebraMapSubmonoid S W₁) α).restrictScalars S
      ).restrictScalars R) hsq1 Q h
  have hu : ∀ x : Algebra.algebraMapSubmonoid S W₁,
      IsUnit ((algebraMap S (Module.End S (LocalizedModule W M))) (x : S)) := fun x =>
    IsLocalizedModule.map_units (LocalizedModule.mkLinearMap W M) ⟨(x : S), hle x.2⟩
  have hu' : ∀ x : Algebra.algebraMapSubmonoid S W₁,
      IsUnit ((algebraMap S (Module.End S (LocalizedModule W M'))) (x : S)) := fun x =>
    IsLocalizedModule.map_units (LocalizedModule.mkLinearMap W M') ⟨(x : S), hle x.2⟩
  have ig : IsLocalizedModule W (IsLocalizedModule.lift (Algebra.algebraMapSubmonoid S W₁)
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M)
      (LocalizedModule.mkLinearMap W M) hu) := isLocalizedModule_lift_of_le hle _ _ hu
  have ig' : IsLocalizedModule W (IsLocalizedModule.lift (Algebra.algebraMapSubmonoid S W₁)
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M')
      (LocalizedModule.mkLinearMap W M') hu') := isLocalizedModule_lift_of_le hle _ _ hu'
  have hsq3 : (LocalizedModule.map W α).restrictScalars S ∘ₗ
        IsLocalizedModule.lift (Algebra.algebraMapSubmonoid S W₁)
          (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M)
          (LocalizedModule.mkLinearMap W M) hu
      = IsLocalizedModule.lift (Algebra.algebraMapSubmonoid S W₁)
          (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M')
          (LocalizedModule.mkLinearMap W M') hu' ∘ₗ
        (LocalizedModule.map (Algebra.algebraMapSubmonoid S W₁) α).restrictScalars S := by
    refine IsLocalizedModule.ext (Algebra.algebraMapSubmonoid S W₁)
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M) hu' ?_
    ext m
    have l1 := LinearMap.congr_fun (IsLocalizedModule.lift_comp
      (Algebra.algebraMapSubmonoid S W₁)
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M)
      (LocalizedModule.mkLinearMap W M) hu) m
    have l2 := LinearMap.congr_fun (IsLocalizedModule.lift_comp
      (Algebra.algebraMapSubmonoid S W₁)
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S W₁) M')
      (LocalizedModule.mkLinearMap W M') hu') (α m)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply] at *
    rw [l1]
    simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk] at *
    rw [l2]
  exact IsLocalizedModule.rTensor_injective_of_rTensor_injective W _ _
    ((LocalizedModule.map (Algebra.algebraMapSubmonoid S W₁) α).restrictScalars S)
    ((LocalizedModule.map W α).restrictScalars S) hsq3 Q step1

/-- If the localization of `α` at the prime `q.under R` of `R` is universally injective as a map
of `R`-modules, then so is its localization at `q`. -/
public theorem Module.injective_rTensor_localizedMap_atPrime_of_under
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M M' : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (α : M →ₗ[S] M') (q : Ideal S) [q.IsPrime]
    (h : ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
      Function.Injective (((LocalizedModule.map (q.under R).primeCompl
        (α.restrictScalars R)).restrictScalars R).rTensor Q)) :
    ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
      Function.Injective (((LocalizedModule.map q.primeCompl α).restrictScalars R).rTensor Q) := by
  intro Q _ _
  refine injective_rTensor_localizedMap_of_algebraMapSubmonoid_le α _ _ ?_ Q (h Q)
  rintro x ⟨a, ha, rfl⟩
  exact ha


/-! ### Elements of `S` outside the contraction of a prime of a localization -/

/-- An element of the localizing submonoid misses the contraction of any prime of the
localization, its image being a unit there. -/
public theorem IsLocalization.algebraMap_mem_primeCompl {S : Type*} [CommRing S]
    (T : Submonoid S) (Sf : Type*)
    [CommRing Sf] [Algebra S Sf] [IsLocalization T Sf] (Q' : Ideal Sf) [Q'.IsPrime] (t : T) :
    algebraMap S Sf (t : S) ∈ Q'.primeCompl :=
  fun hmem => ‹Q'.IsPrime›.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.map_units Sf t))

private lemma le_primeCompl_comap {S : Type*} [CommRing S] (T : Submonoid S) (Sf : Type*)
    [CommRing Sf] [Algebra S Sf] [IsLocalization T Sf] (Q' : Ideal Sf) [Q'.IsPrime] :
    T ≤ (Q'.comap (algebraMap S Sf)).primeCompl :=
  fun t ht => IsLocalization.algebraMap_mem_primeCompl T Sf Q' ⟨t, ht⟩

private lemma exists_smul_eq_smul {S : Type*} [CommRing S] (T : Submonoid S) (Sf : Type*)
    [CommRing Sf] [Algebra S Sf] [IsLocalization T Sf] (Q' : Ideal Sf) [Q'.IsPrime]
    (w : Q'.primeCompl) (X : Type*) [AddCommGroup X] [Module S X] [Module Sf X]
    [IsScalarTower S Sf X] :
    ∃ (a : (Q'.comap (algebraMap S Sf)).primeCompl) (t : T), ∀ x : X,
      (a : S) • x = (t : S) • ((w : Sf) • x) := by
  obtain ⟨⟨a, t⟩, ha⟩ := IsLocalization.mk'_surjective T (w : Sf)
  simp only at ha
  have key : algebraMap S Sf a = algebraMap S Sf (t : S) * (w : Sf) := by
    rw [← ha, mul_comm, IsLocalization.mk'_spec]
  have hmem : a ∈ (Q'.comap (algebraMap S Sf)).primeCompl := by
    change algebraMap S Sf a ∈ Q'.primeCompl
    rw [key]
    exact fun hm => (‹Q'.IsPrime›.mem_or_mem hm).elim
      (IsLocalization.algebraMap_mem_primeCompl T Sf Q' t) w.2
  refine ⟨⟨a, hmem⟩, t, fun x => ?_⟩
  rw [← algebraMap_smul (A := Sf) (a : S) x]
  change algebraMap S Sf a • x = _
  rw [key, mul_smul, algebraMap_smul]

/-- Localizing at `T ⊆ S` and then at the complement of a prime `Q'` of `S[T⁻¹]` is the same as
localizing at the complement of the contraction of `Q'` to `S`. -/
public theorem IsLocalizedModule.comp_atPrime_of_isLocalization {S : Type*} [CommRing S]
    (T : Submonoid S) (Sf : Type*)
    [CommRing Sf] [Algebra S Sf] [IsLocalization T Sf] (Q' : Ideal Sf) [Q'.IsPrime]
    {M N P : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] [Module Sf N] [IsScalarTower S Sf N]
    [AddCommGroup P] [Module S P] [Module Sf P] [IsScalarTower S Sf P]
    (g₁ : M →ₗ[S] N) [IsLocalizedModule T g₁]
    (g₂ : N →ₗ[Sf] P) [IsLocalizedModule Q'.primeCompl g₂] :
    IsLocalizedModule (Q'.comap (algebraMap S Sf)).primeCompl
      ((g₂.restrictScalars S) ∘ₗ g₁) where
  map_units a := by
    have hb := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g₂
      (⟨algebraMap S Sf (a : S), a.2⟩ : Q'.primeCompl))
    have hfun : (⇑(algebraMap S (Module.End S P) (a : S)) : P → P)
        = ⇑(algebraMap Sf (Module.End Sf P) (algebraMap S Sf (a : S))) := by
      funext x
      simp only [Module.algebraMap_end_apply, algebraMap_smul]
    rw [Module.End.isUnit_iff, hfun]
    exact hb
  surj y := by
    obtain ⟨⟨n, w⟩, hw⟩ := IsLocalizedModule.surj Q'.primeCompl g₂ y
    obtain ⟨a, t₀, hat⟩ := exists_smul_eq_smul T Sf Q' w P
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj T g₁ n
    refine ⟨⟨(t₀ : S) • m, a * ⟨(t : S), le_primeCompl_comap T Sf Q' t.2⟩⟩, ?_⟩
    have hay : (a : S) • y = (t₀ : S) • g₂ n := by
      rw [hat y, show (w : Sf) • y = g₂ n from hw]
    change ((a : S) * (t : S)) • y = g₂ (g₁ ((t₀ : S) • m))
    rw [mul_comm, mul_smul, hay, g₁.map_smul, ← ht,
      g₂.map_smul_of_tower, g₂.map_smul_of_tower]
    exact smul_comm _ _ _
  exists_of_eq {x₁ x₂} he := by
    have he' : g₂ (g₁ x₁) = g₂ (g₁ x₂) := he
    obtain ⟨w, hw⟩ := IsLocalizedModule.exists_of_eq (S := Q'.primeCompl) (f := g₂) he'
    obtain ⟨a, t₀, hat⟩ := exists_smul_eq_smul T Sf Q' w N
    have ha : g₁ ((a : S) • x₁) = g₁ ((a : S) • x₂) := by
      rw [map_smul, map_smul, hat, hat,
        show (w : Sf) • g₁ x₁ = (w : Sf) • g₁ x₂ from hw]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g₁) ha
    refine ⟨⟨(t : S), le_primeCompl_comap T Sf Q' t.2⟩ * a, ?_⟩
    change ((t : S) * (a : S)) • x₁ = ((t : S) * (a : S)) • x₂
    rw [mul_smul, mul_smul]
    exact ht


/-! ### Universal injectivity of the localization away from an element -/

private lemma localizedMapR_localization_universallyInjective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M M' : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (α : M →ₗ[S] M') (T : Submonoid S) (Q' : Ideal (Localization T)) [Q'.IsPrime]
    [(Q'.comap (algebraMap S (Localization T))).IsPrime]
    (hq : UniversallyInjective.{max u w} (A := R)
      (localizedMapR α (Q'.comap (algebraMap S (Localization T))))) :
    UniversallyInjective.{max u w} (A := R) (localizedMapR (LocalizedModule.map T α) Q') := by
  intro Q _ _
  have i₁ : IsLocalizedModule (Q'.comap (algebraMap S (Localization T))).primeCompl
      (((LocalizedModule.mkLinearMap Q'.primeCompl (LocalizedModule T M)).restrictScalars S) ∘ₗ
        LocalizedModule.mkLinearMap T M) :=
    IsLocalizedModule.comp_atPrime_of_isLocalization T (Localization T) Q' _ _
  have i₂ : IsLocalizedModule (Q'.comap (algebraMap S (Localization T))).primeCompl
      (((LocalizedModule.mkLinearMap Q'.primeCompl (LocalizedModule T M')).restrictScalars S) ∘ₗ
        LocalizedModule.mkLinearMap T M') :=
    IsLocalizedModule.comp_atPrime_of_isLocalization T (Localization T) Q' _ _
  have hβ : (((LocalizedModule.map Q'.primeCompl (LocalizedModule.map T α)).restrictScalars
          (Localization T)).restrictScalars S) ∘ₗ
        (((LocalizedModule.mkLinearMap Q'.primeCompl (LocalizedModule T M)).restrictScalars S) ∘ₗ
          LocalizedModule.mkLinearMap T M)
      = (((LocalizedModule.mkLinearMap Q'.primeCompl
            (LocalizedModule T M')).restrictScalars S) ∘ₗ
          LocalizedModule.mkLinearMap T M') ∘ₗ α := by
    ext m
    simp [LocalizedModule.mkLinearMap_apply]
  exact injective_rTensor_of_square
    (Q'.comap (algebraMap S (Localization T))).primeCompl _ _ α _ hβ Q (hq Q)

/-- Glueing universal injectivity on a basic open of the base: if for every prime `q` of `S`
whose contraction to `R` avoids `f` the localized map `α_q` is universally injective as a map of
`R`-modules, then the localization of `α` away from the image of `f` is universally injective as
a map of `R`-modules. -/
public theorem Module.universallyInjective_localizedModule_away_of_forall_primes
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M M' : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (α : M →ₗ[S] M') (f : R)
    (h : ∀ (q : Ideal S) [q.IsPrime], f ∉ q.comap (algebraMap R S) →
      UniversallyInjective.{max u w} (A := R) (localizedMapR α q)) :
    UniversallyInjective.{max u w} (A := R)
      ((LocalizedModule.map (Submonoid.powers (algebraMap R S f)) α).restrictScalars R) := by
  have key : ∀ (Q' : Ideal (Localization (Submonoid.powers (algebraMap R S f)))) [Q'.IsPrime],
      UniversallyInjective.{max u w} (A := R)
        (localizedMapR (LocalizedModule.map (Submonoid.powers (algebraMap R S f)) α) Q') := by
    intro Q' _
    have hp : (Q'.comap (algebraMap S
        (Localization (Submonoid.powers (algebraMap R S f))))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hf : f ∉ (Q'.comap (algebraMap S
        (Localization (Submonoid.powers (algebraMap R S f))))).comap (algebraMap R S) :=
      IsLocalization.algebraMap_mem_primeCompl _ _ Q' ⟨algebraMap R S f, Submonoid.mem_powers _⟩
    exact localizedMapR_localization_universallyInjective α _ Q' (h _ hf)
  exact ((universally_injective_check_stalks
    (LocalizedModule.map (Submonoid.powers (algebraMap R S f)) α)).out 2 1).mp key


/-- Spreading out over the base: if `R → S` is flat of finite presentation and `U ⊆ Spec S` is
open and contains a prime lying over `r`, then some `f ∉ r` has the property that every prime of
`R` not containing `f` is in the image of `U`. -/
public theorem PrimeSpectrum.exists_notMem_forall_exists_mem_comap_of_isOpen
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (U : Set (PrimeSpectrum S)) (hU : IsOpen U) (r : Ideal R) [r.IsPrime]
    (q : PrimeSpectrum S) (hqU : q ∈ U) (hq : q.asIdeal.comap (algebraMap R S) = r) :
    ∃ f ∈ r.primeCompl, ∀ r' : Ideal R, r'.IsPrime → f ∉ r' →
      ∃ q' ∈ U, q'.asIdeal.comap (algebraMap R S) = r' := by
  have := Algebra.HasGoingDown.of_flat (R := R) (S := S)
  have hV : IsOpen (comap (algebraMap R S) '' U) :=
    isOpenMap_comap_of_hasGoingDown_of_finitePresentation U hU
  have hp : (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R) ∈ comap (algebraMap R S) '' U :=
    ⟨q, hqU, PrimeSpectrum.ext (by rw [comap_asIdeal, hq])⟩
  obtain ⟨v, ⟨f, hf⟩, hpv, hvV⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hV
  subst hf
  refine ⟨f, (mem_basicOpen f _).1 hpv, fun r' hr' hfr' => ?_⟩
  obtain ⟨q', hq'U, hq'⟩ := hvV ((mem_basicOpen f (⟨r', hr'⟩ : PrimeSpectrum R)).2 hfr')
  exact ⟨q', hq'U, by rw [← comap_asIdeal, hq']⟩


/-- A commutative square whose two vertical maps and whose bottom map are bijective has a
bijective top map. -/
private lemma bijective_of_comm_square {A B C D : Type*} (u : A → B) (l : A → C) (r : B → D)
    (v : C → D) (hl : Function.Bijective l) (hr : Function.Bijective r)
    (hv : Function.Bijective v) (h : ∀ a, r (u a) = v (l a)) : Function.Bijective u := by
  refine (hr.of_comp_iff' u).mp ?_
  rw [show r ∘ u = v ∘ l from funext h]
  exact hv.comp hl

section Auxiliary

variable {S : Type u} [CommRing S] (p : Ideal S) [p.IsPrime]

/-- Every element of `p.primeCompl` acts invertibly on `X ⊗[S] p.ResidueField`, so this module
is already a localization of itself at `p.primeCompl`. -/
private lemma isLocalizedModule_id_rTensor_residueField (X : Type*) [AddCommGroup X] [Module S X] :
    IsLocalizedModule p.primeCompl
      (LinearMap.id : X ⊗[S] p.ResidueField →ₗ[S] X ⊗[S] p.ResidueField) where
  map_units s := by
    have := isLocalizedModule_id p.primeCompl p.ResidueField (Localization.AtPrime p)
    have h : IsUnit (algebraMap S (Module.End S p.ResidueField) s) :=
      IsLocalizedModule.map_units (LinearMap.id : p.ResidueField →ₗ[S] p.ResidueField) s
    have := h.map (Module.End.lTensorAlgHom S p.ResidueField X)
    rwa [AlgHom.commutes] at this
  surj x := ⟨(x, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congrArg _ h⟩

/-- Base changing the localization map `X → X_p` to the residue field of `p` gives a bijection. -/
private lemma bijective_rTensor_residueField_mkLinearMap
    (X : Type*) [AddCommGroup X] [Module S X] :
    Function.Bijective (LinearMap.rTensor p.ResidueField
      (LocalizedModule.mkLinearMap p.primeCompl X)) := by
  have h₁ := isLocalizedModule_id_rTensor_residueField p X
  have h₂ : IsLocalizedModule p.primeCompl (LinearMap.rTensor p.ResidueField
      (LocalizedModule.mkLinearMap p.primeCompl X)) :=
    inferInstanceAs (IsLocalizedModule p.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor S p.ResidueField
        (LocalizedModule.mkLinearMap p.primeCompl X)))
  set e := IsLocalizedModule.linearEquiv p.primeCompl
    (LinearMap.id : X ⊗[S] p.ResidueField →ₗ[S] X ⊗[S] p.ResidueField)
    (LinearMap.rTensor p.ResidueField (LocalizedModule.mkLinearMap p.primeCompl X))
  have hfun : (LinearMap.rTensor p.ResidueField (LocalizedModule.mkLinearMap p.primeCompl X) :
      X ⊗[S] p.ResidueField → _) = e :=
    funext fun x ↦ (IsLocalizedModule.linearEquiv_apply p.primeCompl _ _ x).symm
  rw [hfun]
  exact e.bijective

end Auxiliary

/-- If the localization of `α` at a prime `p` is bijective, then so is its base change to the
residue field of `p`. -/
public theorem LinearMap.bijective_rTensor_residueField_of_bijective_localizedMap
    {S : Type u} [CommRing S] (p : Ideal S) [p.IsPrime]
    {M : Type v} [AddCommGroup M] [Module S M] {M' : Type w} [AddCommGroup M'] [Module S M']
    (α : M →ₗ[S] M') (h : Function.Bijective (LocalizedModule.map p.primeCompl α)) :
    Function.Bijective (LinearMap.rTensor p.ResidueField α) := by
  set K := p.ResidueField
  set αp := (LocalizedModule.map p.primeCompl α).restrictScalars S with hαp
  refine bijective_of_comm_square _
    (LinearMap.rTensor K (LocalizedModule.mkLinearMap p.primeCompl M))
    (LinearMap.rTensor K (LocalizedModule.mkLinearMap p.primeCompl M'))
    (LinearMap.rTensor K αp)
    (bijective_rTensor_residueField_mkLinearMap p M)
    (bijective_rTensor_residueField_mkLinearMap p M') ?_ ?_
  · have hb : Function.Bijective αp := h
    have : (LinearMap.rTensor K αp : _ → _) = (LinearEquiv.ofBijective αp hb).rTensor K := rfl
    rw [this]
    exact (LinearEquiv.ofBijective αp hb).rTensor K |>.bijective
  · intro a
    have hcomp : (LinearMap.rTensor K (LocalizedModule.mkLinearMap p.primeCompl M')) ∘ₗ
        (LinearMap.rTensor K α) = (LinearMap.rTensor K αp) ∘ₗ
          (LinearMap.rTensor K (LocalizedModule.mkLinearMap p.primeCompl M)) := by
      rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
      congr 1
      ext x
      simp [hαp]
    exact LinearMap.congr_fun hcomp a


private theorem mapQ_aux (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] [(Ideal.map (algebraMap R S) (q.under R)).IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : Function.Injective
      (alpha.rTensor (Ideal.map (algebraMap R S) (q.under R)).ResidueField))
    (u : LocalizedModule (q.under R).primeCompl (Fin n → S) →ₗ[R] LocalizedModule q.primeCompl N)
    (hu : u ∘ₗ LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S) =
      ((LocalizedModule.mkLinearMap q.primeCompl N).comp alpha).restrictScalars R)
    (z : LocalizedModule (q.under R).primeCompl (Fin n → S))
    (hz : u z ∈ (q.under R) • (⊤ : Submodule R (LocalizedModule q.primeCompl N))) :
    z ∈ (q.under R) • (⊤ : Submodule R (LocalizedModule (q.under R).primeCompl (Fin n → S))) := by
  classical
  have hpq : Ideal.map (algebraMap R S) (q.under R) ≤ q := Ideal.map_comap_le
  have hun : ∀ s : q.primeCompl, IsUnit (algebraMap S (Module.End S
      ((Ideal.map (algebraMap R S) (q.under R)).ResidueField ⊗[S] N)) (s : S)) := by
    intro s
    have hs : IsUnit (algebraMap S (Ideal.map (algebraMap R S) (q.under R)).ResidueField
        (s : S)) := by
      refine isUnit_iff_ne_zero.mpr fun h => s.2 (hpq ?_)
      exact Ideal.algebraMap_residueField_eq_zero.mp h
    refine (Module.End.isUnit_iff _).mpr ?_
    change Function.Bijective
      (fun z : (Ideal.map (algebraMap R S) (q.under R)).ResidueField ⊗[S] N => (s : S) • z)
    have he : (fun z : (Ideal.map (algebraMap R S) (q.under R)).ResidueField ⊗[S] N =>
          (s : S) • z) =
        (fun z : (Ideal.map (algebraMap R S) (q.under R)).ResidueField ⊗[S] N =>
          algebraMap S (Ideal.map (algebraMap R S) (q.under R)).ResidueField (s : S) • z) :=
      funext fun z => (IsScalarTower.algebraMap_smul _ (s : S) z).symm
    rw [he]
    exact hs.smul_bijective
  have htkill : ∀ y ∈ (q.under R) • (⊤ : Submodule R (LocalizedModule q.primeCompl N)),
      LocalizedModule.lift q.primeCompl (TensorProduct.mk S
        (Ideal.map (algebraMap R S) (q.under R)).ResidueField N 1) hun y = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    intro c hc y _
    rw [← IsScalarTower.algebraMap_smul S c y, map_smul, ← IsScalarTower.algebraMap_smul
      (Ideal.map (algebraMap R S) (q.under R)).ResidueField,
      show algebraMap S (Ideal.map (algebraMap R S) (q.under R)).ResidueField
          (algebraMap R S c) = 0 from
        Ideal.algebraMap_residueField_eq_zero.mpr (Ideal.mem_map_of_mem _ hc), zero_smul]
  revert hz
  refine LocalizedModule.induction_on (fun x s => ?_) z
  intro hz
  have hs1 : (s : R) • (LocalizedModule.mk x s :
      LocalizedModule (q.under R).primeCompl (Fin n → S)) = LocalizedModule.mk x 1 := by
    rw [LocalizedModule.smul'_mk]
    simpa [Submonoid.smul_def] using LocalizedModule.mk_cancel s x
  have huv : u (LocalizedModule.mk x 1) = LocalizedModule.mk (alpha x) 1 := by
    simpa using LinearMap.congr_fun hu x
  have hqx : (LocalizedModule.mk (alpha x) 1 : LocalizedModule q.primeCompl N) ∈
      (q.under R) • (⊤ : Submodule R (LocalizedModule q.primeCompl N)) := by
    rw [← huv, ← hs1, map_smul]
    exact Submodule.smul_mem _ _ hz
  have hz0 : (1 : (Ideal.map (algebraMap R S) (q.under R)).ResidueField) ⊗ₜ[S] alpha x = 0 := by
    have he := LinearMap.congr_fun (LocalizedModule.lift_comp q.primeCompl (TensorProduct.mk S
      (Ideal.map (algebraMap R S) (q.under R)).ResidueField N 1) hun) (alpha x)
    exact he.symm.trans (htkill _ hqx)
  have hxx : (1 : (Ideal.map (algebraMap R S) (q.under R)).ResidueField) ⊗ₜ[S] x = 0 := by
    apply (LinearMap.lTensor_inj_iff_rTensor_inj _ alpha).mpr halpha
    simpa using hz0
  have hm3 : x ∈ (q.under R) • (⊤ : Submodule R (Fin n → S)) :=
    (Ideal.mem_map_smul_top_iff (R' := S) (q.under R) x).mp
      (Module.mem_smul_top_of_tmul_zero S (Ideal.map (algebraMap R S) (q.under R)) n x hxx)
  have hmk : (LocalizedModule.mk x 1 :
      LocalizedModule (q.under R).primeCompl (Fin n → S)) ∈
      (q.under R) • (⊤ : Submodule R
        (LocalizedModule (q.under R).primeCompl (Fin n → S))) := by
    refine Submodule.smul_induction_on (p := fun y =>
      (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S) y) ∈
        (q.under R) • (⊤ : Submodule R
          (LocalizedModule (q.under R).primeCompl (Fin n → S)))) hm3 ?_ ?_
    · intro c hc y _
      rw [map_smul]
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  rw [← Ideal.mem_map_smul_top_iff (R' := Localization.AtPrime (q.under R))] at hmk ⊢
  obtain ⟨v, hv⟩ := IsLocalization.map_units (Localization.AtPrime (q.under R)) s
  have hvs : (LocalizedModule.mk x s : LocalizedModule (q.under R).primeCompl (Fin n → S)) =
      (↑v⁻¹ : Localization.AtPrime (q.under R)) • LocalizedModule.mk x 1 := by
    rw [← hs1, ← algebraMap_smul (Localization.AtPrime (q.under R)) (s : R)
      (LocalizedModule.mk x s : LocalizedModule (q.under R).primeCompl (Fin n → S)), ← hv,
      smul_smul, Units.inv_mul, one_smul]
  rw [hvs]
  exact Submodule.smul_mem _ _ hmk

/-- Let `R → S` be a flat ring map of finite presentation with geometrically integral fibres,
let `q ⊆ S` be a prime lying over `r = q ∩ R`, write `p = rS` for the generic point of the fibre
over `r`, let `N` be a finite `S`-module and let `alpha : S^{⊕ n} → N` become injective over
`κ(p)`. If `N_q` is flat over `R` then `alpha_r : S_r^{⊕ n} → N_r` is universally injective as a
map of `R`-modules. -/
@[stacks 05IA "the implication (1) ⟹ (3), the universal injectivity of `α_𝔯` over `R_𝔯`"]
public theorem Module.universallyInjective_localizedMap_of_flat_localizedModule
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
      Function.Injective (alpha.rTensor
        (Ideal.map (algebraMap R S) (q.under R)).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (Q : Type (max u w)) [AddCommGroup Q] [Module R Q] :
    Function.Injective (((LocalizedModule.map (q.under R).primeCompl
      (alpha.restrictScalars R)).restrictScalars R).rTensor Q) := by
  classical
  have hp : (Ideal.map (algebraMap R S) (q.under R)).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
  have : Module.Projective R S :=
    Algebra.projective_of_geometricallyIntegral_fibres
      (Algebra.isGeometricallyIntegral_tensorProduct_residueField R S)
  have : Module.Projective R (Fin n → S) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype :
      (Π₀ _ : Fin n, S) ≃ₗ[R] (Fin n → S))
  have : Module.Projective (Localization.AtPrime (q.under R))
      (LocalizedModule (q.under R).primeCompl (Fin n → S)) :=
    Module.Projective.of_equiv'
      (LocalizedModule.equivTensorProduct (q.under R).primeCompl (Fin n → S)).symm
  have hid := isLocalizedModule_id (q.under R).primeCompl (LocalizedModule q.primeCompl N)
    (Localization.AtPrime (q.under R))
  have : Module.Flat (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl N) :=
    Module.Flat.of_isLocalizedModule (Localization.AtPrime (q.under R))
      (q.under R).primeCompl LinearMap.id
  have hunits : ∀ s : (q.under R).primeCompl,
      IsUnit (algebraMap R (Module.End R (LocalizedModule q.primeCompl N)) (s : R)) := fun s =>
    IsLocalizedModule.map_units
      (LinearMap.id : LocalizedModule q.primeCompl N →ₗ[R] LocalizedModule q.primeCompl N) s
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : LocalizedModule (q.under R).primeCompl (Fin n → S) →ₗ[R]
      LocalizedModule q.primeCompl N,
      u₀ ∘ₗ LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S) =
        ((LocalizedModule.mkLinearMap q.primeCompl N).comp alpha).restrictScalars R :=
    ⟨IsLocalizedModule.lift (q.under R).primeCompl
        (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S))
        (((LocalizedModule.mkLinearMap q.primeCompl N).comp alpha).restrictScalars R) hunits,
      IsLocalizedModule.lift_comp (q.under R).primeCompl
        (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S))
        (((LocalizedModule.mkLinearMap q.primeCompl N).comp alpha).restrictScalars R) hunits⟩
  have hmapQ : Function.Injective (Submodule.mapQ
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)) •
        (⊤ : Submodule (Localization.AtPrime (q.under R))
          (LocalizedModule (q.under R).primeCompl (Fin n → S))))
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)) •
        (⊤ : Submodule (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl N)))
      (LinearMap.extendScalarsOfIsLocalization (q.under R).primeCompl
        (Localization.AtPrime (q.under R)) u₀)
      (Submodule.smul_top_le_comap_smul_top _ _)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)) •
        (⊤ : Submodule (Localization.AtPrime (q.under R))
          (LocalizedModule (q.under R).primeCompl (Fin n → S)))) z
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q.under R)
      (Localization.AtPrime (q.under R)), Ideal.mem_map_smul_top_iff] at hz ⊢
    exact mapQ_aux R S q N n alpha halpha u₀ hu₀ z hz
  have hengine := Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal'
    (LinearMap.extendScalarsOfIsLocalization (q.under R).primeCompl
      (Localization.AtPrime (q.under R)) u₀) hmapQ
  have hu₀inj : Function.Injective (u₀.rTensor Q) :=
    (LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization (q.under R).primeCompl
      (Localization.AtPrime (q.under R))
      (LocalizedModule.mkLinearMap (q.under R).primeCompl Q) u₀).mpr
      (hengine (LocalizedModule (q.under R).primeCompl Q))
  have hfact : u₀ = (IsLocalizedModule.lift (q.under R).primeCompl
      (LocalizedModule.mkLinearMap (q.under R).primeCompl N)
      ((LocalizedModule.mkLinearMap q.primeCompl N).restrictScalars R) hunits) ∘ₗ
      ((LocalizedModule.map (q.under R).primeCompl
        (alpha.restrictScalars R)).restrictScalars R) := by
    rw [← IsLocalizedModule.lift_unique (q.under R).primeCompl
      (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S)) _ hunits u₀ hu₀]
    refine IsLocalizedModule.lift_unique (q.under R).primeCompl
      (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S)) _ hunits _ ?_
    refine LinearMap.ext fun y => ?_
    have h1 := LinearMap.congr_fun (IsLocalizedModule.lift_comp (q.under R).primeCompl
      (LocalizedModule.mkLinearMap (q.under R).primeCompl N)
      ((LocalizedModule.mkLinearMap q.primeCompl N).restrictScalars R) hunits) (alpha y)
    simpa [LocalizedModule.map_mk] using h1
  rw [hfact, LinearMap.rTensor_comp] at hu₀inj
  exact Function.Injective.of_comp hu₀inj

private theorem primeCompl_under_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (r : Ideal R) [r.IsPrime] (h : q.under R = r) :
    (q.under R).primeCompl = r.primeCompl := by
  subst h
  rfl

/-- In the situation of `Module.universallyInjective_localizedMap_of_flat_localizedModule`, with
`N` finitely presented and `alpha` an isomorphism over `κ(p)`, there is an `f ∈ R`, `f ∉ r`, such
that `alpha_f : S_f^{⊕ n} → N_f` is universally injective as a map of `R`-modules. -/
@[stacks 05IA "the first half of the implication (1) ⟹ (2), the universal injectivity of `α_f`"]
public theorem Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (r : Ideal R) [r.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.under R = r)
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Bijective (alpha.rTensor (Ideal.map (algebraMap R S) r).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    ∃ f ∈ r.primeCompl, ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
        Function.Injective (((LocalizedModule.map (Submonoid.powers f)
          (alpha.restrictScalars R)).restrictScalars R).rTensor Q) := by
  classical
  subst hq
  have hp : (Ideal.map (algebraMap R S) (q.under R)).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
  have hcomap : ∀ r' : Ideal R,
      (Ideal.map (algebraMap R S) r').comap (algebraMap R S) = r' :=
    Ideal.comap_map_of_geometricallyIrreducible R S
  have hU1 : IsOpen {q' : PrimeSpectrum S |
      Module.Flat R (LocalizedModule.AtPrime q'.asIdeal N)} :=
    Module.isOpen_setOf_flat_localizedModule_atPrime
  have hU2 : IsOpen {q' : PrimeSpectrum S |
      Function.Bijective (LocalizedModule.map q'.asIdeal.primeCompl alpha)} :=
    LinearMap.isOpen_setOf_localizedMap_atPrime_bijective alpha
  have hpq : Ideal.map (algebraMap R S) (q.under R) ≤ q := Ideal.map_comap_le
  have hspec : ∀ (U : Set (PrimeSpectrum S)), IsOpen U → ∀ (a b : PrimeSpectrum S),
      a.asIdeal ≤ b.asIdeal → b ∈ U → a ∈ U := fun U hU a b hab hb =>
    Specializes.mem_open ((PrimeSpectrum.le_iff_specializes a b).mp hab) hU hb
  have hpU1 : Module.Flat R (LocalizedModule.AtPrime
      (Ideal.map (algebraMap R S) (q.under R)) N) :=
    hspec _ hU1 ⟨Ideal.map (algebraMap R S) (q.under R), hp⟩ ⟨q, ‹_›⟩ hpq hflat
  have hcore := Module.universallyInjective_localizedMap_of_flat_localizedModule R S q N n
    alpha halpha.1 hflat
  have hpbij : Function.Bijective
      (LocalizedModule.map (Ideal.map (algebraMap R S) (q.under R)).primeCompl alpha) := by
    have hnest : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
        Function.Injective (((LocalizedModule.map
          (Ideal.map (algebraMap R S) (q.under R)).primeCompl alpha).restrictScalars R).rTensor
          Q) := by
      refine Module.injective_rTensor_localizedMap_atPrime_of_under alpha
        (Ideal.map (algebraMap R S) (q.under R)) ?_
      rw [primeCompl_under_eq (R := R) (Ideal.map (algebraMap R S) (q.under R)) (q.under R)
        (hcomap _)]
      exact hcore
    exact ⟨Module.injective_of_rTensor_injective
      ((LocalizedModule.map (Ideal.map (algebraMap R S) (q.under R)).primeCompl
          alpha).restrictScalars R) hnest,
      Module.localized_surjective_of_residue_surjective S _ _ N alpha halpha.2⟩
  obtain ⟨f, hfr, hf⟩ := PrimeSpectrum.exists_notMem_forall_exists_mem_comap_of_isOpen
    ({q' : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q'.asIdeal N)} ∩
      {q' : PrimeSpectrum S |
        Function.Bijective (LocalizedModule.map q'.asIdeal.primeCompl alpha)})
    (hU1.inter hU2) (q.under R) ⟨Ideal.map (algebraMap R S) (q.under R), hp⟩
    ⟨hpU1, hpbij⟩ (hcomap _)
  refine ⟨f, hfr, ?_⟩
  have key : ∀ (r' : Ideal R) [r'.IsPrime], f ∉ r'.comap (algebraMap R R) →
      UniversallyInjective.{u} (A := R) (localizedMapR (alpha.restrictScalars R) r') := by
    intro r' hr' hfr'
    obtain ⟨q'', ⟨hq''1, hq''2⟩, hq''⟩ := hf r' hr' (by simpa using hfr')
    have hur : q''.asIdeal.under R = r' := hq''
    have hpr : (Ideal.map (algebraMap R S) (q''.asIdeal.under R)).IsPrime :=
      Ideal.isPrime_map_of_geometricallyIntegral R S _
    have hle : Ideal.map (algebraMap R S) (q''.asIdeal.under R) ≤ q''.asIdeal :=
      Ideal.map_comap_le
    have hp'U2 : Function.Bijective (LocalizedModule.map
        (Ideal.map (algebraMap R S) (q''.asIdeal.under R)).primeCompl alpha) :=
      hspec _ hU2 ⟨Ideal.map (algebraMap R S) (q''.asIdeal.under R), hpr⟩ q'' hle hq''2
    have hres := LinearMap.bijective_rTensor_residueField_of_bijective_localizedMap _ alpha
      hp'U2
    have hcore' := Module.universallyInjective_localizedMap_of_flat_localizedModule R S
      q''.asIdeal N n alpha hres.1 hq''1
    rw [primeCompl_under_eq (R := R) q''.asIdeal r' hur] at hcore'
    exact hcore'
  have := Module.universallyInjective_localizedModule_away_of_forall_primes (R := R) (S := R)
    (alpha.restrictScalars R) f key
  intro Q _ _
  simpa using this Q

/-- For a finitely presented ring map `R → S` and a finitely presented `S`-module `X`, if
`X_{q'}` is flat over `R` for every prime `q'` of `S` missing `g`, then `X_g` is flat over `R`. -/
public theorem Module.flat_localizedModule_away_of_forall_flat_localizedModule_atPrime
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (X : Type u) [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    [Module.FinitePresentation S X] (g : S)
    (hg : ∀ q' : PrimeSpectrum S, g ∉ q'.asIdeal →
      Module.Flat R (LocalizedModule.AtPrime q'.asIdeal X)) :
    Module.Flat R (LocalizedModule.Away g X) := by
  refine Module.flat_of_isLocalized_maximal (Localization.Away g) (LocalizedModule.Away g X)
    (fun P _ => LocalizedModule P.primeCompl (LocalizedModule.Away g X))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule.Away g X)) ?_
  intro P hP
  have hcomp := IsLocalizedModule.comp_atPrime_of_isLocalization (Submonoid.powers g)
    (Localization.Away g) P (LocalizedModule.mkLinearMap (Submonoid.powers g) X)
    (LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule.Away g X))
  have hpc : (P.comap (algebraMap S (Localization.Away g))).IsPrime := Ideal.comap_isPrime _ _
  have hgP : g ∉ P.comap (algebraMap S (Localization.Away g)) :=
    IsLocalization.algebraMap_mem_primeCompl (Submonoid.powers g) (Localization.Away g) P
      ⟨g, Submonoid.mem_powers g⟩
  have hflat := hg ⟨P.comap (algebraMap S (Localization.Away g)), hpc⟩ hgP
  exact (Module.Flat.equiv_iff ((IsLocalizedModule.linearEquiv
    (P.comap (algebraMap S (Localization.Away g))).primeCompl
    (LocalizedModule.mkLinearMap (P.comap (algebraMap S (Localization.Away g))).primeCompl X)
    (((LocalizedModule.mkLinearMap P.primeCompl
        (LocalizedModule.Away g X)).restrictScalars S) ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers g) X)).restrictScalars R)).mp hflat

/-- In the situation of `Module.universallyInjective_localizedMap_of_flat_localizedModule` the
localization of `Coker(alpha)` at `q` is flat over `R`. -/
@[stacks 05IA "the flatness of `Coker(α)_𝔮`, the second half of conditions (3) to (6)"]
public theorem Module.flat_localizedModule_coker_of_flat_localizedModule
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
      Function.Injective (alpha.rTensor
        (Ideal.map (algebraMap R S) (q.under R)).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)) := by
  have hex : Function.Exact ((LocalizedModule.map q.primeCompl alpha).restrictScalars R)
      ((LocalizedModule.map q.primeCompl (LinearMap.range alpha).mkQ).restrictScalars R) :=
    LocalizedModule.map_exact q.primeCompl alpha (LinearMap.range alpha).mkQ
      alpha.exact_map_mkQ_range
  have hsurj : Function.Surjective
      ((LocalizedModule.map q.primeCompl (LinearMap.range alpha).mkQ).restrictScalars R) :=
    LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective (LinearMap.range alpha))
  exact (Module.flat_of_middle_flat_of_rTensor_injective _ _ hsurj hex
    (Module.injective_rTensor_localizedMap_atPrime_of_under alpha q
      (Module.universallyInjective_localizedMap_of_flat_localizedModule R S q N n alpha
        halpha hflat))).2

/-- In the situation of `Module.universallyInjective_localizedMap_of_flat_localizedModule`, with
`N` finitely presented, there is a `g ∈ S`, `g ∉ q`, such that `Coker(alpha)_g` is flat over
`R`. -/
public theorem Module.exists_flat_localizedModule_away_coker_of_flat_localizedModule
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
      Function.Injective (alpha.rTensor
        (Ideal.map (algebraMap R S) (q.under R)).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    ∃ g ∈ q.primeCompl,
      Module.Flat R (LocalizedModule.Away g (N ⧸ LinearMap.range alpha)) := by
  have hfp : Module.FinitePresentation S (N ⧸ LinearMap.range alpha) :=
    Module.finitePresentation_of_surjective (LinearMap.range alpha).mkQ
      (Submodule.mkQ_surjective _) (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range alpha)
  have hU3 : IsOpen {q' : PrimeSpectrum S | Module.Flat R
      (LocalizedModule.AtPrime q'.asIdeal (N ⧸ LinearMap.range alpha))} :=
    Module.isOpen_setOf_flat_localizedModule_atPrime
  have hq3 : (⟨q, ‹_›⟩ : PrimeSpectrum S) ∈ {q' : PrimeSpectrum S | Module.Flat R
      (LocalizedModule.AtPrime q'.asIdeal (N ⧸ LinearMap.range alpha))} :=
    Module.flat_localizedModule_coker_of_flat_localizedModule R S q N n alpha halpha hflat
  obtain ⟨v, ⟨g, rfl⟩, hqv, hvU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq3 hU3
  exact ⟨g, (PrimeSpectrum.mem_basicOpen g _).1 hqv,
    Module.flat_localizedModule_away_of_forall_flat_localizedModule_atPrime R S _ g
      fun q' hgq' => hvU ((PrimeSpectrum.mem_basicOpen g q').2 hgq')⟩


/-- Let `R → S` be a flat ring map of finite presentation with geometrically integral fibres,
let `q ⊆ S` be a prime lying over `r = q ∩ R`, write `p = rS`, let `N` be a finitely presented
`S`-module and let `alpha : S^{⊕ n} → N` be an isomorphism over `κ(p)`. If `N_q` is flat over `R`
then there are an `f ∈ R`, `f ∉ r`, such that `alpha_f` is universally injective as a map of
`R`-modules, and a `g ∈ S`, `g ∉ q`, such that `Coker(alpha)_g` is flat over `R`. -/
@[stacks 05IA "the implication (1) ⟹ (2)"]
public theorem Module.exists_universallyInjective_and_flat_coker_of_flat_localizedModule
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
      Function.Bijective (alpha.rTensor
        (Ideal.map (algebraMap R S) (q.under R)).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    (∃ f ∈ (q.under R).primeCompl, ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
        Function.Injective (((LocalizedModule.map (Submonoid.powers f)
          (alpha.restrictScalars R)).restrictScalars R).rTensor Q)) ∧
      ∃ g ∈ q.primeCompl, Module.Flat R (LocalizedModule.Away g (N ⧸ LinearMap.range alpha)) :=
  ⟨Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule R S
      (q.under R) q rfl N n alpha halpha hflat,
    Module.exists_flat_localizedModule_away_coker_of_flat_localizedModule R S q N n alpha
      halpha.1 hflat⟩

/-! ### Elements of `S` outside the generic point of the fibre over `r` -/

/-- If `Spec S → Spec R` has geometrically integral fibres, then so does `Spec S' → Spec R'`,
where `R'` is the localization of `R` at `P` and `S'` is the localization of `S` at the image of
`P`. -/
public theorem AlgebraicGeometry.geometricallyIntegral_spec_of_isLocalization (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (P : Submonoid R)
    (R' S' : Type u) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S']
    [IsLocalization P R'] [IsLocalization (Algebra.algebraMapSubmonoid S P) S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap R' S'))) := by
  have hcomm : (algebraMap R' S').comp (algebraMap R R') =
      (algebraMap S S').comp (algebraMap R S) := by
    ext x
    simp [← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Submonoid.map (algebraMap R S) P) S' := ‹_›
  exact MorphismProperty.of_isPullback (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap R S) (algebraMap R' S') hcomm P)) ‹_›

/-- For a flat ring map `R → S` of finite presentation with geometrically integral fibres and a
prime `𝔯` of `R`, an element of `S` outside the generic point `𝔭 = 𝔯S` of the fibre over `𝔯`
becomes a nonzerodivisor in the localization of `S` at `𝔯`. -/
public theorem Algebra.mem_nonZeroDivisors_localization_of_notMem_map (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime]
    (s : S) (hs : s ∉ Ideal.map (algebraMap R S) r) :
    algebraMap S (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) s ∈
      nonZeroDivisors (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) := by
  have hp : (Ideal.map (algebraMap R S) r).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S r
  have := isLocalizedModule_id r.primeCompl
    (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) (Localization.AtPrime r)
  have : GeometricallyIntegral (Spec.map (ofHom (algebraMap (Localization.AtPrime r)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl))))) :=
    AlgebraicGeometry.geometricallyIntegral_spec_of_isLocalization R S r.primeCompl _ _
  have : Algebra.FinitePresentation (Localization.AtPrime r)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) :=
    Algebra.finitePresentation_of_isLocalization R S r.primeCompl _ _
  have : Module.Flat R (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) :=
    Module.Flat.trans R S _
  have : Module.Flat (Localization.AtPrime r)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) :=
    Module.Flat.of_isLocalizedModule (Localization.AtPrime r) r.primeCompl
      (LinearMap.id (R := R)
        (M := Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))
  have : Module.Projective (Localization.AtPrime r)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) :=
    Algebra.projective_of_geometricallyIntegral_fibres
      (Algebra.isGeometricallyIntegral_tensorProduct_residueField _ _)
  have : (Ideal.map (algebraMap (Localization.AtPrime r)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime r))).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral _ _
      (IsLocalRing.maximalIdeal (Localization.AtPrime r))
  have hPeq : Ideal.map (algebraMap (Localization.AtPrime r)
        (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))
        (IsLocalRing.maximalIdeal (Localization.AtPrime r))
      = Ideal.map (algebraMap S (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))
        (Ideal.map (algebraMap R S) r) :=
    Ideal.map_maximalIdeal_eq_map_map_of_isLocalization R S r _ _
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid S r.primeCompl : Submonoid S) : Set S)
      ((Ideal.map (algebraMap R S) r : Ideal S) : Set S) :=
    Set.disjoint_left.mpr fun a ha hb =>
      Algebra.algebraMapSubmonoid_le_primeCompl_map R S r ha hb
  have hunder := IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S r.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) hp hdisj
  have hsP : algebraMap S (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) s ∉
      Ideal.map (algebraMap (Localization.AtPrime r)
        (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))
        (IsLocalRing.maximalIdeal (Localization.AtPrime r)) := by
    rw [hPeq]
    intro hmem
    exact hs (hunder ▸ (Ideal.mem_comap.mpr hmem))
  have hinj := Module.mul_injective_of_notMem_closedFiber (Localization.AtPrime r)
    (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)) _ rfl _ hsP
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => hinj (by simpa using hx),
    fun x hx => hinj (by simpa [mul_comm] using hx)⟩

/-! ### The kernel criterion for injectivity of a localized map -/

/-- An element whose class `z / 1` in the localization at `W` vanishes is killed by an element
of `W`. -/
private lemma exists_mem_smul_eq_zero_of_mk_one_eq_zero {S : Type*} [CommRing S]
    (W : Submonoid S) {M : Type*} [AddCommGroup M] [Module S M] (z : M)
    (hmk : (LocalizedModule.mk z 1 : LocalizedModule W M) = 0) : ∃ c ∈ W, c • z = 0 := by
  rw [← LocalizedModule.zero_mk (1 : W), LocalizedModule.mk_eq] at hmk
  obtain ⟨u, hu⟩ := hmk
  exact ⟨(u : S), u.2, by simpa only [Submonoid.smul_def, one_smul, smul_zero] using hu⟩

/-- The kernel of a map whose localization at `W` is injective is `W`-torsion: an element killed
by the map is killed by an element of `W`. -/
private lemma exists_mem_smul_eq_zero_of_injective_localizedMap {S : Type*} [CommRing S]
    (W : Submonoid S) {M M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup M']
    [Module S M'] (α : M →ₗ[S] M') (h : Function.Injective (LocalizedModule.map W α)) (z : M)
    (hz : α z = 0) : ∃ c ∈ W, c • z = 0 :=
  exists_mem_smul_eq_zero_of_mk_one_eq_zero W z
    (h (by rw [LocalizedModule.map_mk, hz, LocalizedModule.zero_mk, map_zero]))

/-- Conversely, a map whose kernel is `W`-torsion has injective localization at `W`. -/
private lemma injective_localizedMap_of_forall_exists_mem_smul_eq_zero {S : Type*} [CommRing S]
    (W : Submonoid S) {M M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup M']
    [Module S M'] (α : M →ₗ[S] M') (h : ∀ z : M, α z = 0 → ∃ c ∈ W, c • z = 0) :
    Function.Injective (LocalizedModule.map W α) := by
  rw [injective_iff_map_eq_zero]
  intro x
  induction x using LocalizedModule.induction_on with
  | _ a w =>
    intro hx
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : W), LocalizedModule.mk_eq] at hx
    obtain ⟨u, hu⟩ := hx
    have hz : α ((u : S) • a) = 0 := by
      simpa only [Submonoid.smul_def, one_smul, smul_zero, map_smul] using hu
    obtain ⟨c, hc, hcz⟩ := h _ hz
    rw [← LocalizedModule.zero_mk (1 : W), LocalizedModule.mk_eq]
    refine ⟨⟨c * (u : S), mul_mem hc u.2⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul, smul_zero]
    rw [mul_smul]
    exact hcz

/-- Injectivity of a localized map passes to any larger multiplicative set, the localization at
the larger set being a localization of the first one. -/
private lemma injective_localizedMap_of_le {S : Type*} [CommRing S] {W₁ W₂ : Submonoid S}
    (hle : W₁ ≤ W₂) {M M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup M']
    [Module S M'] (α : M →ₗ[S] M') (h : Function.Injective (LocalizedModule.map W₁ α)) :
    Function.Injective (LocalizedModule.map W₂ α) :=
  injective_localizedMap_of_forall_exists_mem_smul_eq_zero W₂ α fun z hz => by
    obtain ⟨c, hc, hcz⟩ := exists_mem_smul_eq_zero_of_injective_localizedMap W₁ α h z hz
    exact ⟨c, hle hc, hcz⟩

/-- Injectivity of the localization of `α` at a multiplicative set `W₁` of the base `R` gives
injectivity of its localization at the image of `W₁` in `S`: inverting the elements of `W₁` and
inverting their images are the same localization. -/
private lemma injective_localizedMap_algebraMapSubmonoid {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (W₁ : Submonoid R) {M M' : Type*} [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (α : M →ₗ[S] M')
    (h : Function.Injective (LocalizedModule.map W₁ (α.restrictScalars R))) :
    Function.Injective (LocalizedModule.map (Algebra.algebraMapSubmonoid S W₁) α) :=
  injective_localizedMap_of_forall_exists_mem_smul_eq_zero _ α fun z hz => by
    obtain ⟨c, hc, hcz⟩ := exists_mem_smul_eq_zero_of_injective_localizedMap W₁
      (α.restrictScalars R) h z hz
    exact ⟨algebraMap R S c, ⟨c, hc, rfl⟩, by rw [IsScalarTower.algebraMap_smul]; exact hcz⟩

/-- Multiplication by an element of `S` outside the generic point `𝔭 = 𝔯S` of the fibre over `𝔯`
is injective on the localization at `𝔯` of an `S`-module which is flat over `S`. -/
private lemma isSMulRegular_localizedModule_of_notMem_map (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime]
    (X : Type w) [AddCommGroup X] [Module S X] [Module.Flat S X] (s : S)
    (hs : s ∉ Ideal.map (algebraMap R S) r) :
    IsSMulRegular (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) X) s := by
  have : Module.Flat (Localization (Algebra.algebraMapSubmonoid S r.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) X) :=
    Module.Flat.of_isLocalizedModule _ (Algebra.algebraMapSubmonoid S r.primeCompl)
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S r.primeCompl) X)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) X)
    (Algebra.mem_nonZeroDivisors_localization_of_notMem_map R S r s hs)
  intro x y hxy
  exact hreg (by simpa only [IsScalarTower.algebraMap_smul] using hxy)

/-- If the localization `α_𝔭` of `α` at the generic point `𝔭 = 𝔯S` of the fibre over `𝔯` is
injective then so is its localization at `𝔯`. -/
private lemma injective_localizedMap_algebraMapSubmonoid_of_injective_map (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime]
    {M : Type v} [AddCommGroup M] [Module S M] [Module.Flat S M] {M' : Type w} [AddCommGroup M']
    [Module S M'] (α : M →ₗ[S] M')
    (h : letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Injective (LocalizedModule.map (Ideal.map (algebraMap R S) r).primeCompl α)) :
    Function.Injective (LocalizedModule.map (Algebra.algebraMapSubmonoid S r.primeCompl) α) := by
  have hp : (Ideal.map (algebraMap R S) r).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S r
  refine injective_localizedMap_of_forall_exists_mem_smul_eq_zero _ α fun z hz => ?_
  obtain ⟨t, ht, htz⟩ := exists_mem_smul_eq_zero_of_injective_localizedMap _ α h z hz
  have hreg := isSMulRegular_localizedModule_of_notMem_map R S r M t ht
  exact exists_mem_smul_eq_zero_of_mk_one_eq_zero _ z (hreg (by
    simp only [LocalizedModule.smul'_mk, htz, LocalizedModule.zero_mk, smul_zero]))

/-! ### The remaining implications between the six conditions -/

/-- If `alpha_f` is universally injective as a map of `R`-modules for some `f ∈ R`, `f ∉ r`, and
`Coker(alpha)_g` is `R`-flat for some `g ∈ S`, `g ∉ q`, then `alpha_r` is universally injective
as a map of `R`-modules and `Coker(alpha)_q` is `R`-flat. The prime `q` need not lie over `r`. -/
@[stacks 05IA "the implication (2) ⟹ (3)"]
public theorem Module.universallyInjective_localizedMap_and_flat_coker_of_exists_away
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : Ideal R) [r.IsPrime]
    (q : Ideal S) [q.IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] (n : ℕ)
    (alpha : (Fin n → S) →ₗ[S] N)
    (h : (∃ f ∈ r.primeCompl, UniversallyInjective.{max u w} (A := R)
            ((LocalizedModule.map (Submonoid.powers f)
              (alpha.restrictScalars R)).restrictScalars R)) ∧
      ∃ g ∈ q.primeCompl,
        Module.Flat R (LocalizedModule.Away g (N ⧸ LinearMap.range alpha))) :
    UniversallyInjective.{max u w} (A := R)
        ((LocalizedModule.map r.primeCompl (alpha.restrictScalars R)).restrictScalars R) ∧
      Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)) := by
  obtain ⟨⟨f, hf, hui⟩, g, hg, hflat⟩ := h
  refine ⟨fun Q _ _ => ?_, ?_⟩
  · have hle : Algebra.algebraMapSubmonoid R (Submonoid.powers f) ≤ r.primeCompl := by
      rintro x ⟨a, ha, rfl⟩
      exact Submonoid.powers_le.mpr hf ha
    exact injective_rTensor_localizedMap_of_algebraMapSubmonoid_le (R := R) (S := R)
      (alpha.restrictScalars R) (Submonoid.powers f) r.primeCompl hle Q (by simpa using hui Q)
  · have := hflat
    exact Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
      (IsLocalizedModule.liftOfLE (Submonoid.powers g) q.primeCompl
        (Submonoid.powers_le.mpr hg)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (N ⧸ LinearMap.range alpha))
        (LocalizedModule.mkLinearMap q.primeCompl (N ⧸ LinearMap.range alpha)))

/-- If `alpha_r` is universally injective as a map of `R`-modules then it is injective. -/
@[stacks 05IA "the implication (3) ⟹ (4), the injectivity of `α_𝔯`"]
public theorem Module.injective_localizedMap_of_universallyInjective_localizedMap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : Ideal R) [r.IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] (n : ℕ)
    (alpha : (Fin n → S) →ₗ[S] N)
    (h : UniversallyInjective.{max u w} (A := R)
      ((LocalizedModule.map r.primeCompl (alpha.restrictScalars R)).restrictScalars R)) :
    Function.Injective (LocalizedModule.map r.primeCompl (alpha.restrictScalars R)) :=
  Module.injective_of_rTensor_injective
    ((LocalizedModule.map r.primeCompl (alpha.restrictScalars R)).restrictScalars R) h

/-- If `alpha` is surjective over `κ(p)` and `alpha_r` is injective, then `alpha_p` is an
isomorphism at the generic point `p = rS` of the fibre over `r`. -/
@[stacks 05IA "the implication (4) ⟹ (5), the isomorphism `α_𝔭`"]
public theorem Module.bijective_localizedMap_map_of_injective_localizedMap (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Surjective (alpha.rTensor (Ideal.map (algebraMap R S) r).ResidueField))
    (hinj : Function.Injective (LocalizedModule.map r.primeCompl (alpha.restrictScalars R))) :
    letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
    Function.Bijective
      (LocalizedModule.map (Ideal.map (algebraMap R S) r).primeCompl alpha) := by
  have hp : (Ideal.map (algebraMap R S) r).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S r
  refine ⟨?_, Module.localized_surjective_of_residue_surjective S _ _ N alpha halpha⟩
  exact injective_localizedMap_of_le (Algebra.algebraMapSubmonoid_le_primeCompl_map R S r) alpha
    (injective_localizedMap_algebraMapSubmonoid r.primeCompl alpha hinj)

/-- If `alpha_p` is an isomorphism at the generic point `p = rS` of the fibre over `r` then
`alpha_q` is injective at every prime `q` of `S` lying over `r`. -/
@[stacks 05IA "the implication (5) ⟹ (6), the injectivity of `α_𝔮`"]
public theorem Module.injective_localizedMap_atPrime_of_bijective_localizedMap_map (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime]
    (q : Ideal S) [q.IsPrime] (hq : q.under R = r)
    (N : Type w) [AddCommGroup N] [Module S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (hbij : letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Bijective (LocalizedModule.map (Ideal.map (algebraMap R S) r).primeCompl alpha)) :
    Function.Injective (LocalizedModule.map q.primeCompl alpha) := by
  have hp : (Ideal.map (algebraMap R S) r).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S r
  have hle : Algebra.algebraMapSubmonoid S r.primeCompl ≤ q.primeCompl := by
    rintro x ⟨a, ha, rfl⟩ hmem
    exact ha (hq ▸ hmem)
  exact injective_localizedMap_of_le hle alpha
    (injective_localizedMap_algebraMapSubmonoid_of_injective_map R S r alpha hbij.1)

/-- For `S` flat over `R`, if `alpha_q` is injective and `Coker(alpha)_q` is `R`-flat then `N_q`
is `R`-flat. -/
@[stacks 05IA "the implication (6) ⟹ (1)"]
public theorem Module.flat_localizedModule_of_injective_localizedMap_of_flat_coker (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] (q : Ideal S) [q.IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] (n : ℕ)
    (alpha : (Fin n → S) →ₗ[S] N)
    (hinj : Function.Injective (LocalizedModule.map q.primeCompl alpha))
    (hC : Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha))) :
    Module.Flat R (LocalizedModule q.primeCompl N) := by
  have hfree : Module.Flat R (LocalizedModule q.primeCompl (Fin n → S)) := by
    have : Module.Flat S (LocalizedModule q.primeCompl (Fin n → S)) :=
      Module.Flat.trans S (Localization q.primeCompl) _
    exact Module.Flat.trans R S _
  exact flat_of_flat_of_flat ((LocalizedModule.map q.primeCompl alpha).restrictScalars R)
    ((LocalizedModule.map q.primeCompl (LinearMap.range alpha).mkQ).restrictScalars R) hinj
    (LocalizedModule.map_exact q.primeCompl alpha _ alpha.exact_map_mkQ_range)
    (LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _))

/-- Let `R → S` be a finitely presented flat ring map with geometrically integral fibres, let
`q ⊆ S` be a prime lying over `r ⊆ R`, write `p = rS` for the generic point of the fibre over `r`,
let `N` be a finitely presented `S`-module and let `alpha : S^{⊕ n} → N` become an isomorphism
over `κ(p)`. Then the following six conditions are equivalent:

1. `N_q` is `R`-flat;
2. there are an `f ∈ R`, `f ∉ r`, with `alpha_f` universally injective over `R`, and a `g ∈ S`,
   `g ∉ q`, with `Coker(alpha)_g` `R`-flat;
3. `alpha_r` is universally injective over `R` and `Coker(alpha)_q` is `R`-flat;
4. `alpha_r` is injective and `Coker(alpha)_q` is `R`-flat;
5. `alpha_p` is an isomorphism and `Coker(alpha)_q` is `R`-flat;
6. `alpha_q` is injective and `Coker(alpha)_q` is `R`-flat. -/
@[stacks 05IA "the equivalence of the six conditions"]
public theorem Module.flat_localizedModule_freeMap_tfae (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] (r : Ideal R) [r.IsPrime]
    (q : Ideal S) [q.IsPrime] (hq : q.under R = r)
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Bijective (alpha.rTensor (Ideal.map (algebraMap R S) r).ResidueField)) :
    letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
    List.TFAE [
      Module.Flat R (LocalizedModule q.primeCompl N),
      (∃ f ∈ r.primeCompl, UniversallyInjective.{u} (A := R)
            ((LocalizedModule.map (Submonoid.powers f)
              (alpha.restrictScalars R)).restrictScalars R)) ∧
        ∃ g ∈ q.primeCompl,
          Module.Flat R (LocalizedModule.Away g (N ⧸ LinearMap.range alpha)),
      UniversallyInjective.{u} (A := R)
          ((LocalizedModule.map r.primeCompl (alpha.restrictScalars R)).restrictScalars R) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Injective (LocalizedModule.map r.primeCompl (alpha.restrictScalars R)) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Bijective (LocalizedModule.map (Ideal.map (algebraMap R S) r).primeCompl alpha) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Injective (LocalizedModule.map q.primeCompl alpha) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha))] := by
  subst hq
  tfae_have 1 → 2 := fun hflat =>
    Module.exists_universallyInjective_and_flat_coker_of_flat_localizedModule R S q N n alpha
      halpha hflat
  tfae_have 2 → 3 := fun h =>
    Module.universallyInjective_localizedMap_and_flat_coker_of_exists_away R S (q.under R) q N n
      alpha h
  tfae_have 3 → 4 := fun h =>
    ⟨Module.injective_localizedMap_of_universallyInjective_localizedMap R S (q.under R) N n
      alpha h.1, h.2⟩
  tfae_have 4 → 5 := fun h =>
    ⟨Module.bijective_localizedMap_map_of_injective_localizedMap R S (q.under R) N n alpha
      halpha.2 h.1, h.2⟩
  tfae_have 5 → 6 := fun h =>
    ⟨Module.injective_localizedMap_atPrime_of_bijective_localizedMap_map R S (q.under R) q rfl
      N n alpha h.1, h.2⟩
  tfae_have 6 → 1 := fun h =>
    Module.flat_localizedModule_of_injective_localizedMap_of_flat_coker R S q N n alpha h.1 h.2
  tfae_finish

end
