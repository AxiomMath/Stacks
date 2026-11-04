module

public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.BoundedBelow
public import StacksFrontier.RingTheory.LocalCohomology.Cutoff.Attainment
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessIsLocal
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.Serre.CohenMacaulay

/-!
# Finiteness of local cohomology, II

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `Z = V(I) ⊆ Spec(A)` and let `M` be a
finite `A`-module. Write `s = s_{A,I}(M)` for the local cohomology finiteness cutoff of Tag
0BJR, which is `Stacks.LocalCohomology.localCohomologyCutoff A I M`. Assume that `A` is
universally catenary and that the formal fibres of the local rings of `A` are Cohen–Macaulay.
Then `H^i_Z(M)` is a finite `A`-module for `0 ≤ i < s`, while `H^s_Z(M)` is not finite.

The proof is the source's. Finiteness through a fixed degree is tested prime by prime after
localizing (Tag 0AW9); local cohomology commutes with the flat base change `A → (A_𝔭)^` (Tag
0ALZ) and finiteness descends along the faithfully flat map `A_𝔭 → (A_𝔭)^` (Tag 03C4), so the
question is one about the completions of the local rings of `A`. Those are Noetherian complete
local rings, hence quotients of regular complete local rings by the Cohen structure theorem
(Tag 032A); a regular local ring is Gorenstein (Tag 0AWX) and therefore its own dualizing
complex, and a dualizing complex travels along a finite ring map (Tag 0AX0), so a Noetherian
complete local ring has a dualizing complex. Over a ring with a dualizing complex, Faltings'
finiteness criterion (Tag 0EFD) says that `H^i_Z(-)` is finite for `i ≤ n` exactly when
`n < s`. Finally the two bounds of Tag 0BJT identify the cutoff after completing a
localization, which is where the hypotheses on `A` enter: they are used through
`Stacks.LocalCohomology.lt_localCohomologyCutoff_adicCompletion_localization` and
`Stacks.LocalCohomology.exists_localCohomologyCutoff_adicCompletion_localization_eq`.

## Main definitions

* `Stacks.LocalCohomology.FormalFibersAreCohenMacaulay` — the formal fibres of a Noetherian
  local ring are Cohen–Macaulay rings.
* `Stacks.LocalCohomology.localCohomologyModuleFlatBaseChangeIso` — Tag 0ALZ read on the
  cohomology modules: along a flat ring map, `H^i_{V(IB)}(B ⊗_A M)` is `B ⊗_A H^i_{V(I)}(M)`.

## Main results

The first lives in the namespace `Dualizing`, the rest in `Stacks.LocalCohomology`.

* `Dualizing.exists_isDualizingComplex_of_isAdicComplete` — a Noetherian complete local ring has
  a dualizing complex, which is Tag 0BFR for complete local rings.
* `finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff_of_dualizing` — Faltings'
  criterion of Tag 0EFD read in terms of the cutoff of Tag 0BJR.
* `finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_formalFibers` —
  **Tag 0BJV**, finiteness in the degrees below the cutoff.
* `not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_formalFibers` —
  **Tag 0BJV**, non-finiteness in the cutoff degree.
* `finite_lt_and_not_finite_localCohomologyCutoff_of_formalFibers` — **Tag 0BJV**, both
  conjuncts together.

## Implementation notes

Local cohomology with support in a closed set appears in two models, which agree over a
Noetherian ring: `Stacks.LocalCohomology.localCohomologyWithSupportIn` for the support
`V(I) = PrimeSpectrum.zeroLocus I`, in which Tags 0EFD and 0BJU are stated, and
`Stacks.LocalCohomology.localCohomologyModule` for the ideal `I`, in which Tags 0AW9 and 0ALZ
are stated; the comparison is
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`. The statements
below use the first.

The cutoff is an infimum in `ℕ∞`, so it is `⊤` exactly when no admissible pair of primes
exists. The two conjuncts are therefore stated so as to stay correct there: the first is indexed
by a natural number `n` strictly below the cutoff, which for `s = ⊤` gives finiteness in every
degree, and the second is hypothesized on the cutoff being a natural number, which is vacuous
for `s = ⊤`. There is no degree `⊤`, so this is exactly the content of the source statement.

## References

* [Faltings, *Über die Annulatoren lokaler Kohomologiegruppen*][Faltings-annulators], Satz 2
* [Stacks Project, Tag 0BJV](https://stacks.math.columbia.edu/tag/0BJV)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJT](https://stacks.math.columbia.edu/tag/0BJT)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Every Noetherian complete local ring has a dualizing complex.** By the Cohen structure
theorem the ring is a quotient of a power series ring in finitely many variables over a field or
a Cohen ring; that power series ring is regular local, hence Gorenstein, so it is its own
dualizing complex, and a dualizing complex is carried along a finite ring map by
`Dualizing.isDualizingComplex_derivedHom_of_finite`. -/
@[stacks 0BFR "Noetherian complete local rings"]
public theorem exists_isDualizingComplex_of_isAdicComplete (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K := by
  obtain ⟨n, Λ, _, _, hΛ, f, hf⟩ :=
    (IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries A).2
      (Ideal.fg_of_isNoetherianRing _)
  have : IsRegularLocalRing Λ := by
    rcases hΛ with hΛ | hΛ
    · let : Field Λ := hΛ.toField
      infer_instance
    · have : IsCohenRing Λ := hΛ
      infer_instance
  have : IsRegularLocalRing (MvPowerSeries (Fin n) Λ) := MvPowerSeries.isRegularLocalRing Λ n
  refine ⟨(derivedHom.{u, u, u} f).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPowerSeries (Fin n) Λ)) 0).obj
      (ModuleCat.of (MvPowerSeries (Fin n) Λ) (MvPowerSeries (Fin n) Λ))), ?_⟩
  exact isDualizingComplex_derivedHom_of_finite.{u, u} f (RingHom.Finite.of_surjective f hf) _
    (IsRegularLocalRing.isGorensteinLocalRing (MvPowerSeries (Fin n) Λ))

end Dualizing

namespace Stacks.LocalCohomology

/-! ### Faltings' criterion in terms of the cutoff -/

/-- **Faltings' finiteness criterion in terms of the cutoff of Tag 0BJR.** Over a Noetherian
ring with a dualizing complex, the local cohomology modules `H^i_{V(I)}(M)` of a finite module
are finite for all `i ≤ n` if and only if `n < s_{A,I}(M)`.

This is Tag 0EFD for `T = V(I)`, with its depth-plus-dimension clause recognised as the
statement that every admissible pair of primes contributes more than `n` to the infimum
defining the cutoff. -/
public theorem finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff_of_dualizing
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega)) :
    (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) ↔
      (n : ℕ∞) < localCohomologyCutoff A I M := by
  have hT : StableUnderSpecialization (PrimeSpectrum.zeroLocus (I : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  rw [finite_localCohomologyWithSupportIn_iff_depth_add_dim A
      (PrimeSpectrum.zeroLocus (I : Set A)) hT n M omega homega,
    ← ENat.add_one_le_iff (ENat.natCast_ne_top n), le_localCohomologyCutoff_iff]
  refine ⟨fun h p q hp hq hpq => ?_, fun h p q hp hq hpq => ?_⟩
  · rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]
    refine (natCast_lt_add_iff_eint n _ _).mpr ?_
    have hpq' := h p q
      (fun hmem => hp ((mem_zeroLocus_iff I p).1 hmem))
      ((mem_zeroLocus_iff I q).2 hq) hpq
    rwa [ringKrullDim_localization_quotient_eq_height p q hpq] at hpq'
  · rw [ringKrullDim_localization_quotient_eq_height p q hpq]
    refine (natCast_lt_add_iff_eint n _ _).mp ?_
    rw [← ENat.add_one_le_iff (ENat.natCast_ne_top n)]
    exact h p q
      (fun hmem => hp ((mem_zeroLocus_iff I p).2 hmem))
      ((mem_zeroLocus_iff I q).1 hq) hpq

/-! ### Base change of local cohomology at the level of modules -/

/-- Extension of scalars along the structure map of an algebra is the tensor product, with the
`R`-module structure on `S` coming from the algebra rather than from the ring map. -/
private theorem nonempty_extendScalars_linearEquiv_tensorProduct {R S : Type u} [CommRing R]
    [CommRing S] [a : Algebra R S] (Y : ModuleCat.{u} R) :
    Nonempty (((ModuleCat.extendScalars (algebraMap R S)).obj Y) ≃ₗ[S] TensorProduct R S Y) := by
  let aRS : Algebra R S := (algebraMap R S).toAlgebra
  have ha : aRS = a := @toAlgebra_algebraMap R S _ _ a
  have h : Nonempty (((ModuleCat.extendScalars (algebraMap R S)).obj Y) ≃ₗ[S]
      @TensorProduct R _ S Y _ _ (@Algebra.toModule R S _ _ aRS) _) := ⟨LinearEquiv.refl _ _⟩
  rwa [ha] at h

/-- Extension of scalars to a localization is localization of modules. -/
private theorem nonempty_extendScalars_iso_localizedModule {A : Type u} [CommRing A]
    (S : Submonoid A) (Y : ModuleCat.{u} A) :
    Nonempty ((ModuleCat.extendScalars (algebraMap A (Localization S))).obj Y ≅
      ModuleCat.of (Localization S) (LocalizedModule S Y)) := by
  obtain ⟨e⟩ := nonempty_extendScalars_linearEquiv_tensorProduct (S := Localization S) Y
  exact ⟨(e ≪≫ₗ (IsLocalizedModule.isBaseChange S (Localization S)
    (LocalizedModule.mkLinearMap S Y)).equiv).toModuleIso⟩

/-- For a finite module over a Noetherian ring, extension of scalars to the completion is the
completion of the module. -/
private theorem nonempty_extendScalars_iso_adicCompletion {R : Type u} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) (Y : ModuleCat.{u} R) [Module.Finite R Y] :
    Nonempty ((ModuleCat.extendScalars (algebraMap R (AdicCompletion J R))).obj Y ≅
      ModuleCat.of (AdicCompletion J R) (AdicCompletion J Y)) := by
  obtain ⟨e⟩ := nonempty_extendScalars_linearEquiv_tensorProduct (S := AdicCompletion J R) Y
  exact ⟨(e ≪≫ₗ AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J Y).toModuleIso⟩

/-- Base change of a finite module along a ring map is finite. -/
private theorem finite_extendScalars_of_finite {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (Y : ModuleCat.{u} R) (hY : Module.Finite R Y) :
    Module.Finite S ((ModuleCat.extendScalars f).obj Y) := by
  algebraize [f]
  show Module.Finite S (TensorProduct R S Y)
  infer_instance

/-- Finiteness descends along a faithfully flat ring map. -/
private theorem finite_of_finite_extendScalars_of_ff {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) (Y : ModuleCat.{u} R)
    (h : Module.Finite S ((ModuleCat.extendScalars f).obj Y)) :
    Module.Finite R Y := by
  algebraize [f]
  change Module.Finite S (TensorProduct R S Y) at h
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- Finiteness is insensitive to a faithfully flat base change. -/
private theorem finite_extendScalars_iff {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) (Y : ModuleCat.{u} R) :
    Module.Finite S ((ModuleCat.extendScalars f).obj Y) ↔ Module.Finite R Y :=
  ⟨finite_of_finite_extendScalars_of_ff f hf Y, finite_extendScalars_of_finite f Y⟩

/-- **Flat base change for local cohomology, read on the cohomology modules.** For a flat ring
map `f : A →+* B` the `B`-module `H^i_{V(IB)}(B ⊗_A M)` is the base change of `H^i_{V(I)}(M)`.
This is Tag 0ALZ for the complex `M[0]`, combined with the facts that a flat extension of
scalars carries `M[0]` to `(B ⊗_A M)[0]` and commutes with cohomology. -/
private noncomputable def localCohomologyModuleExtendScalarsIso {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : f.Flat) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
    (i : ℤ) :
    localCohomologyModule B (I.map f) (hI.map f) ((ModuleCat.extendScalars f).obj M) i ≅
      (ModuleCat.extendScalars f).obj (localCohomologyModule A I hI M i) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  let L := (localCohomologyDerived A I hI).obj K
  let e₁ := (localCohomologyDerived B (I.map f) (hI.map f)).mapIso
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsSingleIso.{u, u, u}
      f hf M).symm
  let e₂ := (localCohomologyBaseChangeIso.{u, u, u} f I hI).app K
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso (e₁ ≪≫ e₂.symm) ≪≫
    (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u} f hf i).app L

/-- **Tag 0ALZ on the cohomology modules.** For a flat ring map `f : A →+* B`, a finitely
generated ideal `I ⊆ A` and an `A`-module `M`, the `B`-module `H^i_{V(IB)}(B ⊗_A M)` is the base
change `B ⊗_A H^i_{V(I)}(M)`. This is the isomorphism built above for the proof of the finiteness
criterion, made available outside this file. -/
@[no_expose]
public noncomputable def localCohomologyModuleFlatBaseChangeIso {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : f.Flat) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
    (i : ℤ) :
    localCohomologyModule B (I.map f) (hI.map f) ((ModuleCat.extendScalars f).obj M) i ≅
      (ModuleCat.extendScalars f).obj (localCohomologyModule A I hI M i) :=
  localCohomologyModuleExtendScalarsIso f hf I hI M i

/-! ### Testing finiteness on the completed local rings -/

/-- The completion of the local ring of `A` at a prime `𝔭`. -/
public abbrev completedLocalRingAt (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal)

/-- The completion of `M_𝔭` over the completion of the local ring of `A` at `𝔭`. -/
public abbrev completedLocalization (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    (M : Type u) [AddCommGroup M] [Module A M] : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl M)

/-- The canonical map from `A` to the completion of its local ring at `𝔭`. -/
public abbrev completedLocalizationMap (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    A →+* completedLocalRingAt A p :=
  (algebraMap (Localization.AtPrime p.asIdeal) (completedLocalRingAt A p)).comp
    (algebraMap A (Localization.AtPrime p.asIdeal))

/-- **Finiteness of local cohomology along a flat map followed by a faithfully flat one.** With
`Z` the base change of `M` to `C` and `X` the base change to `B` of `H^i_{V(I)}(M)`, the
`C`-module `H^i_{V(IC)}(Z)` is finite exactly when `X` is finite over `B`. -/
private theorem finite_localCohomologyModule_tower_iff
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (u : A →+* B) (v : B →+* C) (hu : u.Flat) (hv : v.FaithfullyFlat)
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) (i : ℤ)
    {Y : ModuleCat.{u} B} (eY : (ModuleCat.extendScalars u).obj M ≅ Y)
    {Z : ModuleCat.{u} C} (eZ : (ModuleCat.extendScalars v).obj Y ≅ Z)
    {X : ModuleCat.{u} B}
    (eX : (ModuleCat.extendScalars u).obj (localCohomologyModule A I hI M i) ≅ X) :
    Module.Finite C
        (localCohomologyModule C (I.map (v.comp u)) (hI.map (v.comp u)) Z i) ↔
      Module.Finite B X := by
  have hw : (v.comp u).Flat := hu.comp hv.flat
  have e₁ : (ModuleCat.extendScalars (v.comp u)).obj M ≅ Z :=
    (ModuleCat.extendScalarsComp.{u, u} u v).app M ≪≫
      (ModuleCat.extendScalars v).mapIso eY ≪≫ eZ
  have e₂ : (ModuleCat.extendScalars (v.comp u)).obj (localCohomologyModule A I hI M i) ≅
      (ModuleCat.extendScalars v).obj X :=
    (ModuleCat.extendScalarsComp.{u, u} u v).app _ ≪≫ (ModuleCat.extendScalars v).mapIso eX
  have e₃ : localCohomologyModule C (I.map (v.comp u)) (hI.map (v.comp u)) Z i ≅
      (ModuleCat.extendScalars v).obj X :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).mapIso
        ((localCohomologyDerived C (I.map (v.comp u)) (hI.map (v.comp u))).mapIso
          ((DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).mapIso e₁.symm)) ≪≫
      localCohomologyModuleExtendScalarsIso (v.comp u) hw I hI M i ≪≫ e₂
  rw [Module.Finite.equiv_iff e₃.toLinearEquiv]
  exact finite_extendScalars_iff v hv X

/-- The completion of a finite module over a Noetherian local ring is finite over the
completion of the ring. -/
private theorem finite_adicCompletion_of_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) (Y : Type u) [AddCommGroup Y] [Module R Y] [Module.Finite R Y] :
    Module.Finite (AdicCompletion J R) (AdicCompletion J Y) := by
  obtain ⟨e⟩ := nonempty_extendScalars_iso_adicCompletion J (ModuleCat.of R Y)
  have : Module.Finite (AdicCompletion J R) ((ModuleCat.extendScalars
      (algebraMap R (AdicCompletion J R))).obj (ModuleCat.of R Y)) :=
    finite_extendScalars_of_finite _ (ModuleCat.of R Y) inferInstance
  exact Module.Finite.equiv e.toLinearEquiv

/-- The localization of a finite module at a prime is finite over the local ring. -/
private theorem finite_localizedModule_primeCompl {A : Type u} [CommRing A] (p : Ideal A)
    [p.IsPrime] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.Finite (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
  Module.Finite.of_isLocalizedModule p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)

/-- **Finiteness of local cohomology through a fixed degree is tested on the completed local
rings of `A`.** For a finite module over a Noetherian ring, `H^i_{V(I)}(M)` is finite for all
`i ≤ n` if and only if, for every prime `𝔭`, the local cohomology of the completion of `M_𝔭`
over the completion of `A_𝔭` is finite in those degrees.

Localization at `𝔭` is tested prime by prime by Tag 0AW9; local cohomology commutes with the
flat base change `A → (A_𝔭)^` by Tag 0ALZ; and finiteness descends along the faithfully flat
map `A_𝔭 → (A_𝔭)^` by Tag 03C4. -/
public theorem finite_localCohomologyModule_iff_forall_completedLocalization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    (∀ i : ℕ, i ≤ n →
        Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (i : ℤ))) ↔
      ∀ p : PrimeSpectrum A, ∀ i : ℕ, i ≤ n →
        Module.Finite (completedLocalRingAt A p)
          (localCohomologyModule (completedLocalRingAt A p)
            (I.map (completedLocalizationMap A p)) (hI.map (completedLocalizationMap A p))
            (ModuleCat.of (completedLocalRingAt A p) (completedLocalization A p M)) (i : ℤ)) := by
  have hkey : ∀ (p : PrimeSpectrum A) (i : ℤ),
      Module.Finite (completedLocalRingAt A p)
          (localCohomologyModule (completedLocalRingAt A p)
            (I.map (completedLocalizationMap A p)) (hI.map (completedLocalizationMap A p))
            (ModuleCat.of (completedLocalRingAt A p) (completedLocalization A p M)) i) ↔
        Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl
            (localCohomologyModule A I hI (ModuleCat.of A M) i)) := by
    intro p i
    have hu : (algebraMap A (Localization.AtPrime p.asIdeal)).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ p.asIdeal.primeCompl)
    have hv : (algebraMap (Localization.AtPrime p.asIdeal)
        (completedLocalRingAt A p)).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr
        (AdicCompletion.faithfullyFlat_of_le_ringJacobson _
          (le_of_eq
            (IsLocalRing.ringJacobson_eq_maximalIdeal
              (Localization.AtPrime p.asIdeal)).symm))
    obtain ⟨eY⟩ := nonempty_extendScalars_iso_localizedModule p.asIdeal.primeCompl
      (ModuleCat.of A M)
    obtain ⟨eX⟩ := nonempty_extendScalars_iso_localizedModule p.asIdeal.primeCompl
      (localCohomologyModule A I hI (ModuleCat.of A M) i)
    have := finite_localizedModule_primeCompl p.asIdeal M
    obtain ⟨eZ⟩ := nonempty_extendScalars_iso_adicCompletion
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (ModuleCat.of (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))
    exact finite_localCohomologyModule_tower_iff _ _ hu hv I hI (ModuleCat.of A M) i eY eZ eX
  have h0 := localCohomology_finite_iff_localizations_finite A I M n
  dsimp only at h0
  rw [show (∀ i : ℕ, i ≤ n →
      Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (i : ℤ))) ↔ _ from h0]
  exact ⟨fun h p i hi => (hkey p (i : ℤ)).mpr (h p i hi),
    fun h p i hi => (hkey p (i : ℤ)).mp (h p i hi)⟩

/-! ### The theorem -/

/-- **The formal fibres of a Noetherian local ring are Cohen–Macaulay.** The formal fibre of
`A` over a prime `𝔭` is `A^ ⊗_A κ(𝔭)`; the existence of a Noetherian-ring structure records
that the fibre is Noetherian, as required to speak of Cohen–Macaulayness. -/
public def FormalFibersAreCohenMacaulay (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (p : Ideal A), ∀ [_hp : p.IsPrime],
    let F := TensorProduct A (AdicCompletion (maximalIdeal A) A) p.ResidueField
    ∃ hF : IsNoetherianRing F, @IsCohenMacaulayRing F (inferInstance : CommRing F) hF

/-- Cohen–Macaulay formal fibres satisfy Serre's condition `(Sₖ)` for every `k`. -/
private theorem formalFibersHavePropertySk_of_cohenMacaulay (A : Type u) [CommRing A]
    [IsLocalRing A] (h : FormalFibersAreCohenMacaulay A) (k : ℕ) :
    FormalFibersHavePropertySk A k := by
  intro p hp
  obtain ⟨hF, hCM⟩ := h p
  exact ⟨hF, @propertySkRing_of_isCohenMacaulayRing _ _ hF hCM k⟩

/-- Finiteness of local cohomology is the same in the support model and the ideal model. -/
private theorem finite_localCohomologyWithSupportIn_iff_localCohomologyModule (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) (i : ℤ) :
    Module.Finite A (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) ↔
      Module.Finite A (localCohomologyModule A I hI M i) :=
  Module.Finite.equiv_iff
    (localCohomologyWithSupportInIsoLocalCohomologyModule A I hI M i).toLinearEquiv

/-- Local cohomology of a module placed in degree zero vanishes in negative degrees, so the
degrees `i ≤ n` in which finiteness has to be checked are the natural numbers `i ≤ n`, and
there the two models of local cohomology agree. -/
public theorem finite_forall_int_iff_forall_nat (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) (n : ℕ) :
    (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i)) ↔
      ∀ i : ℕ, i ≤ n → Module.Finite A (localCohomologyModule A I hI M (i : ℤ)) := by
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (finite_localCohomologyWithSupportIn_iff_localCohomologyModule A I hI M i).1
      (h (i : ℤ) (by exact_mod_cast hi))
  · rcases lt_or_ge i 0 with hneg | hpos
    · have := subsingleton_localCohomologyWithSupportIn_single_of_neg.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A)) M i hneg
      infer_instance
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
      exact (finite_localCohomologyWithSupportIn_iff_localCohomologyModule A I hI M j).2
        (h j (by exact_mod_cast hi))

/-- **Faltings' criterion over the completion of a local ring of `A`.** The completion is a
Noetherian complete local ring, so it has a dualizing complex and Tag 0EFD applies to it. -/
public theorem finite_localCohomologyModule_completedLocalRingAt_iff
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (n : ℕ) :
    (∀ i : ℕ, i ≤ n → Module.Finite (completedLocalRingAt A p)
        (localCohomologyModule (completedLocalRingAt A p) (I.map (completedLocalizationMap A p))
          (hI.map (completedLocalizationMap A p))
          (ModuleCat.of (completedLocalRingAt A p) (completedLocalization A p M)) (i : ℤ))) ↔
      (n : ℕ∞) < localCohomologyCutoff (completedLocalRingAt A p)
        (I.map (completedLocalizationMap A p)) (completedLocalization A p M) := by
  have := finite_localizedModule_primeCompl p.asIdeal M
  have : Module.Finite (completedLocalRingAt A p) (completedLocalization A p M) :=
    finite_adicCompletion_of_finite _ _
  obtain ⟨omega, homega⟩ :=
    Dualizing.exists_isDualizingComplex_of_isAdicComplete (completedLocalRingAt A p)
  rw [← finite_forall_int_iff_forall_nat (completedLocalRingAt A p)
    (I.map (completedLocalizationMap A p)) (hI.map (completedLocalizationMap A p))
    (ModuleCat.of (completedLocalRingAt A p) (completedLocalization A p M)) n]
  exact finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff_of_dualizing
    (completedLocalRingAt A p) (I.map (completedLocalizationMap A p)) n
    (completedLocalization A p M) omega homega

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The finiteness half of Tag 0BJV, in the coreflection model. -/
private theorem finite_localCohomologyModule_of_lt_localCohomologyCutoff
    (hA : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal))
    (n : ℕ) (hn : (n : ℕ∞) < localCohomologyCutoff A I M) :
    ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of A M) (i : ℤ)) := by
  rw [finite_localCohomologyModule_iff_forall_completedLocalization]
  intro p i hi
  have hcut := lt_localCohomologyCutoff_adicCompletion_localization A I M n hA
    (fun q => formalFibersHavePropertySk_of_cohenMacaulay _ (hformal q) n) hn p
  rw [Ideal.map_map] at hcut
  exact (finite_localCohomologyModule_completedLocalRingAt_iff A I
    (Ideal.fg_of_isNoetherianRing I) M p n).mpr hcut i hi

/-- **Stacks Project, Tag 0BJV, finiteness below the cutoff.** Let `A` be a universally
catenary Noetherian ring whose local rings have Cohen–Macaulay formal fibres, let `I ⊆ A` be an
ideal, let `Z = V(I)` and let `M` be a finite `A`-module. Then `H^i_Z(M)` is a finite
`A`-module in every degree `i` strictly below the cutoff `s = s_{A,I}(M)` of Tag 0BJR.

The degrees `i < s` are expressed through a natural number `n` with `n < s` and `i ≤ n`, which
for `s = ⊤` gives finiteness in every degree. -/
@[stacks 0BJV "finiteness in the degrees below the cutoff"]
public theorem finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_formalFibers
    (hA : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal))
    (n : ℕ) (hn : (n : ℕ∞) < localCohomologyCutoff A I M) (i : ℤ) (hi : i ≤ (n : ℤ)) :
    Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
  (finite_forall_int_iff_forall_nat A I (Ideal.fg_of_isNoetherianRing I)
      (ModuleCat.of A M) n).mpr
    (finite_localCohomologyModule_of_lt_localCohomologyCutoff A I M hA hformal n hn) i hi

/-- **Stacks Project, Tag 0BJV, non-finiteness at the cutoff.** In the situation of
`finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_formalFibers`, if the cutoff
`s = s_{A,I}(M)` is the natural number `s`, then `H^s_Z(M)` is *not* a finite `A`-module.

Were it finite it would join the finite modules in the degrees below `s` to make `H^i_Z(M)`
finite for all `i ≤ s`; testing that on the completion of the local ring at the prime at which
the cutoff is attained, Tag 0EFD would then force `s < s`. The hypothesis that the cutoff is a
natural number is needed as stated: the cutoff is an infimum in `ℕ∞` and there is no degree
`⊤`. -/
@[stacks 0BJV "non-finiteness in the cutoff degree"]
public theorem not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_formalFibers
    (hA : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal))
    (s : ℕ) (hs : localCohomologyCutoff A I M = (s : ℕ∞)) :
    ¬ Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) (s : ℤ)) := by
  intro hfin
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hfin' := (finite_localCohomologyWithSupportIn_iff_localCohomologyModule A I hI
    (ModuleCat.of A M) s).1 hfin
  have hall : ∀ i : ℕ, i ≤ s →
      Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (i : ℤ)) := by
    intro i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hfin'
    · refine finite_localCohomologyModule_of_lt_localCohomologyCutoff A I M hA hformal
        (s - 1) ?_ i (by omega)
      rw [hs]
      exact_mod_cast Nat.sub_lt (by omega) Nat.one_pos
  have hfa := (finite_localCohomologyModule_iff_forall_completedLocalization A I hI M s).mp hall
  obtain ⟨q, _, hcut⟩ := exists_localCohomologyCutoff_adicCompletion_localization_eq A I M hA
    (by rw [hs]; exact ENat.natCast_lt_top s)
    (fun r => formalFibersHavePropertySk_of_cohenMacaulay _ (hformal r) _)
  rw [Ideal.map_map, hs] at hcut
  have hlt := (finite_localCohomologyModule_completedLocalRingAt_iff A I hI M q s).mp (hfa q)
  rw [hcut] at hlt
  exact lt_irrefl _ hlt

/-- **Stacks Project, Tag 0BJV.** Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let
`Z = V(I) ⊆ Spec(A)` and let `M` be a finite `A`-module. Set `s = s_{A,I}(M)` as in Tag 0BJR.
Assume that `A` is universally catenary and that the formal fibres of the local rings of `A`
are Cohen–Macaulay. Then `H^i_Z(M)` is finite for `0 ≤ i < s`, and `H^s_Z(M)` is not finite.

This is a special case of Satz 2 of Faltings. The first conjunct expresses `i < s` through a
natural number `n` with `n < s` and `i ≤ n`, which covers every degree when `s = ⊤`; the second
is hypothesized on `s` being a natural number, as it must be. -/
@[stacks 0BJV]
public theorem finite_lt_and_not_finite_localCohomologyCutoff_of_formalFibers
    (hA : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal)) :
    (∀ n : ℕ, (n : ℕ∞) < localCohomologyCutoff A I M → ∀ i : ℤ, i ≤ (n : ℤ) →
        Module.Finite A
          (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) ∧
      (∀ s : ℕ, localCohomologyCutoff A I M = (s : ℕ∞) →
        ¬ Module.Finite A
          (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A M)) (s : ℤ))) :=
  ⟨fun n hn i hi =>
      finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_formalFibers A I M
        hA hformal n hn i hi,
    fun s hs =>
      not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_formalFibers A I M
        hA hformal s hs⟩

end Stacks.LocalCohomology

end
