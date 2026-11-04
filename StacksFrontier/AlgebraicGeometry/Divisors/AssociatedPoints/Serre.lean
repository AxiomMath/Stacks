module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Serre's condition `(S₁)` and embedded associated points

A coherent sheaf on a locally Noetherian scheme has no embedded associated points exactly when
it satisfies Serre's condition `(S₁)`.

## Main results

* `AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one` gives the equivalence.

## Implementation notes

The absence of embedded associated points is the predicate of Stacks tag 05AK, and Serre's
condition is the stalkwise predicate of Stacks tag 0341. Both sides are tested on an affine
open, where the stalk is the localization of the module of sections: having no embedded
associated point at `x` is minimality of the corresponding prime among the associated primes of
`Γ(F, U)`, and that is the module-theoretic form of `(S₁)`.

## References

* [Stacks Project, Tag 0346](https://stacks.math.columbia.edu/tag/0346)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Serre's condition `(S₁)` for a module transports along a surjective ring isomorphism. -/
private lemma module_serreSk_one_congr_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (M : Type*) [AddCommGroup M] [Module A M]
    [Module B M] [Algebra A B] [IsScalarTower A B M]
    (hsurj : Function.Surjective (algebraMap A B)) (hAlg : algebraMap A B = e.toRingHom)
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B) [Module.Finite A M] [Module.Finite B M] :
    (min (1 : WithBot ℕ∞) (Module.supportDim A M) ≤
        (Module.depth A (IsLocalRing.maximalIdeal A) M : WithBot ℕ∞)) ↔
      min (1 : WithBot ℕ∞) (Module.supportDim B M) ≤
        (Module.depth B (IsLocalRing.maximalIdeal B) M : WithBot ℕ∞) := by
  rw [Module.supportDim_eq_of_ringEquiv e M hAlg,
    Module.depth_eq_depth_map_algebraMap hsurj (IsLocalRing.maximalIdeal A) M, hmax]

/-- The two module structures on the stalk of a presheaf of modules over the structure sheaf of
a scheme agree. -/
lemma stalkModule_eq_presheafInstance {X : Scheme.{u}}
    (M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toSheafedSpace M x =
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M x :=
  rfl

/-- On an affine open, Serre's condition `(S₁)` for the localized module of sections at the
prime of `x` is Serre's condition for the stalk at `x`. -/
private lemma affine_stalk_serre_iff {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    (min (1 : WithBot ℕ∞) (Module.supportDim
        (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U))) ≤
      (Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (IsLocalRing.maximalIdeal
          (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) :
          WithBot ℕ∞)) ↔
    min (1 : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) : WithBot ℕ∞) := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have hqft :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hqc : F.IsQuasicoherent := hqft.1
  have hft : F.IsFiniteType := hqft.2
  let R := Γ(X, U)
  let M := Γ(F, U)
  have hfinM : Module.Finite R M := moduleFinite_sections_on_affine F U hU
  let S := Localization.AtPrime p
  let T := X.presheaf.stalk x
  let N := F.presheaf.stalk x
  let : Module T N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module R N := affineStalkModule F U x hx
  let : Algebra R T := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime T p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p
  let e : S ≃ₐ[R] T := IsLocalization.algEquiv p.primeCompl S T
  let : Algebra S T := e.toAlgHom.toAlgebra
  let : Module S N := Module.compHom N (algebraMap S T)
  let : IsScalarTower S T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomp (r : R) : algebraMap S T (algebraMap R S r) = algebraMap R T r := by
    change e (algebraMap R S r) = _
    exact e.commutes r
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun r t => by
    change algebraMap S T (algebraMap R S r) * t = algebraMap R T r * t
    rw [hcomp]
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r n => by
    change algebraMap S T (algebraMap R S r) • n = algebraMap R T r • n
    rw [hcomp]
  have hloc : IsLocalizedModule p.primeCompl (affineGerm F U x hx) :=
    affineGerm_isLocalized F U hU x hx
  let eM : LocalizedModule p.primeCompl M ≃ₗ[R] N :=
    IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
      (affineGerm F U x hx)
  let eM' : LocalizedModule p.primeCompl M ≃ₗ[S] N :=
    eM.extendScalarsOfIsLocalization p.primeCompl S
  have hdepth : Module.depth S (IsLocalRing.maximalIdeal S)
      (LocalizedModule p.primeCompl M) = Module.depth S (IsLocalRing.maximalIdeal S) N :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) eM'
  have hdim : Module.supportDim S (LocalizedModule p.primeCompl M) =
      Module.supportDim S N := Module.supportDim_eq_of_equiv eM'
  have halg : algebraMap S T = e.toRingHom := rfl
  have hmax : Ideal.map (algebraMap S T) (IsLocalRing.maximalIdeal S) =
      IsLocalRing.maximalIdeal T := by
    change Ideal.map e.toRingHom (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal T
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hsurj : Function.Surjective (algebraMap S T) := e.surjective
  have hfiniteS : Module.Finite S N := Module.Finite.of_surjective eM'.toLinearMap eM'.surjective
  have hfiniteT : Module.Finite T N := Module.Finite.of_surjective
    ({ toFun := id
       map_smul' := fun s n => rfl
       map_add' := fun _ _ => rfl } : N →ₛₗ[e.toRingHom] N) (by intro n; exact ⟨n, rfl⟩)
  calc
    min 1 (Module.supportDim S (LocalizedModule p.primeCompl M)) ≤
        (Module.depth S (IsLocalRing.maximalIdeal S)
          (LocalizedModule p.primeCompl M) : WithBot ℕ∞) ↔
      min 1 (Module.supportDim S N) ≤
        (Module.depth S (IsLocalRing.maximalIdeal S) N : WithBot ℕ∞) := by rw [hdim, hdepth]
    _ ↔ min 1 (Module.supportDim T N) ≤
        (Module.depth T (IsLocalRing.maximalIdeal T) N : WithBot ℕ∞) :=
      module_serreSk_one_congr_of_ringEquiv e.toRingEquiv N hsurj halg hmax

/-- Every prime of the sections over an affine open is the prime of its image point. -/
private lemma exists_fromSpec_mem_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    ∃ h : hU.fromSpec p ∈ U, hU.primeIdealOf ⟨hU.fromSpec p, h⟩ = p := by
  have h : hU.fromSpec p ∈ U := by
    change hU.fromSpec p ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨p, rfl⟩
  exact ⟨h, hU.fromSpec.isOpenEmbedding.injective (by
    simpa using hU.fromSpec_primeIdealOf ⟨hU.fromSpec p, h⟩)⟩

/-- On an affine open, having no embedded associated point at `x` is minimality of the
corresponding prime among the associated primes of the module of sections. -/
private lemma not_embedded_iff_minimal_associatedPrime_at {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (U : X.Opens)
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ¬ IsEmbeddedAssociatedPoint F x ↔
      ((hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) →
        Minimal (· ∈ associatedPrimes Γ(X, U) Γ(F, U)) (hU.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  have hqft :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hqc : F.IsQuasicoherent := hqft.1
  have hft : F.IsFiniteType := hqft.2
  let p := hU.primeIdealOf ⟨x, hx⟩
  let R : Type u := Γ(X, U)
  let M : Type u := Γ(F, U)
  have hnoeth : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hassoc (z : X) (hz : z ∈ U) :
      (hU.primeIdealOf ⟨z, hz⟩).asIdeal ∈ associatedPrimes R M ↔
        Stacks.Divisors.IsAssociatedPoint F z := by
    rw [← isAssociatedPrimeStacks_iff_mem_associatedPrimes]
    simpa [p, R, M] using
      (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F U hU hz)
  constructor
  · intro hno hp
    have hpn : p.asIdeal ∈ associatedPrimes R M := hp
    refine (minimal_iff_forall_lt).2 ⟨hpn, ?_⟩
    intro q hqp hq
    let q' : PrimeSpectrum R := ⟨q, (AssociatedPrimes.mem_iff.mp hq).isPrime⟩
    obtain ⟨hqU, hqeq⟩ := exists_fromSpec_mem_primeIdealOf_eq hU q'
    let y := hU.fromSpec q'
    have hqassoc : Stacks.Divisors.IsAssociatedPoint F y :=
      (hassoc y hqU).mp (by rw [hqeq]; exact hq)
    have hspec : y ⤳ x := by
      have hqle : q' ≤ p := (PrimeSpectrum.asIdeal_le_asIdeal q' p).mp (le_of_lt hqp)
      have hqspec : q' ⤳ p := (PrimeSpectrum.le_iff_specializes q' p).mp hqle
      have himage : hU.fromSpec q' ⤳ hU.fromSpec p :=
        (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mpr hqspec
      simpa [y, p, hU.fromSpec_primeIdealOf] using himage
    have hne : y ≠ x := by
      intro heq
      have hqeq' : (⟨q, hq.isPrime⟩ : PrimeSpectrum R) = p :=
        hU.fromSpec.isOpenEmbedding.injective (by
          simpa [y, p, hU.fromSpec_primeIdealOf] using
            heq.trans (hU.fromSpec_primeIdealOf ⟨x, hx⟩).symm)
      exact hqp.ne (congrArg PrimeSpectrum.asIdeal hqeq')
    exact hno ⟨(hassoc x hx).mp hpn, y, hqassoc, hspec, hne⟩
  · intro hmin hEmb
    obtain ⟨hxassoc, y, hyassoc, hspec, hne⟩ := hEmb
    have hp : p.asIdeal ∈ associatedPrimes R M := (hassoc x hx).mpr hxassoc
    have hyU : y ∈ U := hspec.mem_open U.isOpen hx
    have hq : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∈ associatedPrimes R M :=
      (hassoc y hyU).mpr hyassoc
    have hqp : (hU.primeIdealOf ⟨y, hyU⟩ : PrimeSpectrum R) ≤ p := by
      apply (PrimeSpectrum.le_iff_specializes _ _).2
      apply (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp
      simpa [p, hU.fromSpec_primeIdealOf] using hspec
    have hneq : (hU.primeIdealOf ⟨y, hyU⟩ : PrimeSpectrum R) ≠ p := by
      intro heq
      apply hne
      simpa [p, hU.fromSpec_primeIdealOf] using congrArg hU.fromSpec heq
    have hlt : (hU.primeIdealOf ⟨y, hyU⟩ : PrimeSpectrum R) < p := lt_of_le_of_ne hqp hneq
    exact (minimal_iff_forall_lt.mp (hmin hp)).2 hlt hq

/-- **Stacks Project, Tag 0346.** A coherent sheaf on a locally Noetherian scheme has no
embedded associated points if and only if it satisfies Serre's condition `(S₁)`. -/
@[stacks 0346]
theorem hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    HasNoEmbeddedAssociatedPoints F ↔ SheafHasPropertySk X F 1 := by
  have hqft :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hqc : F.IsQuasicoherent := hqft.1
  have hft : F.IsFiniteType := hqft.2
  constructor
  · intro hNo x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x)
      (by simp)
    let R : Type u := Γ(X, U)
    let M : Type u := Γ(F, U)
    have hnoeth : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hfinM : Module.Finite R M := moduleFinite_sections_on_affine F U hU
    have hmin : ∀ p : PrimeSpectrum R, p.asIdeal ∈ associatedPrimes R M →
        Minimal (· ∈ associatedPrimes R M) p.asIdeal := by
      intro p hp
      obtain ⟨hpU, hpEq⟩ := exists_fromSpec_mem_primeIdealOf_eq hU p
      have hmin' := (not_embedded_iff_minimal_associatedPrime_at F U hU (hU.fromSpec p) hpU).mp
        (hNo (hU.fromSpec p))
      have hp' : (hU.primeIdealOf ⟨hU.fromSpec p, hpU⟩).asIdeal ∈ associatedPrimes R M := by
        rw [hpEq]
        exact hp
      simpa only [hpEq] using hmin' hp'
    have hmin' : ∀ q ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) q :=
      fun q hq => hmin ⟨q, (AssociatedPrimes.mem_iff.mp hq).isPrime⟩ hq
    have hmodule :=
      (Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth
        (R := R) (M := M)).mp hmin'
    have hSkx := (affine_stalk_serre_iff F U hU x hxU).mp (hmodule (hU.primeIdealOf ⟨x, hxU⟩))
    rw [stalkModule_eq_presheafInstance]
    exact hSkx
  · intro hSk x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x)
      (by simp)
    let R : Type u := Γ(X, U)
    let M : Type u := Γ(F, U)
    have hnoeth : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hfinM : Module.Finite R M := moduleFinite_sections_on_affine F U hU
    have hmodule : ∀ p : PrimeSpectrum R,
        min 1 (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)) ≤
        (Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞) := by
      intro p
      obtain ⟨hpU, hpEq⟩ := exists_fromSpec_mem_primeIdealOf_eq hU p
      have hp' := (affine_stalk_serre_iff F U hU (hU.fromSpec p) hpU).mpr (by
        have hSkPoint := hSk (hU.fromSpec p)
        rw [stalkModule_eq_presheafInstance] at hSkPoint
        exact hSkPoint)
      rwa [hpEq] at hp'
    have hmin :=
      (Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth
        (R := R) (M := M)).mpr hmodule
    exact (not_embedded_iff_minimal_associatedPrime_at F U hU x hxU).2
      (hmin (hU.primeIdealOf ⟨x, hxU⟩))

end AlgebraicGeometry
