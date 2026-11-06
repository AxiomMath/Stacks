module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.FiniteLocalExtension.GluedSubalgebra

/-!
# Finite local extensions with prescribed localizations

Transport of the glued subalgebra along an algebra isomorphism, and the main theorem
`exists_finite_local_extension_with_prescribed_localizations`.
-/

@[expose] public section

open scoped Pointwise

universe u v w

/-- Bijectivity of the residue field map of the structure map transports along an
`A`-algebra isomorphism. -/
private lemma residueField_map_bijective_of_algEquiv
    {A B T : Type*} [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing T] [IsLocalHom (algebraMap A B)]
    [IsLocalHom (algebraMap A T)] (e : B ≃ₐ[A] T)
    (hTresidue : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A T))) :
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) := by
  have : IsLocalHom e.toRingHom := .of_surjective _ e.surjective
  have hrescomp (x : IsLocalRing.ResidueField A) :
      IsLocalRing.ResidueField.map e.toRingHom
          (IsLocalRing.ResidueField.map (algebraMap A B) x) =
        IsLocalRing.ResidueField.map (algebraMap A T) x := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    simp only [IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue T) (e.commutes a)
  have hresEquiv : Function.Bijective (IsLocalRing.ResidueField.map e.toRingHom) := by
    constructor
    · exact (IsLocalRing.ResidueField.map e.toRingHom).injective
    · intro z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨b, hb⟩ := e.toRingEquiv.surjective x
      refine ⟨IsLocalRing.residue B b, ?_⟩
      rw [IsLocalRing.ResidueField.map_residue]
      exact congrArg (IsLocalRing.residue T) hb
  constructor
  · intro x y hxy
    apply hTresidue.1
    rw [← hrescomp x, ← hrescomp y, hxy]
  · intro z
    obtain ⟨x, hx⟩ := hTresidue.2 (IsLocalRing.ResidueField.map e.toRingHom z)
    refine ⟨x, hresEquiv.1 ?_⟩
    rw [hrescomp, hx]

/-- The conclusions of `exists_finite_glued_subalgebra` transport along an `A`-algebra
isomorphism. -/
private lemma prescribed_localizations_of_algEquiv
    {A : Type u} [CommRing A] [IsLocalRing A] {t : A}
    {ι : Type v} (q : ι → Ideal A) (hq : ∀ i, (q i).IsPrime)
    (Bᵢ : ι → Type w) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)]
    {B T : Type*} [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]
    [IsLocalRing B] [IsLocalRing T] [IsLocalHom (algebraMap A B)]
    [IsLocalHom (algebraMap A T)] [Module.Finite A T]
    (e : B ≃ₐ[A] T) (hTinj : Function.Injective (algebraMap A T))
    (hTresidue : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A T)))
    (hTtorsion : ∃ n : ℕ, ∀ b : T, ∃ a : A,
      algebraMap A T a = algebraMap A T (t ^ n) * b)
    (ℓ : ∀ i, T →ₐ[A] Bᵢ i)
    (hloc : ∀ i, letI := (ℓ i).toRingHom.toAlgebra
      IsLocalization ((q i).primeCompl.map (algebraMap A T)) (Bᵢ i)) :
    Function.Injective (algebraMap A B) ∧
      Module.Finite A B ∧
      Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) ∧
      (∃ n : ℕ, ∀ b : B, ∃ a : A,
        algebraMap A B a = algebraMap A B (t ^ n) * b) ∧
      ∃ ℓ : ∀ i, B →ₐ[A] Bᵢ i, ∀ i,
        letI := (ℓ i).toRingHom.toAlgebra
        IsLocalization ((q i).primeCompl.map (algebraMap A B)) (Bᵢ i) := by
  have hBfinite : Module.Finite A B :=
    Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
  have hBinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply hTinj
    simpa only [← e.commutes] using congrArg e hab
  have hBtorsion : ∃ n : ℕ, ∀ b : B, ∃ a : A,
      algebraMap A B a = algebraMap A B (t ^ n) * b := by
    obtain ⟨n, hn⟩ := hTtorsion
    refine ⟨n, fun b => ?_⟩
    obtain ⟨a, ha⟩ := hn (e b)
    refine ⟨a, e.injective ?_⟩
    simpa only [map_mul, e.commutes] using ha
  let ℓB (i : ι) : B →ₐ[A] Bᵢ i := (ℓ i).comp e.toAlgHom
  have hBloc (i : ι) :
      let := (ℓB i).toRingHom.toAlgebra
      IsLocalization ((q i).primeCompl.map (algebraMap A B)) (Bᵢ i) := by
    let : (q i).IsPrime := hq i
    exact localization_equiv_source A B T (Bᵢ i) (q i).primeCompl e (ℓ i) (hloc i)
  exact ⟨hBinj, hBfinite, residueField_map_bijective_of_algEquiv e hTresidue, hBtorsion, ℓB,
    hBloc⟩

/-- Finite modifications at the finitely many primes above a nonzerodivisor in a Noetherian local
ring come from one finite local modification. -/
@[stacks 0EAV]
public theorem exists_finite_local_extension_with_prescribed_localizations
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {t : A} (_htm : t ∈ IsLocalRing.maximalIdeal A) (ht : IsSMulRegular A t)
    {ι : Type v} [Finite ι] (q : ι → Ideal A) (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A) (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (Bᵢ : ι → Type w) [∀ i, CommRing (Bᵢ i)]
    [∀ i, Algebra (Localization.AtPrime (q i)) (Bᵢ i)]
    [∀ i, Algebra A (Bᵢ i)]
    [∀ i, IsScalarTower A (Localization.AtPrime (q i)) (Bᵢ i)]
    (hinj : ∀ i, Function.Injective
      (algebraMap (Localization.AtPrime (q i)) (Bᵢ i)))
    (hfinite : ∀ i, Module.Finite (Localization.AtPrime (q i)) (Bᵢ i))
    (htorsion : ∀ i, ∃ n : ℕ, ∀ b : Bᵢ i, ∃ a : Localization.AtPrime (q i),
      algebraMap (Localization.AtPrime (q i)) (Bᵢ i) a =
        algebraMap A (Bᵢ i) (t ^ n) * b) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsLocalRing B)
      (_ : IsLocalHom (algebraMap A B)),
      Function.Injective (algebraMap A B) ∧
      Module.Finite A B ∧
      Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) ∧
      (∃ n : ℕ, ∀ b : B, ∃ a : A,
        algebraMap A B a = algebraMap A B (t ^ n) * b) ∧
      ∃ ℓ : ∀ i, B →ₐ[A] Bᵢ i, ∀ i,
        letI := (ℓ i).toRingHom.toAlgebra
        IsLocalization ((q i).primeCompl.map (algebraMap A B)) (Bᵢ i) := by
  classical
  obtain ⟨T, hTfinite, hTinj, hTlocal, hTlocalHom, hTresidue, hTtorsion, ℓ, hloc⟩ :=
    exists_finite_glued_subalgebra t ht q hq hq_ne hq_inj hV Bᵢ hinj hfinite htorsion
  let : Module.Finite A T := hTfinite
  let : IsLocalRing T := hTlocal
  let : IsLocalHom (algebraMap A T) := hTlocalHom
  let : Small.{u} T := Module.Finite.small A T
  let hTRing : CommRing T := inferInstance
  let : CommSemiring T := hTRing.toCommSemiring
  let : Semiring T := hTRing.toCommSemiring.toSemiring
  let : NonAssocSemiring T := hTRing.toCommSemiring.toNonAssocSemiring
  let B : Type u := Shrink.{u} T
  let r₀ : B ≃ T := (equivShrink T).symm
  let hBRing : CommRing B := r₀.commRing
  let : CommRing B := hBRing
  let : CommSemiring B := hBRing.toCommSemiring
  let : Semiring B := hBRing.toCommSemiring.toSemiring
  let : NonAssocSemiring B := hBRing.toCommSemiring.toNonAssocSemiring
  let : Mul B := hBRing.toCommSemiring.toNonAssocSemiring.toDistrib.toMul
  let : Add B := hBRing.toCommSemiring.toNonAssocSemiring.toDistrib.toAdd
  let r : B ≃+* T := r₀.ringEquiv
  let fB : A →+* B := r.symm.toRingHom.comp (algebraMap A T)
  let : Algebra A B := fB.toAlgebra
  let : Module A B := Algebra.toModule
  let e : B ≃ₐ[A] T := AlgEquiv.ofRingEquiv (f := r) (by
    intro a
    show r (fB a) = algebraMap A T a
    simp [fB])
  let : IsLocalRing B := e.toRingEquiv.symm.isLocalRing
  have heq : e.toRingHom.comp (algebraMap A B) = algebraMap A T :=
    RingHom.ext e.commutes
  have : IsLocalHom e.toRingHom := .of_surjective _ e.surjective
  let : IsLocalHom (e.toRingHom.comp (algebraMap A B)) := by
    rw [heq]
    exact hTlocalHom
  let : IsLocalHom (algebraMap A B) :=
    isLocalHom_of_comp (algebraMap A B) e.toRingHom
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    prescribed_localizations_of_algEquiv q hq Bᵢ e hTinj hTresidue hTtorsion ℓ hloc⟩
