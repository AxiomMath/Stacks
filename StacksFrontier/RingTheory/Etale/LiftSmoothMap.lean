module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.LiftIdempotentsAndModules
public import StacksFrontier.RingTheory.Etale.Locus
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.Smooth.Conormal
public import StacksFrontier.RingTheory.Smooth.NaiveCotangentCriterion
public import StacksFrontier.RingTheory.Smooth.SymmetricAlgebra

/-!
# Lifting a map out of a smooth algebra along an étale extension

Let `A` be a commutative ring, `I` an ideal, and `B` a smooth `A`-algebra. Any `A`-algebra map
`B → A ⧸ I` lifts to an `A`-algebra map `B → A'` for some étale `A`-algebra `A'` inducing an
isomorphism `A ⧸ I ≃ A' ⧸ IA'`. This is the strongest of the lifting results of this directory and
uses most of the others.

## Main results

* `exists_etale_lift_of_smooth`: the lift of an `A`-algebra map from a smooth `A`-algebra into
  `A ⧸ I`.

## Implementation notes

The proof is the source's. Writing `J` for the kernel of `B → A ⧸ I`, smoothness makes
`0 → I ⧸ I² → J ⧸ J² → Ω[B⁄A] ⊗ B ⧸ J → 0` split, so `P = J ⧸ (J² + IB)` is a finite projective
`A ⧸ I`-module. Lifting a complement of `P` by Stacks 07M5
(`exists_etale_baseChange_finite_projective_lift`) and enlarging `B` by the symmetric algebra on
that complement — smooth over `A` by Stacks 07M6
(`symmetricAlgebra_smooth_iff_finite_projective`), with its cotangent complex computed by Stacks
07EV — reduces to the case where `Ω[B⁄A] ⊗ B ⧸ J` is free of rank `n`.

In that case, choosing `f₁, …, f_n ∈ J` lifting a basis and setting `C = B ⧸ (f₁, …, f_n)`, the
Jacobi–Zariski sequence shows `H₁(L_{C⁄A})` and `Ω[C⁄A]` vanish locally along `J C`, so `A → C` is
étale there; Stacks 07M0 (`exists_isUnit_quotient_mk_and_etale_away`) inverts one element to make
`A → C_f` étale outright, and a further localization identifies `A ⧸ I` with a localization of
`C_f ⧸ I C_f`, giving `A'`.

## References

* [Stacks Project, Tag 07M7](https://stacks.math.columbia.edu/tag/07M7)
-/


open TensorProduct

universe u v

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

@[expose] public section

private theorem etale_mod_ideal
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Etale A C] (I : Ideal A) :
    Algebra.Etale (A ⧸ I) (C ⧸ I.map (algebraMap A C)) :=
  Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm

/-- A map to `A ⧸ I` induces a retraction of the canonical closed-fibre map. -/
private theorem quotient_retraction_of_algHom
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) (σ : C →ₐ[A] A ⧸ I) :
    let J := I.map (algebraMap A C)
    ∃ τ : (C ⧸ J) →ₐ[A ⧸ I] (A ⧸ I),
      τ.toRingHom.comp
        (Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map) = RingHom.id _ ∧
      ∀ x, τ (Ideal.Quotient.mk J x) = σ x := by
  dsimp
  let J := I.map (algebraMap A C)
  have hJ : J ≤ RingHom.ker σ.toRingHom := Ideal.map_le_iff_le_comap.mpr fun a ha =>
    (σ.commutes a).trans (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  let τ₀ : (C ⧸ J) →+* (A ⧸ I) :=
    Ideal.Quotient.lift J σ.toRingHom (fun x hx => RingHom.mem_ker.mp (hJ hx))
  have key : ∀ x, τ₀ (Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact σ.commutes a
  exact ⟨{ toRingHom := τ₀, commutes' := key }, RingHom.ext key, fun _ => rfl⟩

/-- If the original algebra is étale, the induced closed-fibre retraction is étale as well. -/
private theorem quotient_retraction_etale
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Etale A C] (I : Ideal A) (σ : C →ₐ[A] A ⧸ I) :
    let J := I.map (algebraMap A C)
    ∃ τ : (C ⧸ J) →ₐ[A ⧸ I] (A ⧸ I),
      τ.toRingHom.comp
        (Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map) = RingHom.id _ ∧
      τ.toRingHom.Etale ∧
      ∀ x, τ (Ideal.Quotient.mk J x) = σ x := by
  dsimp
  let J := I.map (algebraMap A C)
  obtain ⟨τ, hτ, hσ⟩ := quotient_retraction_of_algHom I σ
  have hCbar : Algebra.Etale (A ⧸ I) (C ⧸ J) := etale_mod_ideal I
  let q : (A ⧸ I) →+* (C ⧸ J) :=
    Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map
  have hq : q.Etale := RingHom.etale_algebraMap.mpr hCbar
  have hcomp : (τ.toRingHom.comp q).Etale := by
    rw [hτ]
    exact RingHom.etale_algebraMap.mpr
      (inferInstance : Algebra.Etale (A ⧸ I) (A ⧸ I))
  have hqft : q.FiniteType := by
    show (algebraMap (A ⧸ I) (C ⧸ J)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact ⟨τ, hτ, RingHom.Etale.of_comp hq.formallyUnramified hqft hcomp, hσ⟩

/-- The closed-fibre section of an étale algebra is the localization at an idempotent. -/
private theorem quotient_retraction_idempotent
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Etale A C] (I : Ideal A) (σ : C →ₐ[A] A ⧸ I) :
    let J := I.map (algebraMap A C)
    ∃ (τ : (C ⧸ J) →ₐ[A ⧸ I] A ⧸ I) (e : C ⧸ J),
      τ.toRingHom.comp (Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map) =
        RingHom.id _ ∧
      IsIdempotentElem e ∧
      RingHom.ker τ.toRingHom = Ideal.span {1 - e} ∧
      (letI : Algebra (C ⧸ J) (A ⧸ I) := τ.toRingHom.toAlgebra
       IsLocalization.Away e (A ⧸ I)) ∧
      ∀ x, τ (Ideal.Quotient.mk J x) = σ x := by
  dsimp
  let J := I.map (algebraMap A C)
  obtain ⟨τ, hτ, hτet, hσ⟩ := quotient_retraction_etale I σ
  let : Algebra (C ⧸ J) (A ⧸ I) := τ.toRingHom.toAlgebra
  have : Algebra.Etale (C ⧸ J) (A ⧸ I) := hτet.toAlgebra
  have hsurj : Function.Surjective (algebraMap (C ⧸ J) (A ⧸ I)) := fun x =>
    ⟨(Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map) x, RingHom.congr_fun hτ x⟩
  obtain ⟨e, he, hker, hloc⟩ :=
    Algebra.exists_isIdempotentElem_isLocalizationAway_of_surjective
      (C ⧸ J) (A ⧸ I) hsurj
  exact ⟨τ, e, hτ, he, hker, hloc, hσ⟩

/-- Two localizations away from the same element identify the base map of a retraction with a
ring equivalence. -/
private theorem bijective_base_map_of_localization_retraction
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra S R] [Algebra S T] (f : R →+* S)
    (h : (algebraMap S R).comp f = RingHom.id R) (e : S)
    [IsLocalization.Away e R] [IsLocalization.Away e T] :
    Function.Bijective ((algebraMap S T).comp f) ∧
      ∀ x, ((algebraMap S T).comp f) (algebraMap S R x) = algebraMap S T x := by
  let E : R ≃ₐ[S] T := IsLocalization.algEquiv (Submonoid.powers e) R T
  have hE : E.toRingHom = (algebraMap S T).comp f := RingHom.ext fun r =>
    (congrArg E (RingHom.congr_fun h r).symm).trans (E.commutes (f r))
  rw [← hE]
  exact ⟨E.bijective, E.commutes⟩

/-- An étale algebra with a closed-fibre section has a principal localization whose closed
fibre is precisely the base quotient. -/
private theorem exists_localization_bijective_closedFiber
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Etale A C] (I : Ideal A) (σ : C →ₐ[A] A ⧸ I) :
    let J := I.map (algebraMap A C)
    let q : (A ⧸ I) →+* (C ⧸ J) :=
      Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map
    ∃ g : C,
      let K := J.map (algebraMap C (Localization.Away g))
      let qg : (C ⧸ J) →+* ((Localization.Away g) ⧸ K) :=
        Ideal.quotientMap K (algebraMap C (Localization.Away g)) Ideal.le_comap_map
      Function.Bijective (qg.comp q) ∧ IsUnit (σ g) ∧
      ∀ x, (qg.comp q) (σ x) =
        Ideal.Quotient.mk K (algebraMap C (Localization.Away g) x) := by
  dsimp
  let J := I.map (algebraMap A C)
  obtain ⟨τ, e, hτ, he, _, hloc, hσ⟩ := quotient_retraction_idempotent I σ
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective e
  refine ⟨g, ?_⟩
  let L := Localization.Away g
  let K := J.map (algebraMap C L)
  let q : (A ⧸ I) →+* (C ⧸ J) :=
    Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map
  let qg : (C ⧸ J) →+* (L ⧸ K) :=
    Ideal.quotientMap K (algebraMap C L) Ideal.le_comap_map
  let : Algebra (C ⧸ J) (L ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hlocL : IsLocalization.Away e (L ⧸ K) := by
    have hm : Algebra.algebraMapSubmonoid (C ⧸ J) (Submonoid.powers g) =
        Submonoid.powers e := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact congrArg Submonoid.powers hg
    show IsLocalization (Submonoid.powers e) _
    rw [← hm]
    infer_instance
  let : Algebra (C ⧸ J) (A ⧸ I) := τ.toRingHom.toAlgebra
  have : IsLocalization.Away e (A ⧸ I) := hloc
  have : IsLocalization.Away e (L ⧸ K) := hlocL
  have hbij := bijective_base_map_of_localization_retraction
    (T := L ⧸ K) q hτ e
  show Function.Bijective (qg.comp q) ∧ IsUnit (σ g) ∧
    ∀ x, (qg.comp q) (σ x) = Ideal.Quotient.mk K (algebraMap C L x)
  have hqg : qg = algebraMap (C ⧸ J) (L ⧸ K) := rfl
  rw [hqg]
  refine ⟨hbij.1, ?_, ?_⟩
  · rw [← hσ g, hg]
    exact IsLocalization.Away.algebraMap_isUnit e
  · intro x
    rw [← hσ x]
    exact hbij.2 (Ideal.Quotient.mk J x)

/-- The localization of an étale algebra at a closed-fibre section preserves the quotient by
the ideal of the base ring. -/
private theorem exists_localization_bijective_baseQuotient
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Etale A C] (I : Ideal A) (σ : C →ₐ[A] A ⧸ I) :
    ∃ g : C,
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A (Localization.Away g)))
          (algebraMap A (Localization.Away g)) Ideal.le_comap_map) ∧
      IsUnit (σ g) ∧
      ∀ x, (Ideal.quotientMap (I.map (algebraMap A (Localization.Away g)))
        (algebraMap A (Localization.Away g)) Ideal.le_comap_map) (σ x) =
        Ideal.Quotient.mk _ (algebraMap C (Localization.Away g) x) := by
  obtain ⟨g, hbij, hunit, hcomm⟩ := exists_localization_bijective_closedFiber I σ
  refine ⟨g, ?_⟩
  let J := I.map (algebraMap A C)
  let L := Localization.Away g
  let K := J.map (algebraMap C L)
  have hK : K = I.map (algebraMap A L) := by
    simp only [K, J, Ideal.map_map]
    rw [IsScalarTower.algebraMap_eq A C L]
  let e := Ideal.quotEquivOfEq hK
  let q : (A ⧸ I) →+* (C ⧸ J) :=
    Ideal.quotientMap J (algebraMap A C) Ideal.le_comap_map
  let qg : (C ⧸ J) →+* (L ⧸ K) :=
    Ideal.quotientMap K (algebraMap C L) Ideal.le_comap_map
  have hcomp : e.toRingHom.comp (qg.comp q) =
      Ideal.quotientMap (I.map (algebraMap A L)) (algebraMap A L)
        Ideal.le_comap_map := by
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply, q, qg, Ideal.quotientMap_mk,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    show e (Ideal.Quotient.mk K (algebraMap C L (algebraMap A C a))) = _
    rw [Ideal.quotEquivOfEq_mk]
    rfl
  refine ⟨?_, hunit, ?_⟩
  · rw [← hcomp]
    exact e.bijective.comp hbij
  · intro x
    rw [← hcomp]
    show e ((qg.comp q) (σ x)) = _
    rw [hcomm]
    exact Ideal.quotEquivOfEq_mk hK _

/-- A finite projective module is a summand of a finite free module, with a finite projective
complement. -/
theorem Module.exists_finite_projective_complement
    {R : Type u} [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    ∃ (n : ℕ) (K : Type u) (_ : AddCommGroup K) (_ : Module R K)
      (_ : Module.Finite R K) (_ : Module.Projective R K),
      Nonempty ((Fin n → R) ≃ₗ[R] P × K) := by
  obtain ⟨n, f, g, hf, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (R := R) (M := P)
  let K := LinearMap.ker f
  have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  have hKfin : Module.Finite R K :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
  let r : (Fin n → R) →ₗ[R] K :=
    (LinearMap.id - g.comp f).codRestrict K (by
      intro x
      show f (x - g (f x)) = 0
      simp only [map_sub]
      have h := LinearMap.congr_fun hfg (f x)
      simpa using congrArg (fun y : P => f x - y) h)
  have hr : r.comp K.subtype = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show x.1 - g (f x.1) = x.1
    simp [LinearMap.mem_ker.mp x.2]
  have hKproj : Module.Projective R K := Module.Projective.of_split K.subtype r hr
  let e : (Fin n → R) →ₗ[R] P × K := f.prod r
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      have hfx : f x = f y := congrArg Prod.fst hxy
      have hrx : (r x : Fin n → R) = r y :=
        congrArg (fun z : P × K => (z.2 : Fin n → R)) hxy
      have hx : x = g (f x) + (r x : Fin n → R) := by simp [r]
      have hy : y = g (f y) + (r y : Fin n → R) := by simp [r]
      rw [hx, hy, hfx, hrx]
    · intro ⟨p, k⟩
      refine ⟨g p + k.1, ?_⟩
      apply Prod.ext
      · show f (g p + k.1) = p
        rw [map_add, LinearMap.mem_ker.mp k.2, add_zero]
        exact LinearMap.congr_fun hfg p
      · apply Subtype.ext
        show (g p + k.1) - g (f (g p + k.1)) = k.1
        have h : f (g p) = p := LinearMap.congr_fun hfg p
        rw [map_add, LinearMap.mem_ker.mp k.2, add_zero, h]
        simp
  exact ⟨n, K, inferInstance, inferInstance, hKfin, hKproj,
    ⟨LinearEquiv.ofBijective e he⟩⟩

/-- The conormal module of the section on the closed fibre is finite projective. -/
private theorem closedFiber_conormal_finite_projective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (f : B →ₐ[A] (A ⧸ I)) [Algebra.Smooth A B] :
    let σ : TensorProduct A (A ⧸ I) B →ₐ[A ⧸ I] (A ⧸ I) :=
      AlgHom.liftEquiv A (A ⧸ I) B (A ⧸ I) f
    Module.Finite (A ⧸ I) (RingHom.ker σ.toRingHom).Cotangent ∧
      Module.Projective (A ⧸ I) (RingHom.ker σ.toRingHom).Cotangent := by
  dsimp
  exact conormal_finite_projective
    (AlgHom.liftEquiv A (A ⧸ I) B (A ⧸ I) f) inferInstance

/-- After an étale base change preserving the closed fibre, the conormal module of the
closed-fibre section has a complement which lifts to a finite projective module. -/
private theorem exists_etale_baseChange_conormal_complement
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (f : B →ₐ[A] (A ⧸ I)) [Algebra.Smooth A B] :
    let σ : TensorProduct A (A ⧸ I) B →ₐ[A ⧸ I] (A ⧸ I) :=
      AlgHom.liftEquiv A (A ⧸ I) B (A ⧸ I) f
    ∃ (n : ℕ) (Kbar : Type u) (_ : AddCommGroup Kbar) (_ : Module (A ⧸ I) Kbar)
      (_ : Module.Finite (A ⧸ I) Kbar) (_ : Module.Projective (A ⧸ I) Kbar),
      Nonempty ((Fin n → A ⧸ I) ≃ₗ[A ⧸ I]
        (RingHom.ker σ.toRingHom).Cotangent × Kbar) ∧
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A'),
        let J := I.map (algebraMap A A')
        let q : (A ⧸ I) →+* (A' ⧸ J) :=
          Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
        Algebra.Etale A A' ∧
        ∃ hq : Function.Bijective q,
        ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module A' K)
          (_ : Module.Finite A' K) (_ : Module.Projective A' K),
          Nonempty
            (Kbar ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.ofBijective q hq)]
              TensorProduct A' (A' ⧸ J) K) := by
  dsimp
  let Pbar := (RingHom.ker
    (AlgHom.liftEquiv A (A ⧸ I) B (A ⧸ I) f).toRingHom).Cotangent
  have hP := closedFiber_conormal_finite_projective I f
  let : Module.Finite (A ⧸ I) Pbar := hP.1
  let : Module.Projective (A ⧸ I) Pbar := hP.2
  obtain ⟨n, Kbar, hKadd, hKmod, hKfin, hKproj, he⟩ :=
    Module.exists_finite_projective_complement (R := A ⧸ I) Pbar
  exact ⟨n, Kbar, hKadd, hKmod, hKfin, hKproj, he,
    exists_etale_baseChange_finite_projective_lift I Kbar⟩

/-- Adjoining the symmetric algebra of a finite projective module preserves smoothness. -/
private theorem smooth_tensor_symmetricAlgebra
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (K : Type*) [AddCommGroup K] [Module A K]
    [Module.Finite A K] [Module.Projective A K] :
    Algebra.Smooth A (TensorProduct A B (SymmetricAlgebra A K)) := by
  have : Algebra.Smooth A (SymmetricAlgebra A K) :=
    (symmetricAlgebra_smooth_iff_finite_projective A K).2
      ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth B (TensorProduct A B (SymmetricAlgebra A K)) := inferInstance
  exact Algebra.Smooth.comp A B (TensorProduct A B (SymmetricAlgebra A K))

/-- The differentials of a finite symmetric algebra are the scalar extension of its generators. -/
private theorem exists_symmetricKaehlerEquiv
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Nonempty (KaehlerDifferential R (SymmetricAlgebra R M) ≃ₗ[SymmetricAlgebra R M]
      (SymmetricAlgebra R M) ⊗[R] M) := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let b := Pi.basisFun R (Fin n)
  let l : (Fin n → R) →ₗ[R] MvPolynomial (Fin n) R := b.constr R MvPolynomial.X
  let α : MvPolynomial (Fin n) R →ₐ[R] SymmetricAlgebra R M :=
    MvPolynomial.aeval (fun i => SymmetricAlgebra.ι R M (p (b i)))
  have hαl : α.toLinearMap.comp l = (SymmetricAlgebra.ι R M).comp p :=
    b.ext fun i => by simp [l, α]
  have hα : Function.Surjective α := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨MvPolynomial.C r, by simp [α]⟩
    | ι m =>
      obtain ⟨y, rfl⟩ := hp m
      exact ⟨l y, LinearMap.congr_fun hαl y⟩
    | mul x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x * y, map_mul α x y⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add α x y⟩
  obtain ⟨_, _, e, _⟩ := cotangentComplex_of_isSymmetricAlgebra n
    p.ker.subtype p Subtype.val_injective p.exact_subtype_ker_map hp
    (SymmetricAlgebra R M) (SymmetricAlgebra.ι R M)
    SymmetricAlgebra.isSymmetricAlgebra_ι α hα (by intro i; simp [α, b])
  exact ⟨e⟩

/-- A smooth algebra admits a smooth enlargement with free differentials and an augmentation. -/
private theorem smooth_enlargement_free_differentials
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (I : Ideal A) (f : B →ₐ[A] A ⧸ I) :
    ∃ (S : Type v) (_ : CommRing S) (_ : Algebra A S)
      (j : B →ₐ[A] S) (σ : S →ₐ[A] A ⧸ I),
      Algebra.Smooth A S ∧ Module.Free S (KaehlerDifferential A S) ∧ σ.comp j = f := by
  classical
  let W := KaehlerDifferential A B
  have : Module.Projective B W := Algebra.FormallySmooth.projective_kaehlerDifferential
  obtain ⟨n, K, hKadd, hKmod, hKfin, hKproj, ⟨ec⟩⟩ :=
    Module.exists_finite_projective_complement (R := B) W
  let S := SymmetricAlgebra B K
  let : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Smooth B S :=
    (symmetricAlgebra_smooth_iff_finite_projective B K).mpr
      ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth A S := Algebra.Smooth.comp A B S
  obtain ⟨eΩ⟩ := exists_symmetricKaehlerEquiv B K
  have : Module.Projective S (KaehlerDifferential B S) :=
    Module.Projective.of_equiv eΩ.symm
  let g := KaehlerDifferential.map A B S S
  have hg : Function.Surjective g := KaehlerDifferential.map_surjective A B S
  obtain ⟨l, hl⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have hsplit : ∃ k : KaehlerDifferential B S →ₗ[S] KaehlerDifferential A S,
      (KaehlerDifferential.map A B S S).comp k = LinearMap.id := ⟨l, hl⟩
  obtain ⟨e, _, _⟩ := (((KaehlerDifferential.exact_mapBaseChange_map A B S).split_tfae
    (KaehlerDifferential.mapBaseChange_injective A B S) hg).out 1 3).mp hsplit
  let ecS := LinearEquiv.baseChange B S _ _ ec
  let et : KaehlerDifferential A S ≃ₗ[S] (Fin n → S) :=
    e.trans (((LinearEquiv.refl S (S ⊗[B] W)).prodCongr eΩ).trans
      ((TensorProduct.prodRight B S S W K).symm.trans
        (ecS.symm.trans (TensorProduct.piScalarRight B S S (Fin n)))))
  let aug : S →ₐ[A] B := (SymmetricAlgebra.lift (0 : K →ₗ[B] B)).restrictScalars A
  refine ⟨S, inferInstance, inferInstance, IsScalarTower.toAlgHom A B S,
    f.comp aug, inferInstance, Module.Free.of_equiv et.symm, ?_⟩
  ext b
  show f (SymmetricAlgebra.lift (0 : K →ₗ[B] B) (algebraMap B S b)) = f b
  rw [AlgHom.commutes]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equations whose differentials form a basis cut out an étale quotient. -/
private theorem etale_quotient_of_exact_differential_basis
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.Smooth A S] {ι : Type*} [Finite ι] (values : ι → S)
    (basis : Module.Basis ι S (KaehlerDifferential A S))
    (hb : ∀ i, basis i = KaehlerDifferential.D A S (values i)) :
    Algebra.Etale A (S ⧸ Ideal.span (Set.range values)) := by
  classical
  let J := Ideal.span (Set.range values)
  let C := S ⧸ J
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ A J)
    Ideal.Quotient.mk_surjective
  have hJ : Ideal.span (Set.range values) = P.ker := by
    show J = RingHom.ker (Ideal.Quotient.mk J)
    exact (Ideal.mk_ker).symm
  let c : ι → P.Cotangent := fun i =>
    Algebra.Extension.Cotangent.mk (P := P) ⟨values i, hJ.le (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hc : Submodule.span C (Set.range c) = ⊤ :=
    Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P) values hJ
  let b : Module.Basis ι C P.CotangentSpace := basis.baseChange C
  let l : P.CotangentSpace →ₗ[C] P.Cotangent := b.constr C c
  have hl : P.cotangentComplex.comp l = LinearMap.id := by
    refine b.ext fun i => ?_
    show P.cotangentComplex (b.constr C c (b i)) = b i
    rw [Module.Basis.constr_basis]
    show 1 ⊗ₜ[S] KaehlerDifferential.D A S (values i) = (basis.baseChange C) i
    rw [Module.Basis.baseChange_apply, hb]
  have hls : Function.Surjective l := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hc]
    exact Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i => ⟨b i, b.constr_basis C c i⟩
  have hleft : l.comp P.cotangentComplex = LinearMap.id := by
    ext x
    obtain ⟨y, rfl⟩ := hls x
    exact congrArg l (LinearMap.congr_fun hl y)
  have : Algebra.FormallySmooth A P.Ring := (inferInstance : Algebra.FormallySmooth A S)
  have : Algebra.FormallySmooth A C :=
    P.formallySmooth_iff_split_injection.mpr ⟨l, hleft⟩
  have hz : P.toKaehler = 0 := by
    refine LinearMap.ext fun x => ?_
    show P.toKaehler x = 0
    have hx : P.cotangentComplex (l x) = x := LinearMap.congr_fun hl x
    rw [← hx]
    exact (Algebra.Extension.exact_cotangentComplex_toKaehler (P := P)).apply_apply_eq_zero (l x)
  have : Subsingleton (KaehlerDifferential A C) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Algebra.Extension.toKaehler_surjective (P := P) x
    obtain ⟨y, rfl⟩ := Algebra.Extension.toKaehler_surjective (P := P) y
    rw [hz]
    rfl
  have : Algebra.FormallyUnramified A C := ⟨inferInstance⟩
  have : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range values))
  exact Algebra.Etale.iff_formallyUnramified_and_smooth.mpr
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

/-- Determinants of a family commute with scalar extension. -/
private theorem basis_det_baseChange
    {R T M ι : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (v : ι → M) :
    (b.baseChange T).det (fun i => 1 ⊗ₜ[R] v i) = algebraMap R T (b.det v) := by
  simp only [Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.algebraMap_eq_smul_one]

/-- A free differential module has an exact differential basis near a closed-fibre section. -/
private theorem exact_differential_frame_near_section
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (I : Ideal A) (σ : S →ₐ[A] A ⧸ I)
    {ι : Type*} [Fintype ι] (basis : Module.Basis ι S (KaehlerDifferential A S)) :
    ∃ g : S, IsUnit (σ g) ∧
      ∃ (values : ι → S), (∀ i, σ (values i) = 0) ∧
        ∃ b : Module.Basis ι (Localization.Away g)
            (KaehlerDifferential A (Localization.Away g)),
          ∀ i, b i = KaehlerDifferential.D A (Localization.Away g)
            (algebraMap S (Localization.Away g) (values i)) := by
  classical
  let : Algebra S (A ⧸ I) := σ.toAlgebra
  have : IsScalarTower A S (A ⧸ I) := inferInstance
  have hs : Function.Surjective (algebraMap S (A ⧸ I)) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨algebraMap A S a, σ.commutes a⟩
  have : Subsingleton (KaehlerDifferential A (A ⧸ I)) :=
    KaehlerDifferential.subsingleton_of_surjective A (A ⧸ I) Ideal.Quotient.mk_surjective
  have hc : Function.Surjective (KaehlerDifferential.kerCotangentToTensor A S (A ⧸ I)) := by
    rw [← LinearMap.range_eq_top, KaehlerDifferential.range_kerCotangentToTensor A S (A ⧸ I) hs]
    simp [LinearMap.ker_eq_top.mpr (Subsingleton.elim _ (0 :
      (A ⧸ I) ⊗[S] KaehlerDifferential A S →ₗ[A ⧸ I] KaehlerDifferential A (A ⧸ I)))]
  let bbar := basis.baseChange (A ⧸ I)
  choose c hc using fun i => hc (bbar i)
  choose v hv using fun i => (RingHom.ker (algebraMap S (A ⧸ I))).toCotangent_surjective (c i)
  have hvD (i) : (1 : A ⧸ I) ⊗ₜ[S] KaehlerDifferential.D A S (v i).1 = bbar i := by
    rw [← KaehlerDifferential.kerCotangentToTensor_toCotangent, hv]
    exact hc i
  let d : ι → KaehlerDifferential A S := fun i => KaehlerDifferential.D A S (v i).1
  let g := basis.det d
  have hg : σ g = 1 := by
    show algebraMap S (A ⧸ I) (basis.det d) = 1
    rw [← basis_det_baseChange]
    have heq : (fun i => (1 : A ⧸ I) ⊗ₜ[S] d i) = bbar := funext hvD
    rw [heq]
    exact bbar.det_self
  refine ⟨g, hg ▸ isUnit_one, fun i => (v i).1, fun i => (v i).2, ?_⟩
  let L := Localization.Away g
  let bL := basis.baseChange L
  let dL : ι → L ⊗[S] KaehlerDifferential A S := fun i => 1 ⊗ₜ[S] d i
  have hdet : IsUnit (bL.det dL) := by
    rw [basis_det_baseChange]
    exact IsLocalization.Away.algebraMap_isUnit g
  let b' := Module.Basis.mk (bL.is_basis_iff_det.mpr hdet).1
    (bL.is_basis_iff_det.mpr hdet).2.ge
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A S L
  refine ⟨b'.map e, fun i => ?_⟩
  show e (b' i) = _
  rw [Module.Basis.mk_apply]
  show KaehlerDifferential.mapBaseChange A S L (1 ⊗ₜ[S] d i) = _
  simp only [d, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  rfl

/-- A section of a smooth algebra factors through an étale algebra. -/
private theorem exists_etale_factorization_of_smooth
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (I : Ideal A) (f : B →ₐ[A] A ⧸ I) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C)
      (j : B →ₐ[A] C) (σ : C →ₐ[A] A ⧸ I),
      Algebra.Etale A C ∧ σ.comp j = f := by
  classical
  obtain ⟨S, hSring, hSalg, j, σ, hSsmooth, hSfree, hj⟩ :=
    smooth_enlargement_free_differentials I f
  let := hSring
  let := hSalg
  let := hSsmooth
  let := hSfree
  obtain ⟨g, hg, values, hvalues, b, hb⟩ := exact_differential_frame_near_section I σ
    (Module.Free.chooseBasis S (KaehlerDifferential A S))
  let L := Localization.Away g
  let σL : L →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom g hg
  have hσL (x : S) : σL (algebraMap S L x) = σ x :=
    IsLocalization.Away.lift_eq g hg x
  let vL := fun i => algebraMap S L (values i)
  let K := Ideal.span (Set.range vL)
  have hK : K ≤ RingHom.ker σL.toRingHom := Ideal.span_le.mpr <| Set.range_subset_iff.mpr
    fun i => show σL (algebraMap S L (values i)) = 0 by rw [hσL, hvalues]
  let C := L ⧸ K
  let τ : C →ₐ[A] A ⧸ I := Ideal.Quotient.liftₐ K σL (fun x hx => hK hx)
  let k : B →ₐ[A] C := (Ideal.Quotient.mkₐ A K).comp
    ((IsScalarTower.toAlgHom A S L).comp j)
  have : Algebra.Smooth A L := Algebra.Smooth.comp A S L
  have : Algebra.Etale A C := etale_quotient_of_exact_differential_basis vL b hb
  refine ⟨C, inferInstance, inferInstance, k, τ, inferInstance, ?_⟩
  ext x
  show σL (algebraMap S L (j x)) = f x
  rw [hσL]
  exact AlgHom.congr_fun hj x

/-- If the quotient map already has a lift to the base, the base itself is a suitable étale
extension. -/
private theorem exists_etale_lift_of_lift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (f : B →ₐ[A] (A ⧸ I)) (g : B →ₐ[A] A)
    (hg : (Ideal.Quotient.mkₐ A I).comp g = f) :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A'),
      let J := I.map (algebraMap A A')
      let q : (A ⧸ I) →+* (A' ⧸ J) :=
        Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
      Algebra.Etale A A' ∧
      Function.Bijective q ∧
      ∃ f' : B →ₐ[A] A',
        q.comp f.toRingHom = (Ideal.Quotient.mk J).comp f'.toRingHom := by
  let A' := ULift.{v} A
  let : CommRing A' := inferInstance
  let : Algebra A A' := inferInstance
  let φ : A ≃ₐ[A] A' := (ULift.algEquiv (R := A)).symm
  refine ⟨A', inferInstance, inferInstance, Algebra.Etale.of_equiv φ, ?_, ?_⟩
  · have hinj : Function.Injective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
          Ideal.le_comap_map) := by
      apply Ideal.quotientMap_injective'
      rw [Ideal.comap_map_of_bijective (algebraMap A A') φ.bijective]
    have hsurj : Function.Surjective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
          Ideal.le_comap_map) :=
      Ideal.quotientMap_surjective φ.surjective
    exact ⟨hinj, hsurj⟩
  · refine ⟨φ.toAlgHom.comp g, RingHom.ext fun b => ?_⟩
    have hga : Ideal.Quotient.mk I (g b) = f b :=
      congrArg (fun (h : B →ₐ[A] (A ⧸ I)) => h b) hg
    show (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
      Ideal.le_comap_map) (f b) = Ideal.Quotient.mk _ (φ (g b))
    rw [← hga, Ideal.quotientMap_mk]
    rfl

/-- Formal smoothness lifts a map across a nilpotent ideal, so no change of base is needed. -/
private theorem exists_etale_lift_of_formallySmooth_nilpotent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (f : B →ₐ[A] (A ⧸ I)) [Algebra.FormallySmooth A B]
    (hI : IsNilpotent I) :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A'),
      let J := I.map (algebraMap A A')
      let q : (A ⧸ I) →+* (A' ⧸ J) :=
        Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
      Algebra.Etale A A' ∧
      Function.Bijective q ∧
      ∃ f' : B →ₐ[A] A',
        q.comp f.toRingHom = (Ideal.Quotient.mk J).comp f'.toRingHom := by
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift I hI f
  exact exists_etale_lift_of_lift I f g hg

/-- **Stacks 07M7.** A map from a smooth `A`-algebra `B` to `A ⧸ I` lifts to an étale
`A`-algebra which induces an isomorphism modulo the extension of `I`. -/
@[stacks 07M7]
theorem exists_etale_lift_of_smooth
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (f : B →ₐ[A] (A ⧸ I)) [Algebra.Smooth A B] :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A'),
      let J := I.map (algebraMap A A')
      let q : (A ⧸ I) →+* (A' ⧸ J) :=
        Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
      Algebra.Etale A A' ∧
      Function.Bijective q ∧
      ∃ f' : B →ₐ[A] A',
        q.comp f.toRingHom = (Ideal.Quotient.mk J).comp f'.toRingHom := by
  classical
  obtain ⟨C, hCring, hCalg, j, σ, hCet, hj⟩ :=
    exists_etale_factorization_of_smooth I f
  let := hCring
  let := hCalg
  let := hCet
  let C' := ULift.{u} C
  let e : C ≃ₐ[A] C' := (ULift.algEquiv (R := A)).symm
  have : Algebra.Etale A C' := Algebra.Etale.of_equiv e
  let σ' := σ.comp e.symm.toAlgHom
  obtain ⟨g, hbij, _, hcomm⟩ := exists_localization_bijective_baseQuotient I σ'
  let A' := Localization.Away g
  have : Algebra.Etale A A' := Algebra.Etale.comp A C' A'
  refine ⟨A', inferInstance, inferInstance, inferInstance, hbij,
    (IsScalarTower.toAlgHom A C' A').comp (e.toAlgHom.comp j), RingHom.ext fun b => ?_⟩
  have hσ : σ' (e (j b)) = f b := by
    show σ (e.symm (e (j b))) = f b
    rw [e.symm_apply_apply]
    exact AlgHom.congr_fun hj b
  show (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
    Ideal.le_comap_map) (f b) = Ideal.Quotient.mk _ (algebraMap C' A' (e (j b)))
  rw [← hσ]
  exact hcomm (e (j b))
