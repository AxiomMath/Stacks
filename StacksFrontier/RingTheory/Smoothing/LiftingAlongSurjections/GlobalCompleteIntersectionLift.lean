module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Different.Formula.SquarePresentation
public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Koszul.FlatQuotient
public import StacksFrontier.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smooth.SymmetricAlgebra
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension
public import StacksFrontier.RingTheory.Syntomic.BaseChange
public import StacksFrontier.RingTheory.Syntomic.Defs
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.RingTheory.Syntomic.Morphisms

/-!
# Lifting relative global complete intersections along a surjection

Let `R → R₀` be a surjective map of commutative rings with kernel `I`. This file contains the
first step of the lift of a syntomic `R₀`-algebra to a syntomic `R`-algebra: a syntomic algebra
is enlarged to a finite-type retract which is a relative global complete intersection with finite
projective conormal module (the improvement of a presentation of Tag 07CE, applied with the
trivial localization), and a relative global complete intersection over `R₀` lifts to one over
`R`, because the coefficients of its defining polynomials lift. It also records the canonical
`R₀`-algebra structure on the special fibre `A/IA` and its invariance under localizing at an
element congruent to `1` modulo `IA`.

## References

* [Stacks Project, Proposition 16.10.4, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/

@[expose] public section

open scoped TensorProduct

open RingTheory.Sequence

namespace Stacks.Smoothing

open Koszul

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u v w

/-- A surjection on the base ring lifts the coefficients of every polynomial presentation. -/
private theorem presentation_hasCoeffs_of_surjective
    {R R₀ S : Type*} [CommRing R] [CommRing R₀] [CommRing S]
    [Algebra R R₀] [Algebra R₀ S] [Algebra R S] [IsScalarTower R R₀ S]
    (hR : Function.Surjective (algebraMap R R₀))
    {ι σ : Type*} (P : Algebra.Presentation R₀ S ι σ) :
    P.HasCoeffs R := ⟨by simp [hR.range_eq]⟩

/-- The presentation model and the original algebra form a pushout square. -/
private theorem presentation_model_isPushout
    {R R₀ S ι σ : Type*} [CommRing R] [CommRing R₀] [CommRing S]
    [Algebra R R₀] [Algebra R₀ S] [Algebra R S] [IsScalarTower R R₀ S]
    (P : Algebra.Presentation R₀ S ι σ) [P.HasCoeffs R] :
    ∃ (_ : Algebra (P.ModelOfHasCoeffs R) S)
      (_ : IsScalarTower R (P.ModelOfHasCoeffs R) S),
      Algebra.IsPushout R R₀ (P.ModelOfHasCoeffs R) S := by
  let toS : P.ModelOfHasCoeffs R →ₐ[R] S :=
    ((P.tensorModelOfHasCoeffsHom R).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  let _ : Algebra (P.ModelOfHasCoeffs R) S := toS.toAlgebra
  have htower : IsScalarTower R (P.ModelOfHasCoeffs R) S :=
    IsScalarTower.of_algebraMap_eq fun x => (toS.commutes x).symm
  have halg (y : MvPolynomial ι R) :
      algebraMap (P.ModelOfHasCoeffs R) S (Ideal.Quotient.mk _ y) =
        MvPolynomial.aeval P.val y := by
    rw [show algebraMap (P.ModelOfHasCoeffs R) S (Ideal.Quotient.mk _ y) =
        P.tensorModelOfHasCoeffsHom R (1 ⊗ₜ[R] Ideal.Quotient.mk _ y) from rfl,
      P.tensorModelOfHasCoeffsHom_tmul, map_one, one_mul]
  refine ⟨_, htower, ⟨IsBaseChange.of_equiv
    (P.tensorModelOfHasCoeffsEquiv R).toLinearEquiv fun x => ?_⟩⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show (IsScalarTower.toAlgHom R (P.ModelOfHasCoeffs R) S).toLinearMap
      (Ideal.Quotient.mk _ y) = MvPolynomial.aeval P.val y from halg y]
  show P.tensorModelOfHasCoeffsEquiv R (1 ⊗ₜ[R] (Ideal.Quotient.mk _ y)) = _
  rw [P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul]

/-- The canonical `toAlgebra` structure is the one whose algebra map was given. -/
private theorem algebra_eq_toAlgebra_of_algebraMap
    (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] :
    (inferInstance : Algebra R S) = (algebraMap R S).toAlgebra :=
  (toAlgebra_algebraMap (R := R) (S := S)).symm

/-- A syntomic algebra is a local complete intersection as a ring map. -/
private theorem isLocalCompleteIntersection_of_syntomic
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hS : Algebra.Syntomic R S) : RingHom.IsLocalCompleteIntersection (algebraMap R S) := by
  let f : R →+* S := algebraMap R S
  let old : Algebra R S := inferInstance
  have halg : old = f.toAlgebra := by
    simpa only [old, f] using algebra_eq_toAlgebra_of_algebraMap R S
  let : Algebra R S := f.toAlgebra
  have hS' : @Algebra.Syntomic R _ S _ f.toAlgebra :=
    Eq.mp (congrArg (fun a : Algebra R S => @Algebra.Syntomic R _ S _ a) halg) hS
  exact (RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection f).mp hS' |>.2

/-- A local complete intersection presentation stays one after identifying a ring with its
localization away from `1`. -/
private theorem isLocalCompleteIntersection_away_one
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : RingHom.IsLocalCompleteIntersection f) :
    RingHom.IsLocalCompleteIntersection
      ((algebraMap S (Localization.Away (1 : S))).comp f) := by
  classical
  let : Algebra R S := f.toAlgebra
  let : IsLocalization.Away (1 : S) S :=
    IsLocalization.away_of_isUnit_of_bijective S isUnit_one Function.bijective_id
  rcases hf with ⟨_, n, p, hp, hreg⟩
  let T := Localization.Away (1 : S)
  let g : R →+* T := (algebraMap S T).comp f
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  let q : MvPolynomial (Fin n) R →ₐ[R] T := {
    toRingHom := (algebraMap S T).comp p.toRingHom
    commutes' := fun r => by
      show algebraMap S T (p (algebraMap R (MvPolynomial (Fin n) R) r)) = g r
      rw [p.commutes]
      rfl
  }
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨k, y, hy⟩ := IsLocalization.Away.surj (1 : S) x
    simp only [map_one, one_pow, mul_one] at hy
    obtain ⟨z, hz⟩ := hp y
    refine ⟨z, ?_⟩
    simpa [q, hz] using hy.symm
  have hinj : Function.Injective (algebraMap S T) :=
    (IsLocalization.atOne S T).injective
  have hker : RingHom.ker q.toRingHom = RingHom.ker p.toRingHom := by
    ext x
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show (algebraMap S T) (p x) = 0 ↔ p x = 0
    constructor
    · intro hx
      exact hinj (by simpa using hx)
    · intro hx
      simp [hx]
  have hftT : Algebra.FiniteType R T := Algebra.FiniteType.of_surjective q hq
  refine ⟨RingHom.finiteType_algebraMap.mpr hftT, n, q, hq, ?_⟩
  rwa [hker]

/-- A syntomic algebra has a finite-type enlargement which is a relative global complete
intersection over the base, with finite projective conormal module and free conormal presentation.
This is the improvement of a presentation of Tag 07CE, evaluated at the unit of the algebra, where
the localization is the algebra itself. -/
theorem exists_syntomic_free_conormal_enlargement
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (hA : Algebra.Syntomic R A) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Algebra.FiniteType A C) (g : C →ₐ[R] A)
      (n : ℕ) (P : Algebra.Generators R A (Fin n))
      (e : C ≃ₐ[A] SymmetricAlgebra A P.toExtension.Cotangent),
      Module.Finite A P.toExtension.Cotangent ∧
      Module.Projective A P.toExtension.Cotangent ∧
      (∀ c : C, g c = SymmetricAlgebra.algebraMapInv (e c)) ∧
      g.comp (IsScalarTower.toAlgHom R A C) = AlgHom.id R A ∧
      Algebra.Syntomic R C ∧
      Algebra.IsRelativeGlobalCompleteIntersection R C ∧
      (let A₁ := Localization.Away (1 : A)
       let C₁ := Localization.Away (algebraMap A C (1 : A))
       letI : Algebra A₁ C₁ := (Localization.awayMap (algebraMap A C) (1 : A)).toAlgebra
       Algebra.Smooth A₁ C₁ ∧ HasFreeConormalPresentation R C₁) := by
  let : Algebra.FinitePresentation R A := hA.finitePresentation
  let hlci := isLocalCompleteIntersection_of_syntomic R A hA
  let hlci₁ := isLocalCompleteIntersection_away_one (algebraMap R A) hlci
  obtain ⟨C, hC, aRC, aAC, htower, hft, g, n, P, e,
    hfinite, hprojective, haugmentation, hg, hprops⟩ :=
    exists_finiteType_retraction_improving_presentation R A
  have hSyn : Algebra.Syntomic R C := by
    let : Module.Finite A P.toExtension.Cotangent := hfinite
    let : Module.Projective A P.toExtension.Cotangent := hprojective hlci
    let : Algebra.Smooth A (SymmetricAlgebra A P.toExtension.Cotangent) :=
      (symmetricAlgebra_smooth_iff_finite_projective A P.toExtension.Cotangent).2
        ⟨hfinite, hprojective hlci⟩
    let : Algebra.Smooth A C := Algebra.Smooth.of_equiv e.symm
    let : Algebra.Syntomic R A := hA
    let : Algebra.Syntomic A C := Algebra.Smooth.syntomic A C
    exact Algebra.Syntomic.comp R A C
  have hAtOne :
      let A₁ := Localization.Away (1 : A)
      let C₁ := Localization.Away (algebraMap A C (1 : A))
      let : Algebra A₁ C₁ := (Localization.awayMap (algebraMap A C) (1 : A)).toAlgebra
      Algebra.Smooth A₁ C₁ ∧ HasFreeConormalPresentation R C₁ := by
    dsimp
    simpa only [show (algebraMap A (Localization.Away (1 : A))) 1 = 1 from
      map_one (algebraMap A (Localization.Away (1 : A)))] using
      hprops.1 1 hlci₁
  refine ⟨C, hC, aRC, aAC, htower, hft, g, n, P, e,
    hfinite, hprojective hlci, haugmentation, hg, hSyn, ?_, hAtOne⟩
  let C₁ := Localization.Away (algebraMap A C (1 : A))
  let : IsLocalization.Away (1 : C) C₁ := by
    convert (inferInstance : IsLocalization.Away (algebraMap A C (1 : A)) C₁) using 1
    simp
  let : Algebra.Syntomic R C := hSyn
  let : Algebra.Smooth C C₁ := Algebra.Smooth.of_isLocalization_Away (1 : C)
  let : Algebra.Syntomic C C₁ := Algebra.Smooth.syntomic C C₁
  let : Algebra.Syntomic R C₁ := Algebra.Syntomic.comp R C C₁
  have hGci₁ : Algebra.IsRelativeGlobalCompleteIntersection R C₁ :=
    syntomic_freeConormal_isRelativeGlobalCompleteIntersection hAtOne.2
  let : Algebra.IsRelativeGlobalCompleteIntersection R C₁ := hGci₁
  exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv
    ((IsLocalization.atOne C C₁).restrictScalars R).symm

/-- The quotient by the extension of the kernel inherits the canonical `R₀`-algebra structure.
This is the ring map induced by `R → R₀` and the structure map `R → A`. -/
noncomputable def specialFiberBaseMap
    (R R₀ A : Type*) [CommRing R] [CommRing R₀] [CommRing A]
    [Algebra R R₀] [Algebra R A]
    (hR : Function.Surjective (algebraMap R R₀)) :
    R₀ →+* A ⧸ Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)) := by
  let I := RingHom.ker (algebraMap R R₀)
  let J := Ideal.map (algebraMap R A) I
  let g : R →+* A ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap R A)
  have hker : RingHom.ker (algebraMap R R₀) ≤ RingHom.ker g := by
    intro r hr
    change Ideal.Quotient.mk J (algebraMap R A r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem (algebraMap R A) hr
  exact (algebraMap R R₀).liftOfSurjective hR ⟨g, hker⟩

/-- The induced map from `R₀` reduces to the structure map from `R` on representatives. -/
theorem specialFiberBaseMap_comp
    (R R₀ A : Type*) [CommRing R] [CommRing R₀] [CommRing A]
    [Algebra R R₀] [Algebra R A]
    (hR : Function.Surjective (algebraMap R R₀)) (r : R) :
    specialFiberBaseMap R R₀ A hR (algebraMap R R₀ r) =
      Ideal.Quotient.mk _ (algebraMap R A r) :=
  RingHom.liftOfSurjective_comp_apply _ hR _ r

/-- Compatibility on representatives lifts to compatibility with all `R₀`-scalars. -/
theorem ringEquiv_specialFiberBaseMap
    (R R₀ A₀ A : Type*) [CommRing R] [CommRing R₀] [CommRing A₀] [CommRing A]
    [Algebra R R₀] [Algebra R₀ A₀] [Algebra R A]
    (hR : Function.Surjective (algebraMap R R₀))
    (e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)))
    (he : ∀ r : R, e (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
      Ideal.Quotient.mk _ (algebraMap R A r)) (r₀ : R₀) :
    e (algebraMap R₀ A₀ r₀) = specialFiberBaseMap R R₀ A hR r₀ := by
  obtain ⟨r, rfl⟩ := hR r₀
  rw [he, specialFiberBaseMap_comp]

/-- The representative compatibility required in the statement is exactly compatibility with the
canonical `R₀`-algebra structure on the special fibre. -/
noncomputable def specialFiberAlgEquiv
    (R R₀ A₀ A : Type*) [CommRing R] [CommRing R₀] [CommRing A₀] [CommRing A]
    [Algebra R R₀] [Algebra R₀ A₀] [Algebra R A]
    (hR : Function.Surjective (algebraMap R R₀))
    (e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)))
    (he : ∀ r : R, e (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
      Ideal.Quotient.mk _ (algebraMap R A r)) :
    letI : Algebra R₀
        (A ⧸ Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀))) :=
      (specialFiberBaseMap R R₀ A hR).toAlgebra
    A₀ ≃ₐ[R₀] A ⧸ Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)) := by
  letI : Algebra R₀
      (A ⧸ Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀))) :=
    (specialFiberBaseMap R R₀ A hR).toAlgebra
  exact AlgEquiv.ofRingEquiv (f := e)
    (ringEquiv_specialFiberBaseMap R R₀ A₀ A hR e he)

/-- If `φ : A → S` is a surjection of `R`-algebras with kernel `I A` and `φ g` is a unit, then `S`
is the quotient of `A_g` by the extension of `I`. -/
private theorem exists_ringEquiv_localizationAway_quotient
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (I : Ideal R) (φ : A →ₐ[R] S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = I.map (algebraMap R A)) (g : A) (hu : IsUnit (φ g)) :
    ∃ e : S ≃+* Localization.Away g ⧸ I.map (algebraMap R (Localization.Away g)),
      ∀ r : R, e (algebraMap R S r) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.Away g) r) := by
  let ψ : Localization.Away g →ₐ[R] S := IsLocalization.Away.liftAlgHom (f := φ) g hu
  have hψ (a : A) : ψ (algebraMap A (Localization.Away g) a) = φ a :=
    IsLocalization.Away.lift_eq g hu a
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨a, rfl⟩ := hφ x
    exact ⟨algebraMap A (Localization.Away g) a, hψ a⟩
  have hkerψ : RingHom.ker ψ = I.map (algebraMap R (Localization.Away g)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, y, hy⟩ := IsLocalization.Away.surj g x
      have hu' : IsUnit (algebraMap A (Localization.Away g) g ^ k) :=
        (IsLocalization.Away.algebraMap_isUnit g).pow k
      rw [← Ideal.mul_unit_mem_iff_mem _ hu', hy]
      have hyzero : φ y = 0 := by
        rw [← hψ, ← hy, map_mul, RingHom.mem_ker.mp hx, zero_mul]
      have hy' : y ∈ I.map (algebraMap R A) := hker ▸ RingHom.mem_ker.mpr hyzero
      have := Ideal.mem_map_of_mem (algebraMap A (Localization.Away g)) hy'
      rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ← φ.commutes]
      exact RingHom.mem_ker.mp (hker.ge (Ideal.mem_map_of_mem _ hr))
  rw [← hkerψ]
  refine ⟨(RingHom.quotientKerEquivOfSurjective hψsurj).symm, fun r => ?_⟩
  rw [← ψ.commutes]
  exact RingHom.quotientKerEquivOfSurjective_symm_apply hψsurj _

/-- Localizing at an element equal to one on the special fibre preserves that fibre. -/
theorem specialFiber_equiv_localizationAway
    (R R₀ A₀ A : Type*) [CommRing R] [CommRing R₀] [CommRing A₀] [CommRing A]
    [Algebra R R₀] [Algebra R₀ A₀] [Algebra R A]
    (e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R A)
      (RingHom.ker (algebraMap R R₀)))
    (he : ∀ r : R, e (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
      Ideal.Quotient.mk _ (algebraMap R A r))
    (g : A) (hg : g - 1 ∈ Ideal.map (algebraMap R A)
      (RingHom.ker (algebraMap R R₀))) :
    ∃ e' : A₀ ≃+* Localization.Away g ⧸
        Ideal.map (algebraMap R (Localization.Away g))
          (RingHom.ker (algebraMap R R₀)),
      ∀ r : R, e' (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.Away g) r) := by
  let I : Ideal R := RingHom.ker (algebraMap R R₀)
  let J : Ideal A := I.map (algebraMap R A)
  let : Algebra R A₀ := ((algebraMap R₀ A₀).comp (algebraMap R R₀)).toAlgebra
  let φ : A →ₐ[R] A₀ := {
    toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk J)
    commutes' := fun r => e.symm_apply_eq.mpr (he r).symm
  }
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e x)
    refine ⟨a, ?_⟩
    apply e.injective
    simpa [φ] using ha
  have hφker : RingHom.ker φ.toRingHom = J := by
    rw [show φ.toRingHom = e.symm.toRingHom.comp (Ideal.Quotient.mk J) from rfl,
      RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]
  have hφg : φ g = 1 := by
    apply e.injective
    rw [map_one, show e (φ g) = Ideal.Quotient.mk J g from e.apply_symm_apply _]
    exact sub_eq_zero.mp (Ideal.Quotient.eq_zero_iff_mem.mpr hg)
  have hu : IsUnit (φ g) := hφg ▸ isUnit_one
  exact exists_ringEquiv_localizationAway_quotient I φ hφsurj hφker g hu

/-- A relative global complete intersection over a quotient lifts to one over the base. -/
theorem exists_relativeGlobalCompleteIntersection_lift
    (R : Type u) (R₀ : Type v) (S : Type*)
    [CommRing R] [CommRing R₀] [CommRing S]
    [Algebra R R₀] [Algebra R₀ S]
    (hR : Function.Surjective (algebraMap R R₀))
    [Algebra.IsRelativeGlobalCompleteIntersection R₀ S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Algebra.IsRelativeGlobalCompleteIntersection R T ∧
      ∃ e : S ≃+* T ⧸ Ideal.map (algebraMap R T)
          (RingHom.ker (algebraMap R R₀)),
        ∀ r : R, e (algebraMap R₀ S (algebraMap R R₀ r)) =
          Ideal.Quotient.mk _ (algebraMap R T r) := by
  classical
  let I := RingHom.ker (algebraMap R R₀)
  let : Algebra R S := ((algebraMap R₀ S).comp (algebraMap R R₀)).toAlgebra
  let : IsScalarTower R R₀ S := .of_algebraMap_eq fun _ => rfl
  obtain ⟨n, c, P, hP⟩ :=
    (inferInstance : Algebra.IsRelativeGlobalCompleteIntersection R₀ S).out
  let : P.IsRelativeGlobalCompleteIntersection := hP
  let : P.HasCoeffs R := presentation_hasCoeffs_of_surjective hR P
  let f : Fin c → MvPolynomial (Fin n) R := P.relationOfHasCoeffs R
  let B := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let Pn := Algebra.Presentation.naive (v := f)
  have := Pn.finitePresentation_of_isFinite
  obtain ⟨aBS, hBSTower, hpush⟩ :=
    presentation_model_isPushout (R := R) (R₀ := R₀) (S := S) P
  let : Algebra B S := aBS
  let : IsScalarTower R B S := hBSTower
  let : Algebra.IsPushout R R₀ B S := hpush
  let : Algebra.IsPushout R B R₀ S := hpush.symm
  have hbase : Function.Surjective (algebraMap B S) ∧
      RingHom.ker (algebraMap B S) = I.map (algebraMap R B) :=
    Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
      (R := R) (S := R₀) (R' := B) (S' := S) hR
  let hsurj := hbase.1
  let hker := hbase.2
  have key (q : Ideal B) [q.IsPrime] (hIq : I ≤ q.under R) :
      c ≤ n ∧ Algebra.relativeDimensionAt R q ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
    have hkq : RingHom.ker (algebraMap B S) ≤ q := by
      rwa [hker, Ideal.map_le_iff_le_comap]
    have hq'' : (q.map (algebraMap B S)).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj hkq
    have hcq : PrimeSpectrum.comap (algebraMap B S)
        ⟨q.map (algebraMap B S), hq''⟩ = ⟨q, ‹_›⟩ :=
      PrimeSpectrum.ext (by
        show (q.map (algebraMap B S)).comap (algebraMap B S) = q
        rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left,
          ← RingHom.ker_eq_comap_bot]
        exact hkq)
    have hdim := Algebra.IsPushout.relativeDimensionAt_comap_eq
      R B R₀ S ⟨q.map (algebraMap B S), hq''⟩
    rw [hcq] at hdim
    change Algebra.relativeDimensionAt R q = _ at hdim
    have hnt := Stacks.RegularSequence.FibrewiseLocus.nontrivial_fiber (R := R₀)
      (q.map (algebraMap B S))
    obtain ⟨hcn, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq (by
      simpa using hP.ringKrullDim_fiber_add_card_eq_card
        ((q.map (algebraMap B S)).under R₀) hnt)
    exact ⟨hcn, hdim ▸
      (Algebra.relativeDimensionAt_le_ringKrullDim_fiber
        (q.map (algebraMap B S))).trans hd.le⟩
  have hI : ∀ (p : Ideal R) [p.IsPrime], I ≤ p → Nontrivial (p.Fiber B) →
      ringKrullDim (p.Fiber B) + ((Nat.card (Fin c) : ℕ) : WithBot ℕ∞) =
        ((Nat.card (Fin n) : ℕ) : WithBot ℕ∞) := by
    intro p _ hIp hnt
    refine le_antisymm ?_ (Pn.baseChange p.ResidueField).natCard_le_ringKrullDim_add_natCard
    obtain ⟨x⟩ : Nonempty (PrimeSpectrum (p.Fiber B)) := inferInstance
    set q := x.asIdeal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B)
    have hunder : q.under R = p := by
      refine Eq.trans ?_ (Ideal.over_def x.asIdeal p).symm
      ext r
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
        Ideal.mem_comap, AlgHom.commutes]
    have hcn := (key q (hunder ▸ hIp)).1
    have hle := Algebra.ringKrullDim_fiber_le_of_relativeDimensionAt_le (S := B) p
      (N := ((n - c : ℕ) : WithBot ℕ∞)) fun q _ hq => (key q (hq ▸ hIp)).2
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    calc ringKrullDim (p.Fiber B) + (c : WithBot ℕ∞)
        ≤ ((n - c : ℕ) : WithBot ℕ∞) + c := by gcongr
      _ = n := by norm_cast; omega
  obtain ⟨h, hh1, hRG⟩ :=
    Pn.exists_sub_one_mem_map_isRelativeGlobalCompleteIntersection I hI
  let a := algebraMap Pn.Ring B h
  let T := Localization.Away a
  have hTGci : Algebra.IsRelativeGlobalCompleteIntersection R T :=
    .of_presentation (Pn.localizationAwayComp h T) (hP := hRG)
  have hIa : I.map (algebraMap R B) ≤ RingHom.ker (algebraMap B S) := hker.ge
  have ha : algebraMap B S a = 1 := by
    have hmem := hIa hh1
    rwa [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hu : IsUnit ((IsScalarTower.toAlgHom R B S).toRingHom a) := by
    show IsUnit (algebraMap B S a)
    rw [ha]
    exact isUnit_one
  obtain ⟨e, he⟩ := exists_ringEquiv_localizationAway_quotient I (IsScalarTower.toAlgHom R B S)
    hsurj hker a hu
  exact ⟨T, inferInstance, inferInstance, hTGci, e, fun r => by
    rw [← IsScalarTower.algebraMap_apply R R₀ S]
    exact he r⟩

end Stacks.Smoothing

end
