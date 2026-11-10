module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.LengthCriterion
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# Algebraization of a versal formal object: levelwise comparisons and realizations

A part of `StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation`: closed points
and residue fields of the adic quotients, levelwise isomorphisms of formal objects from a
second-order comparison, realizations of formal objects in a predeformation category, and
the change-of-residue-field functor on Artinian local algebras.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

namespace Deformation.Artin

open Deformation.Artin.Approximation

universe u v w

/-- An isomorphism of formal objects identifies their complete local base rings. -/
noncomputable def formalBaseRingEquiv
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F]
    {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {X Y : Deformation.Artin.FormalObject B S hS p} (e : X ≅ Y) :
    X.base.R ≃+* Y.base.R := by
  letI : CommRing X.base.R := X.base.commRing
  letI : CommRing Y.base.R := Y.base.commRing
  exact ((Spec.fullyFaithful.preimageIso
    (formalBaseMapIso e)).unop.symm).commRingCatIsoToRingEquiv

/-- A surjective ring map between local rings sends the closed point of `Spec T` to that of
`Spec R`. -/
private theorem spec_map_closedPoint_of_surjective
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (g : R →+* T) (hg : Function.Surjective g) :
    Spec.map (CommRingCat.ofHom g) (closedPoint T) = closedPoint R :=
  have := IsLocalHom.of_surjective g hg
  Spec_closedPoint

theorem specIso_closedPoint
    {R T : Type u} [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T]
    (e : Spec (.of R) ≅ Spec (.of T)) :
    e.hom (closedPoint R) = closedPoint T := by
  obtain ⟨g, hg⟩ := exists_ringEquiv_of_specIso e
  rw [← hg]
  exact spec_map_closedPoint_of_surjective g.toRingHom g.surjective

theorem locallyFiniteType_and_quasiCompact_quotient_pow_one
    {A : Type u} [CommRing A] (I : Ideal A) {S : Scheme.{u}}
    (f : Spec (.of A) ⟶ S)
    (hlft : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) ≫ f))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) ≫ f)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f) := by
  let q : (A ⧸ I ^ (0 + 1)) ≃ₐ[A] A ⧸ I :=
    Ideal.quotientEquivAlgOfEq A (by simp)
  let e : Spec (.of (A ⧸ I)) ≅ Spec (.of (A ⧸ I ^ (0 + 1))) :=
    Scheme.Spec.mapIso q.toRingEquiv.toCommRingCatIso.op
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    dsimp [e]
    rw [← Spec.map_comp]
    congr 1
  have := hlft
  have := hqc
  rw [← he, Category.assoc]
  exact ⟨inferInstance, inferInstance⟩

theorem finiteTypePoint_of_isClosed {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) :
    AlgebraicGeometry.IsFiniteTypePoint x := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_isClosedImmersion).mp hx
  exact ⟨inferInstance, inferInstance⟩

/-- A ring equivalence modulo the square of the maximal ideals identifies the
residue fields. -/
noncomputable def residueFieldEquivOfSquareQuotientEquiv
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A]
    (m : Ideal A) (hm : m.IsMaximal)
    (φ : (R ⧸ maximalIdeal R ^ 2) ≃+* (A ⧸ m ^ 2)) :
    ResidueField R ≃+* A ⧸ m := by
  let QR := R ⧸ maximalIdeal R ^ 2
  let QA := A ⧸ m ^ 2
  letI : Nontrivial QR := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (show 2 ≠ 0 by decide)).trans_lt
      (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing QR := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (maximalIdeal R ^ 2)) Ideal.Quotient.mk_surjective
  letI : IsLocalRing QA := φ.isLocalRing
  have hφmax : Ideal.map φ (maximalIdeal QR) = maximalIdeal QA :=
    IsLocalRing.map_ringEquiv_maximalIdeal φ
  let qR : R →+* QR := Ideal.Quotient.mk (maximalIdeal R ^ 2)
  let qA : A →+* QA := Ideal.Quotient.mk (m ^ 2)
  have hpowR : maximalIdeal R ^ 2 ≤ maximalIdeal R :=
    Ideal.pow_le_self (show 2 ≠ 0 by decide)
  have hpowA : m ^ 2 ≤ m := Ideal.pow_le_self (show 2 ≠ 0 by decide)
  have hmaxMapR : Ideal.map qR (maximalIdeal R) = maximalIdeal QR :=
    IsLocalRing.map_maximalIdeal_of_surjective qR Ideal.Quotient.mk_surjective
  have hmaxMapA : (m.map qA).IsMaximal := by
    let e := DoubleQuot.quotQuotEquivQuotOfLE hpowA
    let : m.IsMaximal := hm
    let : Field (A ⧸ m) := Ideal.Quotient.field m
    let : IsField (A ⧸ m) := Field.toIsField _
    have hfield : IsField (QA ⧸ m.map qA) := by
      change IsField ((A ⧸ m ^ 2) ⧸ (m.map (Ideal.Quotient.mk (m ^ 2))))
      exact MulEquiv.isField (Field.toIsField (A ⧸ m)) e.toMulEquiv
    exact Ideal.Quotient.maximal_of_isField (m.map qA) hfield
  have hmaxMapA' : m.map qA = maximalIdeal QA :=
    IsLocalRing.eq_maximalIdeal hmaxMapA
  let eQ : ResidueField QR ≃+* ResidueField QA :=
    Ideal.quotientEquiv (maximalIdeal QR) (maximalIdeal QA) φ hφmax.symm
  let eR : ResidueField QR ≃+* ResidueField R :=
    ((Ideal.quotientEquiv (maximalIdeal QR) ((maximalIdeal R).map qR)
      (RingEquiv.refl QR) (by
        simpa using hmaxMapR)).trans
      (DoubleQuot.quotQuotEquivQuotOfLE hpowR))
  let eA : ResidueField QA ≃+* A ⧸ m :=
    ((Ideal.quotientEquiv (maximalIdeal QA) (m.map qA)
      (RingEquiv.refl QA) (by simpa using hmaxMapA')).trans
      (DoubleQuot.quotQuotEquivQuotOfLE hpowA))
  exact eR.symm.trans (eQ.trans eA)

/-- The base point of an affine scheme over `S` is the image of its point. -/
theorem basePoint_specOver (A : Type u) [CommRing A]
    (S : Scheme.{u}) (f : Spec (.of A) ⟶ S)
    (u₀ : Spec (.of A)) :
    Deformation.Artin.basePoint (Over.mk f) u₀ = f u₀ := by
  have h := Scheme.fromSpecResidueField_apply u₀
    (closedPoint ((Over.mk f).left.residueField u₀))
  exact congrArg f h

/-- The closed point of a quadratic maximal-ideal quotient lies over its defining ideal. -/
private theorem quotientPow_closedPoint
    (A : Type u) [CommRing A] (m : Ideal A) (hm : m.IsMaximal)
    [IsLocalRing (A ⧸ m ^ 2)] :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ 2))))
      (closedPoint (A ⧸ m ^ 2)) =
      (⟨m, hm.isPrime⟩ : Spec (.of A)) := by
  let : m.IsMaximal := hm
  let qA : A →+* A ⧸ m ^ 2 := Ideal.Quotient.mk (m ^ 2)
  have hpowA : m ^ 2 ≤ m := Ideal.pow_le_self (show 2 ≠ 0 by decide)
  have hmaxMapA : (m.map qA).IsMaximal := by
    let e := DoubleQuot.quotQuotEquivQuotOfLE hpowA
    let : Field (A ⧸ m) := Ideal.Quotient.field m
    exact Ideal.Quotient.maximal_of_isField (m.map qA)
      (MulEquiv.isField (Field.toIsField (A ⧸ m)) e.toMulEquiv)
  have hmaxMapA' : m.map qA = maximalIdeal (A ⧸ m ^ 2) :=
    IsLocalRing.eq_maximalIdeal hmaxMapA
  apply PrimeSpectrum.ext
  change (maximalIdeal (A ⧸ m ^ 2)).comap qA = m
  rw [← hmaxMapA', Ideal.comap_map_mk hpowA]

/-- A comparison through the second infinitesimal neighborhoods identifies
their images in the base scheme. -/
theorem point_eq_of_second_order_comparison
    (R A : Type u) [CommRing R] [IsLocalRing R] [CommRing A]
    (m : Ideal A) (hm : m.IsMaximal) (S : Scheme.{u})
    (fR : Spec (.of R) ⟶ S) (fA : Spec (.of A) ⟶ S)
    (φ : (R ⧸ maximalIdeal R ^ 2) ≃+* (A ⧸ m ^ 2))
    (hφ : Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ 2))) ≫ fA =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ 2))) ≫ fR) :
    fA (⟨m, hm.isPrime⟩ : Spec (.of A)) = fR (closedPoint R) := by
  let QR := R ⧸ maximalIdeal R ^ 2
  let QA := A ⧸ m ^ 2
  let : Nontrivial QR := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (show 2 ≠ 0 by decide)).trans_lt
      (maximalIdeal.isMaximal R).lt_top).ne
  let : IsLocalRing QR := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (maximalIdeal R ^ 2)) Ideal.Quotient.mk_surjective
  let : IsLocalRing QA := φ.isLocalRing
  have hφclosed :
      (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) (closedPoint QR) =
        closedPoint QA := by
    exact spec_map_closedPoint_of_surjective φ.symm.toRingHom φ.symm.surjective
  have hRclosed :
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ 2))))
        (closedPoint QR) = closedPoint R := by
    exact spec_map_closedPoint_of_surjective _ Ideal.Quotient.mk_surjective
  have hAclosed := quotientPow_closedPoint A m hm
  have h := congrArg (fun f : Spec (.of QR) ⟶ S => f (closedPoint QR)) hφ
  change fA ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ 2))))
    ((Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) (closedPoint QR))) =
    fR ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ 2))))
      (closedPoint QR)) at h
  rw [hφclosed, hAclosed, hRclosed] at h
  exact h

/-- A compatible family of levelwise isomorphisms is an isomorphism of formal objects. -/
private noncomputable def formalObjectIsoOfLevelwise
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F]
    {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (X Y : Deformation.Artin.FormalObject B S hS p)
    (e : ∀ n, X.level n ≅ Y.level n)
    (he : ∀ n, X.transition n ≫ (e (n + 1)).hom =
      (e n).hom ≫ Y.transition n) : X ≅ Y := by
  refine ⟨⟨fun n => (e n).hom, he⟩,
    ⟨fun n => (e n).inv, ?_⟩, ?_, ?_⟩
  · intro n
    apply (cancel_mono (e (n + 1)).hom).1
    calc
      (Y.transition n ≫ (e (n + 1)).inv) ≫ (e (n + 1)).hom =
          Y.transition n := by simp
      _ = (e n).inv ≫ ((e n).hom ≫ Y.transition n) := by simp
      _ = (e n).inv ≫ (X.transition n ≫ (e (n + 1)).hom) := by rw [he n]
      _ = ((e n).inv ≫ X.transition n) ≫ (e (n + 1)).hom := by rw [Category.assoc]
  · apply Deformation.Artin.FormalObject.Hom.ext
    intro n
    exact (e n).hom_inv_id
  · apply Deformation.Artin.FormalObject.Hom.ext
    intro n
    exact (e n).inv_hom_id

/-- A morphism at the second level extends when the target tower stabilizes there. -/
private theorem exists_formalHom_of_level_one
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (X Y : Deformation.FormalObject p) (a : X.base ⟶ Y.base)
    (a₁ : X.level 1 ⟶ Y.level 1)
    (ha₁ : p.IsHomLift (Deformation.AdicTruncation.map a 1) a₁)
    (hY : ∀ n, IsIso (Y.transition (n + 1))) :
    ∃ f : X ⟶ Y, f.base = a ∧ f.app 1 = a₁ := by
  let (n : ℕ) := hY n
  let (j : ℕ) : p.IsHomLift (Deformation.AdicTruncation.transition X.base j)
      (X.transition j) := X.transition_lift j
  let (j : ℕ) : p.IsHomLift (Deformation.AdicTruncation.transition Y.base j)
      (Y.transition j) := Y.transition_lift j
  let := ha₁
  let := X.transition_lift 0
  let := Y.transition_lift 0
  let : p.IsStronglyCocartesian (Deformation.AdicTruncation.transition X.base 0)
      (X.transition 0) :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp _ _ (X.transition_lift 0)
  let : p.IsHomLift
      ((Deformation.AdicTruncation.functor 1).map a ≫
        (Deformation.AdicTruncation.transitionNat 0).app Y.base)
      (a₁ ≫ Y.transition 0) :=
    IsHomLift.comp p (Deformation.AdicTruncation.map a 1)
      (Deformation.AdicTruncation.transition Y.base 0) a₁ (Y.transition 0)
  let a₀ : X.level 0 ⟶ Y.level 0 := Functor.IsStronglyCocartesian.map p
    (Deformation.AdicTruncation.transition X.base 0) (X.transition 0)
    ((Deformation.AdicTruncation.transitionNat 0).naturality a) (a₁ ≫ Y.transition 0)
  have ha₀ : p.IsHomLift (Deformation.AdicTruncation.map a 0) a₀ := by
    dsimp only [a₀]
    exact Functor.IsStronglyCocartesian.map_isHomLift p _ _ _ _
  have h₀ : X.transition 0 ≫ a₀ = a₁ ≫ Y.transition 0 := by
    dsimp only [a₀]
    exact Functor.IsStronglyCocartesian.fac _ _ _ _ _
  let app : (n : ℕ) → X.level n ⟶ Y.level n
    | 0 => a₀
    | n + 1 => Nat.rec a₁
      (fun n b => X.transition (n + 1) ≫ b ≫ inv (Y.transition (n + 1))) n
  have happ : ∀ n, p.IsHomLift (Deformation.AdicTruncation.map a n) (app n) := by
    intro n
    cases n with
    | zero => exact ha₀
    | succ n =>
      induction n with
      | zero => exact ha₁
      | succ n ih =>
        let : p.IsHomLift (Deformation.AdicTruncation.map a (n + 1))
            (app (n + 1)) := ih
        let := X.transition_lift (n + 1)
        let := Y.transition_lift (n + 1)
        have : IsIso (Deformation.AdicTruncation.transition Y.base (n + 1)) :=
          IsHomLift.isIso_of_lift_isIso p _ (Y.transition (n + 1))
        have h : Deformation.AdicTruncation.transition X.base (n + 1) ≫
            Deformation.AdicTruncation.map a (n + 1) ≫
              inv (Deformation.AdicTruncation.transition Y.base (n + 1)) =
            Deformation.AdicTruncation.map a (n + 2) := by
          have hnat : Deformation.AdicTruncation.map a (n + 2) ≫
              Deformation.AdicTruncation.transition Y.base (n + 1) =
            Deformation.AdicTruncation.transition X.base (n + 1) ≫
              Deformation.AdicTruncation.map a (n + 1) :=
            (Deformation.AdicTruncation.transitionNat (n + 1)).naturality a
          rw [← Category.assoc, ← hnat]
          simp
        rw [← h]
        change p.IsHomLift _ (X.transition (n + 1) ≫ app (n + 1) ≫
          inv (Y.transition (n + 1)))
        have hright : p.IsHomLift
            (Deformation.AdicTruncation.map a (n + 1) ≫
              inv (Deformation.AdicTruncation.transition Y.base (n + 1)))
            (app (n + 1) ≫ inv (Y.transition (n + 1))) :=
          @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
            (Deformation.AdicTruncation.map a (n + 1))
            (inv (Deformation.AdicTruncation.transition Y.base (n + 1)))
            (app (n + 1)) (inv (Y.transition (n + 1))) ih (by infer_instance)
        exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
          (Deformation.AdicTruncation.transition X.base (n + 1))
          (Deformation.AdicTruncation.map a (n + 1) ≫
            inv (Deformation.AdicTruncation.transition Y.base (n + 1)))
          (X.transition (n + 1)) (app (n + 1) ≫ inv (Y.transition (n + 1)))
          (X.transition_lift (n + 1)) hright
  refine ⟨{ base := a, app := app, app_lift := happ, naturality := ?_ }, rfl, rfl⟩
  intro n
  cases n with
  | zero => exact h₀
  | succ n =>
    change X.transition (n + 1) ≫ app (n + 1) =
      (X.transition (n + 1) ≫ app (n + 1) ≫ inv (Y.transition (n + 1))) ≫
        Y.transition (n + 1)
    simp

/-- A formal object over a ring with square-zero maximal ideal stabilizes at level one. -/
private theorem isIso_transition_of_maximalIdeal_sq_eq_bot
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (Y : Deformation.FormalObject p) (hY : maximalIdeal Y.base ^ 2 = ⊥)
    (n : ℕ) : IsIso (Y.transition (n + 1)) := by
  have hpow (j : ℕ) (hj : 2 ≤ j) : maximalIdeal Y.base ^ j = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right hj).trans_eq hY)
  let t := Deformation.AdicTruncation.transition Y.base (n + 1)
  have ht : Function.Bijective t.hom := by
    constructor
    · change Function.Injective (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := maximalIdeal Y.base) (Nat.le_succ (n + 2))))
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      apply Ideal.map_mk_eq_bot_of_le
      rw [hpow (n + 2) (by omega), hpow (n + 3) (by omega)]
    · exact Ideal.Quotient.factor_surjective
        (Ideal.pow_le_pow_right (I := maximalIdeal Y.base) (Nat.le_succ (n + 2)))
  have : IsIso t := isIso_of_bijective_artinianLocalHom t ht
  let : p.IsStronglyCocartesian t (Y.transition (n + 1)) :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp t _ (Y.transition_lift (n + 1))
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p t (Y.transition (n + 1))

/-- The defining power of the maximal ideal vanishes in an adic truncation. -/
private theorem maximalIdeal_pow_truncation_eq_bot
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : Deformation.CompleteLocalAlgCat Λ k) (n : ℕ) :
    maximalIdeal (Deformation.AdicTruncation.obj R n) ^ (n + 1) = ⊥ := by
  let f : R →+* Deformation.AdicTruncation.obj R n :=
    Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))
  rw [← map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le le_rfl

/-- A compatible second-level morphism and equal adic lengths identify a versal formal object. -/
theorem exists_formal_iso_of_second_level_of_length_eq
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ η : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ)
    (ηn : ℕ → Deformation.FormalObject p)
    (q : ∀ n, η ⟶ ηn n) (g : ∀ n, ηn (n + 1) ⟶ ηn n)
    (hq : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (formalBaseQuotient η.base n) (q n))
    (hg : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (Deformation.artinianToComplete.map
        (Deformation.AdicTruncation.transition η.base n)) (g n))
    (hqg : ∀ n, q (n + 1) ≫ g n = q n)
    (a : ξ.base ⟶ (ηn 1).base) (ha : Function.Surjective a.hom)
    (a₁ : ξ.level 1 ⟶ (ηn 1).level 1)
    (ha₁ : p.IsHomLift (Deformation.AdicTruncation.map a 1) a₁)
    (hlen : ∀ n,
      Module.length (Deformation.AdicTruncation.obj ξ.base n)
        (Deformation.AdicTruncation.obj ξ.base n) =
      Module.length (Deformation.AdicTruncation.obj η.base n)
        (Deformation.AdicTruncation.obj η.base n)) :
    Nonempty (ξ ≅ η) ∧ Deformation.IsVersal hp η := by
  let Q := Deformation.FormalObject.projection (p := p)
  let := hq 1
  have hbase : (ηn 1).base =
      Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj η.base 1) :=
    IsHomLift.codomain_eq Q (formalBaseQuotient η.base 1) (q 1)
  have hnil : maximalIdeal (ηn 1).base ^ 2 = ⊥ := by
    rw [hbase]
    exact maximalIdeal_pow_truncation_eq_bot η.base 1
  obtain ⟨f, hf, _⟩ := exists_formalHom_of_level_one hp ξ (ηn 1) a a₁ ha₁
    (isIso_transition_of_maximalIdeal_sq_eq_bot hp (ηn 1) hnil)
  apply exists_formal_iso_of_second_reduction_of_length_eq hp ξ η hξ
    ηn q g hq hg hqg f _ hlen
  rw [hf]
  exact ha

section Realization

attribute [local instance] Deformation.Artin.PredeformationConstruction.category

private def formalEvaluation
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F] {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (n : ℕ) : Deformation.FormalObject p ⥤ F where
  obj η := η.level n
  map a := a.app n
  map_id _ := rfl
  map_comp _ _ := rfl

-- Two heterogeneously equal morphisms become equal after conjugating by the
-- identifications of their sources and targets. MATHLIB REPLACES THIS:
-- `CategoryTheory.conj_eqToHom_iff_heq'`, Mathlib/CategoryTheory/EqToHom.lean:88. A
-- `private` re-declaration of one direction of it stood here.

theorem formalObjectIsoOfRealizations
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F]
    {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (D : Deformation.Artin.PredeformationConstruction iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (ξ ζ : Deformation.Artin.FormalObject B S hS p)
    (η θ : @Deformation.FormalObject _ _ _ _ _ D.carrier D.category D.projection)
    (hη : ∀ n, (D.objects (η.level n)).point = ξ.level n)
    (hθ : ∀ n, (D.objects (θ.level n)).point = ζ.level n)
    (tη : ∀ n, HEq (D.morphisms _ _ (η.transition n)).arrow (ξ.transition n))
    (tθ : ∀ n, HEq (D.morphisms _ _ (θ.transition n)).arrow (ζ.transition n))
    (e : η ≅ θ) : Nonempty (ξ ≅ ζ) := by
  let := D.category
  let G := deformationForget D
  let en (n : ℕ) : ξ.level n ≅ ζ.level n :=
    (eqToIso (hη n).symm) ≪≫
      G.mapIso ((formalEvaluation n).mapIso e).op.symm ≪≫
      eqToIso (hθ n)
  have hηt (n : ℕ) : eqToHom (hη n).symm ≫ G.map (η.transition n).op ≫
      eqToHom (hη (n + 1)) = ξ.transition n :=
    ((CategoryTheory.conj_eqToHom_iff_heq' _ _ (hη n).symm (hη (n + 1))).2 (tη n).symm).symm
  have hθt (n : ℕ) : eqToHom (hθ n).symm ≫ G.map (θ.transition n).op ≫
      eqToHom (hθ (n + 1)) = ζ.transition n :=
    ((CategoryTheory.conj_eqToHom_iff_heq' _ _ (hθ n).symm (hθ (n + 1))).2 (tθ n).symm).symm
  refine ⟨formalObjectIsoOfLevelwise ξ ζ en (fun n => ?_)⟩
  rw [← hηt n, ← hθt n]
  change (eqToHom (hη n).symm ≫ G.map (η.transition n).op ≫
      eqToHom (hη (n + 1))) ≫
      (eqToHom (hη (n + 1)).symm ≫ G.map (e.inv.app (n + 1)).op ≫
        eqToHom (hθ (n + 1))) =
    (eqToHom (hη n).symm ≫ G.map (e.inv.app n).op ≫ eqToHom (hθ n)) ≫
      (eqToHom (hθ n).symm ≫ G.map (θ.transition n).op ≫ eqToHom (hθ (n + 1)))
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h := congrArg (fun f => G.map f.op) (e.inv.naturality n)
  simp only [op_comp, Functor.map_comp] at h
  simpa only [Category.assoc] using congrArg
    (fun f => eqToHom (hη n).symm ≫ f ≫ eqToHom (hθ (n + 1))) h.symm

/-- The complete base with a specified identification of its residue field. -/
private noncomputable def formalCompleteBase
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (Y : Deformation.Artin.FormalObject B S hS p)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Algebra Λ Y.base.R] (e : ResidueField Y.base.R ≃ₐ[Λ] k) :
    Deformation.CompleteLocalAlgCat.{u, u, u} Λ k where
  carrier := Y.base.R
  completeLocal := ⟨Y.base.noetherian, Y.base.localRing, Y.base.complete⟩
  residueEquiv := e

private theorem formalLevel_base
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (Y : Deformation.Artin.FormalObject B S hS p)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Algebra Λ Y.base.R] (e : ResidueField Y.base.R ≃ₐ[Λ] k)
    (iΛ : Spec (.of Λ) ⟶ S)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ Y.base.R)) ≫ iΛ =
      Y.base.toS) (n : ℕ) :
    (p ⋙ Over.post B.inclusion).obj (Y.level n) = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ
        (Deformation.AdicTruncation.obj (formalCompleteBase Y e) n))) ≫ iΛ) := by
  have h : Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (maximalIdeal Y.base.R ^ (n + 1)))) ≫ Y.base.toS =
      Spec.map (CommRingCat.ofHom (algebraMap Λ
        (Deformation.AdicTruncation.obj (formalCompleteBase Y e) n))) ≫ iΛ := by
    rw [← hbase, ← Spec.map_comp_assoc]
    rfl
  exact (congrArg ((Over.post B.inclusion).obj) (Y.level_eq n)).trans
    (congrArg Over.mk h)

private theorem formalTransition_base
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (Y : Deformation.Artin.FormalObject B S hS p)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Algebra Λ Y.base.R] (e : ResidueField Y.base.R ≃ₐ[Λ] k)
    (iΛ : Spec (.of Λ) ⟶ S)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ Y.base.R)) ≫ iΛ =
      Y.base.toS) (n : ℕ) :
    eqToHom (congrArg Over.left (formalLevel_base Y e iΛ hbase n)).symm ≫
      ((p ⋙ Over.post B.inclusion).map (Y.transition n)).left ≫
      eqToHom (congrArg Over.left (formalLevel_base Y e iΛ hbase (n + 1))) =
    Spec.map (CommRingCat.ofHom
      (Deformation.AdicTruncation.transition (formalCompleteBase Y e) n).hom.toRingHom) := by
  let := Y.transition_lift n
  have h := IsHomLift.fac p
    (Deformation.Artin.truncationOverSucc B S hS Y.base Y.contains n) (Y.transition n)
  have h' := congrArg (fun f => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) h
  simp only [Functor.map_comp, eqToHom_map] at h'
  convert h'.symm using 1 <;> rfl

theorem deformationObject_arrow_heq
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀} (h : a = b) :
    HEq a.arrow b.arrow := by cases h; rfl

private theorem deformationMorphism_fields_heq
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b c d : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    {f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b}
    {g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ c d}
    (hac : a = c) (hbd : b = d) (h : HEq f g) :
    HEq f.ringHom g.ringHom ∧ HEq f.arrow g.arrow := by
  subst c; subst d; cases h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Compatible pointed levels realize a formal object in the fixed predeformation category. -/
private theorem exists_realization_of_point_arrows
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (Y : Deformation.Artin.FormalObject B S hS p)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Algebra Λ Y.base.R] (e : ResidueField Y.base.R ≃ₐ[Λ] k)
    (iΛ : Spec (.of Λ) ⟶ S)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ Y.base.R)) ≫ iΛ =
      Y.base.toS)
    (x₀ : F) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (a : ∀ n, x₀ ⟶ Y.level n)
    (ha : ∀ n, a n ≫ Y.transition n = a (n + 1))
    (hab : ∀ n, eqToHom (congrArg Over.left hx₀).symm ≫
        ((p ⋙ Over.post B.inclusion).map (a n)).left ≫
        eqToHom (congrArg Over.left (formalLevel_base Y e iΛ hbase n)) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap
        (Deformation.AdicTruncation.obj (formalCompleteBase Y e) n)))) :
    ∃ η : Deformation.FormalObject D.projection,
      η.base = formalCompleteBase Y e ∧
      (∀ n, (D.objects (η.level n)).point = Y.level n) ∧
      (∀ n, HEq (D.objects (η.level n)).arrow (a n)) ∧
      (∀ n, HEq (D.morphisms _ _ (η.transition n)).arrow (Y.transition n)) := by
  let T := formalCompleteBase Y e
  let z (n : ℕ) : Deformation.Artin.DeformationObject iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀ := {
    algebra := Deformation.AdicTruncation.obj T n
    point := Y.level n
    arrow := a n
    base := formalLevel_base Y e iΛ hbase n
    arrow_base := hab n }
  let Z (n : ℕ) := D.objects.symm (z n)
  have hZ (n : ℕ) : D.objects (Z n) = z n := D.objects.apply_symm_apply _
  have hZp (n : ℕ) : D.projection.obj (Z n) = Deformation.AdicTruncation.obj T n :=
    (D.object_projection _).trans (congrArg (fun z => z.algebra) (hZ n))
  have htrans (n : ℕ) :
      eqToHom (congrArg Over.left (z n).base).symm ≫
        ((p ⋙ Over.post B.inclusion).map (Y.transition n)).left ≫
        eqToHom (congrArg Over.left (z (n + 1)).base) =
      Spec.map (CommRingCat.ofHom (Deformation.AdicTruncation.transition T n).hom.toRingHom) :=
    formalTransition_base Y e iΛ hbase n
  let t (n : ℕ) : Deformation.Artin.DeformationMorphism iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀ (z (n + 1)) (z n) := {
    ringHom := Deformation.AdicTruncation.transition T n
    arrow := Y.transition n
    triangle := ha n
    arrow_base := htrans n }
  let t' (n : ℕ) : Deformation.Artin.DeformationMorphism iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀ (D.objects (Z (n + 1))) (D.objects (Z n)) :=
    (hZ (n + 1)).symm ▸ (hZ n).symm ▸ t n
  let f (n : ℕ) : Z (n + 1) ⟶ Z n := (D.morphisms _ _).symm (t' n)
  have hf (n : ℕ) : HEq (D.morphisms _ _ (f n)) (t n) :=
    (heq_of_eq ((D.morphisms _ _).apply_symm_apply (t' n))).trans (by
      dsimp only [t']
      simp only [eqRec_heq_iff]
      rfl)
  have hfl (n : ℕ) : D.projection.IsHomLift
      (Deformation.AdicTruncation.transition T n) (f n) := by
    apply IsHomLift.of_fac _ _ _ (hZp (n + 1)) (hZp n)
    have h := D.morphism_projection (f n)
    have hr := ((CategoryTheory.conj_eqToHom_iff_heq' _ _
      (congrArg (fun z => z.algebra) (hZ (n + 1))).symm
      (congrArg (fun z => z.algebra) (hZ n))).2
      (deformationMorphism_fields_heq (hZ (n + 1)) (hZ n) (hf n)).1.symm).symm
    dsimp only [t] at hr
    rw [← hr, ← h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine ⟨{ base := T
            level := Z
            level_eq := hZp
            transition := f
            transition_lift := hfl }, rfl, ?_, ?_, ?_⟩
  · intro n
    exact congrArg (fun z => z.point) (hZ n)
  · intro n
    exact deformationObject_arrow_heq (hZ n)
  · intro n
    exact (deformationMorphism_fields_heq (hZ (n + 1)) (hZ n) (hf n)).2
/-- A chosen closed-fibre identification realizes the whole formal object over that point. -/
private theorem exists_realization_of_closedPoint_arrow
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (Y : Deformation.Artin.FormalObject B S hS p)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Algebra Λ Y.base.R] (e : ResidueField Y.base.R ≃ₐ[Λ] k)
    (iΛ : Spec (.of Λ) ⟶ S)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ Y.base.R)) ≫ iΛ =
      Y.base.toS)
    (x₀ : F) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (a₀ : x₀ ⟶ Y.level 0)
    (ha₀ : eqToHom (congrArg Over.left hx₀).symm ≫
        ((p ⋙ Over.post B.inclusion).map a₀).left ≫
        eqToHom (congrArg Over.left (formalLevel_base Y e iΛ hbase 0)) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap
        (Deformation.AdicTruncation.obj (formalCompleteBase Y e) 0)))) :
    ∃ η : Deformation.FormalObject D.projection,
      η.base = formalCompleteBase Y e ∧
      (∀ n, (D.objects (η.level n)).point = Y.level n) ∧
      (∀ n, HEq (D.objects (η.level n)).arrow
        (a₀ ≫ Deformation.Artin.FormalObject.closedPointArrow Y n)) ∧
      (∀ n, HEq (D.morphisms _ _ (η.transition n)).arrow (Y.transition n)) := by
  let a (n : ℕ) := a₀ ≫ Deformation.Artin.FormalObject.closedPointArrow Y n
  have ha (n : ℕ) : a n ≫ Y.transition n = a (n + 1) := by
    simp only [a, Deformation.Artin.FormalObject.closedPointArrow, Category.assoc]
  apply exists_realization_of_point_arrows Y e iΛ hbase x₀ hx₀ D a ha
  intro n
  induction n with
  | zero =>
    simpa only [a, Deformation.Artin.FormalObject.closedPointArrow,
      Category.comp_id] using ha₀
  | succ n ih =>
    rw [← ha]
    simp only [Functor.map_comp, Over.comp_left]
    have ht := formalTransition_base Y e iΛ hbase n
    have hcomp := congrArg₂ (fun f g => f ≫ g) ih ht
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp] at hcomp
    simp only [Category.assoc]
    rw [hcomp]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (Deformation.AdicTruncation.transition (formalCompleteBase Y e) n).residue_comm r


end Realization

/-! ### Change of residue field and of predeformation category

The declarations in this section repeat those of the `Proof_07XY` development of
Tag 07XY, which builds the transport of versality between predeformation categories
at different base points and over different residue fields; that module is not
imported here, so they are restated. -/

universe uC vC uD vD uX vX uY vY

-- Formal objects agreeing on base, levels and transitions are equal:
-- `Deformation.FormalObject.ext`, public beside the structure and beside
-- `Deformation.FormalObject.Hom.ext` in `StacksFrontier.Deformation.FormalObject.Basic`
-- (already a direct public import here, so no new import edge). A `private` re-declaration
-- stood here.

def artinianChangeResidueField
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k') :
    Deformation.ArtinianLocalAlgCat.{u, u, v} Λ k ⥤
      Deformation.ArtinianLocalAlgCat.{u, u, w} Λ k' where
  obj A := { carrier := A, residueEquiv := A.residueEquiv.trans e }
  map f := {
    hom := f.hom
    isLocal := f.isLocal
    residue_comm := fun a => congrArg e (f.residue_comm a) }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private theorem artinianChangeResidueField_obj_carrier
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    (A : Deformation.ArtinianLocalAlgCat.{u, u, v} Λ k) :
    ((artinianChangeResidueField e).obj A).carrier = A.carrier := rfl

private theorem artinianChangeResidueField_map_hom
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    {A B : Deformation.ArtinianLocalAlgCat.{u, u, v} Λ k} (f : A ⟶ B) :
    ((artinianChangeResidueField e).map f).hom.toRingHom = f.hom.toRingHom := rfl

theorem artinianChangeResidueField_faithful
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k') :
    (artinianChangeResidueField e).Faithful := by
  refine ⟨fun {A B} f g h => ?_⟩
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  exact congrArg (fun m => m.hom a) h

theorem artinianChangeResidueField_full
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k') :
    (artinianChangeResidueField e).Full where
  map_surjective f := ⟨{
    hom := f.hom
    isLocal := f.isLocal
    residue_comm := fun a => e.injective (f.residue_comm a) }, by
      apply Deformation.ArtinianLocalAlgCat.hom_ext
      rfl⟩

private theorem artinianChangeResidueField_essSurj
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, w} Λ k') :
    ∃ A, Nonempty ((artinianChangeResidueField e).obj A ≅ B) := by
  let A : Deformation.ArtinianLocalAlgCat.{u, u, v} Λ k :=
    { carrier := B, residueEquiv := B.residueEquiv.trans e.symm }
  refine ⟨A, ⟨eqToIso ?_⟩⟩
  have he : (B.residueEquiv.trans e.symm).trans e = B.residueEquiv := by
    ext x
    exact e.apply_symm_apply _
  exact congrArg (fun E =>
    ({ carrier := B, residueEquiv := E } :
      Deformation.ArtinianLocalAlgCat.{u, u, w} Λ k')) he

private theorem artinianChangeResidueField_isEquivalence
    {Λ : Type u} {k : Type v} {k' : Type w} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k') :
    (artinianChangeResidueField e).IsEquivalence := by
  let := artinianChangeResidueField_faithful e
  let := artinianChangeResidueField_full e
  refine { essSurj := ⟨fun B => ?_⟩ }
  obtain ⟨A, h⟩ := artinianChangeResidueField_essSurj e B
  exact ⟨A, h⟩

theorem artinianChangeResidueField_residueMap
    {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Deformation.Artin.residueMap ((artinianChangeResidueField e).obj A) =
      e.toRingHom.comp (Deformation.Artin.residueMap A) := by
  ext a
  rfl
section
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  (p : X ⥤ C) (q : Y ⥤ D) (F : X ⥤ Y) (G : C ⥤ D)
  (h : F ⋙ q = p ⋙ G)
include h in
theorem isHomLift_map_of_commSq
    {A B : C} {a b : X} (f : A ⟶ B) (r : a ⟶ b) (hr : p.IsHomLift f r) :
    q.IsHomLift (G.map f) (F.map r) := by
  cases hr
  apply IsHomLift.of_commSq q _ _
    (congrArg (fun H : X ⥤ D => H.obj a) h)
    (congrArg (fun H : X ⥤ D => H.obj b) h)
  exact ⟨by simpa using (eqToHom h).naturality r⟩
end

section DeformationTransportHelpers
variable (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
variable {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S) (x₀ : X)
  (hxΛ : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

theorem predeformation_ringHom_id
    (D : Deformation.Artin.PredeformationConstruction iΛ q x₀ hxΛ) :
    letI := D.category
    ∀ a : D.carrier, (D.morphisms a a (𝟙 a)).ringHom = 𝟙 (D.objects a).algebra := by
  let := D.category
  intro a
  rw [← D.morphism_projection]
  simp

theorem predeformation_ringHom_comp
    (D : Deformation.Artin.PredeformationConstruction iΛ q x₀ hxΛ) :
    letI := D.category
    ∀ {a b c : D.carrier} (f : a ⟶ b) (g : b ⟶ c),
      (D.morphisms a c (f ≫ g)).ringHom =
        (D.morphisms a b f).ringHom ≫ (D.morphisms b c g).ringHom := by
  let := D.category
  intro a b c f g
  simp [← D.morphism_projection, Category.assoc]

end DeformationTransportHelpers

end Deformation.Artin

end
