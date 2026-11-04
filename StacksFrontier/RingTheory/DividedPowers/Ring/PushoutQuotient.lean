module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.SetTheory.Cardinal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Representable.SolutionSet
public import StacksFrontier.RingTheory.DividedPowers.Ring.Colimits

/-!
# Divided power rings: the quotient of a pushout

For a pushout square of divided power rings with legs `g : B ⟶ B''` and `g' : B' ⟶ B''`, the
induced map on quotients by the distinguished ideals is an isomorphism
`(B/I_B) ⊗_{A/I_A} (B'/I_{B'}) ≃+* B''/I_{B''}`.

## Main definitions

* `DividedPowerRing.quotientRingHom` — the map on quotients by the distinguished ideals induced
  by a morphism of divided power rings.

## Main results

* `DividedPowerRing.tensorProductQuotientEquivPushoutQuotient` — the quotient of a pushout by
  its distinguished ideal is the tensor product of the quotients of the two factors over the
  quotient of the base.

## References

* [Stacks Project, Tag 0H86](https://stacks.math.columbia.edu/tag/0H86)
-/

@[expose] public section

universe u

namespace DividedPowerRing

section PushoutQuotient

open CategoryTheory Limits
open scoped TensorProduct

private noncomputable abbrev zeroDPRing (C : Type u) [CommRing C] : DividedPowerRing.{u} :=
  ⟨C, ⊥, dividedPowersBot C⟩

private def toZeroDPRing (R : DividedPowerRing.{u}) {C : Type u} [CommRing C]
    (φ : R →+* C) (hφ : ∀ x ∈ R.ideal, φ x = 0) : R ⟶ zeroDPRing C := by
  refine ⟨φ, ?_, ?_⟩
  · exact Ideal.map_le_iff_le_comap.mpr (fun x hx => by simpa using hφ x hx)
  · intro n x hx
    by_cases hn : n = 0
    · subst n; rw [R.dividedPowers.dpow_zero hx, map_one]
      simp [dividedPowersBot, hφ x hx]
    · have hd := R.dividedPowers.dpow_mem hn hx
      simp [dividedPowersBot, hn, hφ _ hx, hφ _ hd]

/-- A morphism of divided power rings induces a ring homomorphism between the quotients by
their distinguished ideals. -/
@[implicit_reducible]
public def quotientRingHom {A B : DividedPowerRing.{u}} (f : A ⟶ B) :
    (A ⧸ A.ideal) →+* (B ⧸ B.ideal) :=
  Ideal.quotientMap B.ideal f.toRingHom
    (Ideal.map_le_iff_le_comap.mp f.ideal_comp)

private def quotientToZero (R : DividedPowerRing.{u}) {C : Type u} [CommRing C]
    (φ : (R ⧸ R.ideal) →+* C) : R ⟶ zeroDPRing C :=
  toZeroDPRing R (φ.comp (Ideal.Quotient.mk R.ideal))
    (by intro x hx; simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx])

private def zeroToQuotient (R : DividedPowerRing.{u}) {C : Type u} [CommRing C]
    (φ : R ⟶ zeroDPRing C) : (R ⧸ R.ideal) →+* C :=
  Ideal.Quotient.lift R.ideal φ.toRingHom
    (by intro x hx; simpa using (Ideal.map_le_iff_le_comap.mp φ.ideal_comp) hx)

/-- Precomposing `quotientToZero` with a divided power map is `quotientToZero` of the
precomposition on quotients. -/
private theorem comp_quotientToZero {R S : DividedPowerRing.{u}} {C : Type u} [CommRing C]
    (u : R ⟶ S) (φ : (S ⧸ S.ideal) →+* C) :
    u ≫ quotientToZero S φ = quotientToZero R (φ.comp (quotientRingHom u)) :=
  DividedPowers.DPMorphism.ext (funext fun _ => rfl)

/-- The induced map on quotients sends the class of `x` to the class of `f x`. -/
@[simp]
public theorem quotientRingHom_mk {A B : DividedPowerRing.{u}} (f : A ⟶ B) (x : A) :
    quotientRingHom f (Ideal.Quotient.mk A.ideal x) = Ideal.Quotient.mk B.ideal (f x) :=
  Ideal.quotientMap_mk

/-- The identity divided power map induces the identity on quotients. -/
@[simp]
public theorem quotientRingHom_id (A : DividedPowerRing.{u}) :
    quotientRingHom (𝟙 A) = RingHom.id (A ⧸ A.ideal) := by ext x; simp

/-- Passing to quotients is compatible with composition of divided power maps. -/
@[simp]
public lemma quotientRingHom_comp {A B C : DividedPowerRing.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    quotientRingHom (f ≫ g) = (quotientRingHom g).comp (quotientRingHom f) := by
  apply RingHom.ext; intro x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [quotientRingHom, Ideal.quotientMap_mk]; rfl

/-- Applying the quotient by the distinguished ideal to a pushout square of divided power rings
gives a pushout square of commutative rings. -/
public lemma quotient_isPushout {A B B' B'' : DividedPowerRing.{u}}
    (f : A ⟶ B) (f' : A ⟶ B') (g : B ⟶ B'') (g' : B' ⟶ B'')
    (h : IsPushout f f' g g') :
    IsPushout (CommRingCat.ofHom (quotientRingHom f))
      (CommRingCat.ofHom (quotientRingHom f'))
      (CommRingCat.ofHom (quotientRingHom g))
      (CommRingCat.ofHom (quotientRingHom g')) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, quotientRingHom_comp] using
      congrArg quotientRingHom h.w
  · intro T φ ψ heq h'eq
    apply CommRingCat.hom_ext; apply RingHom.ext; intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hh : (quotientToZero B'' φ.hom) = quotientToZero B'' ψ.hom := by
      apply h.hom_ext
      · rw [comp_quotientToZero, comp_quotientToZero]
        exact congrArg _ (congrArg CommRingCat.Hom.hom heq)
      · rw [comp_quotientToZero, comp_quotientToZero]
        exact congrArg _ (congrArg CommRingCat.Hom.hom h'eq)
    exact congrArg (fun k : B'' ⟶ zeroDPRing T => k x) hh
  · intro T φ ψ hw
    let φ' : B ⟶ zeroDPRing T := quotientToZero B φ.hom
    let ψ' : B' ⟶ zeroDPRing T := quotientToZero B' ψ.hom
    have hw' : f ≫ φ' = f' ≫ ψ' := by
      rw [comp_quotientToZero, comp_quotientToZero]
      exact congrArg _ (congrArg CommRingCat.Hom.hom hw)
    let k := h.desc φ' ψ' hw'
    refine ⟨CommRingCat.ofHom (zeroToQuotient B'' k), ?_, ?_⟩
    · apply CommRingCat.hom_ext; apply RingHom.ext; intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact congrArg (fun t : B ⟶ zeroDPRing T => t x) (h.inl_desc φ' ψ' hw')
    · apply CommRingCat.hom_ext; apply RingHom.ext; intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact congrArg (fun t : B' ⟶ zeroDPRing T => t x) (h.inr_desc φ' ψ' hw')

/-- For a pushout of divided power rings, the tensor product of the quotients of the two
factors over the quotient of the base is canonically isomorphic to the quotient of the
pushout. -/
@[stacks 0H86 "quotient_of_pushout"]
public noncomputable def tensorProductQuotientEquivPushoutQuotient
    {A B B' B'' : DividedPowerRing.{u}} (f : A ⟶ B) (f' : A ⟶ B')
    (g : B ⟶ B'') (g' : B' ⟶ B'') (h : IsPushout f f' g g') :
    letI : Algebra (A ⧸ A.ideal) (B ⧸ B.ideal) := (quotientRingHom f).toAlgebra
    letI : Algebra (A ⧸ A.ideal) (B' ⧸ B'.ideal) := (quotientRingHom f').toAlgebra
    {e : (B ⧸ B.ideal) ⊗[A ⧸ A.ideal] (B' ⧸ B'.ideal) ≃+* (B'' ⧸ B''.ideal) //
      ∀ (b : B) (b' : B'),
        e (Ideal.Quotient.mk B.ideal b ⊗ₜ[A ⧸ A.ideal] Ideal.Quotient.mk B'.ideal b') =
          Ideal.Quotient.mk B''.ideal (g b * g' b')} := by
  letI : Algebra (A ⧸ A.ideal) (B ⧸ B.ideal) := (quotientRingHom f).toAlgebra
  letI : Algebra (A ⧸ A.ideal) (B' ⧸ B'.ideal) := (quotientRingHom f').toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct (A ⧸ A.ideal)
    (B ⧸ B.ideal) (B' ⧸ B'.ideal)
  let hq := quotient_isPushout f f' g g' h
  let i := ht.isoIsPushout (CommRingCat.of (B ⧸ B.ideal))
    (CommRingCat.of (B' ⧸ B'.ideal)) hq
  refine ⟨i.commRingCatIsoToRingEquiv, ?_⟩
  intro b b'
  have hl := ht.inl_isoIsPushout_hom
    (CommRingCat.of (B ⧸ B.ideal)) (CommRingCat.of (B' ⧸ B'.ideal)) hq
  have hr := ht.inr_isoIsPushout_hom
    (CommRingCat.of (B ⧸ B.ideal)) (CommRingCat.of (B' ⧸ B'.ideal)) hq
  have hleft : i.hom (Algebra.TensorProduct.includeLeftRingHom
      (Ideal.Quotient.mk B.ideal b)) =
      quotientRingHom g (Ideal.Quotient.mk B.ideal b) :=
    congrArg (fun k : CommRingCat.of (B ⧸ B.ideal) ⟶
      CommRingCat.of (B'' ⧸ B''.ideal) => k (Ideal.Quotient.mk B.ideal b)) hl
  have hright : i.hom (Algebra.TensorProduct.includeRight.toRingHom
      (Ideal.Quotient.mk B'.ideal b')) =
      quotientRingHom g' (Ideal.Quotient.mk B'.ideal b') :=
    congrArg (fun k : CommRingCat.of (B' ⧸ B'.ideal) ⟶
      CommRingCat.of (B'' ⧸ B''.ideal) => k (Ideal.Quotient.mk B'.ideal b')) hr
  change i.hom.hom _ = _
  rw [show (Ideal.Quotient.mk B.ideal b ⊗ₜ[A ⧸ A.ideal]
      Ideal.Quotient.mk B'.ideal b') =
      Algebra.TensorProduct.includeLeftRingHom (Ideal.Quotient.mk B.ideal b) *
        Algebra.TensorProduct.includeRight.toRingHom
          (Ideal.Quotient.mk B'.ideal b') by simp]
  rw [map_mul, hleft, hright]; simp [quotientRingHom]; rfl

end PushoutQuotient

end DividedPowerRing
