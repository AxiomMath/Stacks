module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.ResidueFieldTransport
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
import StacksFrontier.CategoryTheory.Sites.Hypercovering.ConstantPowerMatching

/-!
# Algebraization of a versal formal object: second-order descent

A part of `StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation`: descent of a
second-order comparison to the residue quotients, and the complete local restriction of an
object at a finite type point
(`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Elements
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

namespace Deformation.Artin

open Deformation.Artin.Approximation

universe u v w

/-! ### Descent of a second-order comparison to the residue quotients -/

/-- In the first adic quotient of a local ring a square-zero element vanishes. -/
private theorem sq_eq_zero_imp_eq_zero_quotient_pow_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    (y : R ⧸ maximalIdeal R ^ 1) (hy : y ^ 2 = 0) : y = 0 := by
  have : (maximalIdeal R ^ 1).IsMaximal := by
    rw [pow_one]
    exact maximalIdeal.isMaximal R
  have : Field (R ⧸ maximalIdeal R ^ 1) := Ideal.Quotient.field _
  exact pow_eq_zero_iff two_ne_zero |>.mp hy

/-- A ring map between the second infinitesimal neighbourhoods of two local rings
descends to their first adic quotients. -/
private theorem exists_quotientPow_one_descent
    {C R : Type u} [CommRing C] [IsLocalRing C] [CommRing R] [IsLocalRing R]
    (γ : (C ⧸ maximalIdeal C ^ 2) →+* (R ⧸ maximalIdeal R ^ 2)) :
    ∃ γ₀ : (C ⧸ maximalIdeal C ^ 1) →+* (R ⧸ maximalIdeal R ^ 1),
      γ₀.comp (Ideal.Quotient.factorPow (maximalIdeal C) (Nat.le_succ 1)) =
        (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ 1)).comp γ := by
  classical
  refine ⟨Ideal.Quotient.lift (maximalIdeal C ^ 1)
      ((Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ 1)).comp
        (γ.comp (Ideal.Quotient.mk (maximalIdeal C ^ 2)))) ?_, ?_⟩
  · intro a ha
    apply sq_eq_zero_imp_eq_zero_quotient_pow_one
    have h2 : a ^ 2 ∈ maximalIdeal C ^ 2 := by
      rw [pow_one] at ha
      exact Ideal.pow_mem_pow ha 2
    have hsq : (Ideal.Quotient.mk (maximalIdeal C ^ 2) a) ^ 2 = 0 := by
      rw [← map_pow]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 h2
    simp only [RingHom.comp_apply]
    rw [← map_pow, ← map_pow, hsq, map_zero, map_zero]
  · apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk, Ideal.Quotient.lift_mk]

/-- A ring isomorphism between the second infinitesimal neighbourhoods of two local
rings descends to an isomorphism of their first adic quotients. -/
private theorem exists_quotientPow_one_descent_equiv
    {C R : Type u} [CommRing C] [IsLocalRing C] [CommRing R] [IsLocalRing R]
    (γ : (C ⧸ maximalIdeal C ^ 2) ≃+* (R ⧸ maximalIdeal R ^ 2)) :
    ∃ γ₀ : (C ⧸ maximalIdeal C ^ 1) ≃+* (R ⧸ maximalIdeal R ^ 1),
      γ₀.toRingHom.comp
          (Ideal.Quotient.factorPow (maximalIdeal C) (Nat.le_succ 1)) =
        (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ 1)).comp
          γ.toRingHom := by
  classical
  obtain ⟨f, hf⟩ := exists_quotientPow_one_descent γ.toRingHom
  obtain ⟨g, hg⟩ := exists_quotientPow_one_descent γ.symm.toRingHom
  have hgf : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ 1)) x
    rw [← RingHom.comp_apply f, hf, RingHom.comp_apply, ← RingHom.comp_apply g, hg]
    simp
  have hfg : ∀ y, f (g y) = y := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ 1)) y
    rw [← RingHom.comp_apply g, hg, RingHom.comp_apply, ← RingHom.comp_apply f, hf]
    simp
  refine ⟨RingEquiv.ofBijective f
    (Function.bijective_iff_has_inverse.2 ⟨g, hgf, hfg⟩), ?_⟩
  exact hf

/-- A second-level isomorphism of formal objects descends to the closed fibres,
together with the ring isomorphism of residue quotients it induces on bases. -/
theorem exists_level_zero_iso_of_level_one_iso
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (hp : p.IsFiberedInGroupoids)
    (X Y : Deformation.Artin.FormalObject B S hS p)
    (e₁ : X.level 1 ≅ Y.level 1) :
    ∃ (γ₀ : (Y.base.R ⧸ maximalIdeal Y.base.R ^ 1) ≃+*
          (X.base.R ⧸ maximalIdeal X.base.R ^ 1))
        (β₀ : Deformation.Artin.truncationOver B S hS X.base X.contains 0 ⟶
          Deformation.Artin.truncationOver B S hS Y.base Y.contains 0)
        (ρ : X.level 0 ⟶ Y.level 0),
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β₀ =
            Spec.map (CommRingCat.ofHom γ₀.toRingHom) ∧
          p.IsHomLift β₀ ρ ∧ IsIso ρ ∧
          ρ ≫ Y.transition 0 = X.transition 0 ≫ e₁.hom := by
  classical
  let : CommRing X.base.R := X.base.commRing
  let : CommRing Y.base.R := Y.base.commRing
  let β₁ : Deformation.Artin.truncationOver B S hS X.base X.contains 1 ⟶
      Deformation.Artin.truncationOver B S hS Y.base Y.contains 1 :=
    eqToHom (X.level_eq 1).symm ≫ p.map e₁.hom ≫ eqToHom (Y.level_eq 1)
  have : IsIso β₁ := by
    dsimp only [β₁]
    infer_instance
  obtain ⟨γ, hγ⟩ := exists_ringEquiv_of_specIso
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapIso (asIso β₁))
  obtain ⟨γ₀, hγ₀⟩ := exists_quotientPow_one_descent_equiv γ
  let gs : X.base.truncation 0 ⟶ Y.base.truncation 0 :=
    Spec.map (CommRingCat.ofHom γ₀.toRingHom)
  have : IsIso gs := by
    show IsIso (Spec.map γ₀.toCommRingCatIso.hom)
    infer_instance
  have hγ' : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β₁ =
      Spec.map (CommRingCat.ofHom γ.toRingHom) := hγ.symm
  have hspec : Spec.map (CommRingCat.ofHom γ₀.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factorPow (maximalIdeal Y.base.R) (Nat.le_succ 1))) =
      Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factorPow (maximalIdeal X.base.R) (Nat.le_succ 1))) ≫
        Spec.map (CommRingCat.ofHom γ.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hγ₀]
  have hschemeSq : gs ≫ Y.base.truncationSucc 0 =
      X.base.truncationSucc 0 ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β₁ := by
    rw [hγ']
    exact hspec
  have hcomm : gs ≫ Y.base.truncationToS 0 = X.base.truncationToS 0 := by
    rw [← Deformation.Artin.FormalBase.truncationSucc_toS Y.base 0, ← Category.assoc,
      hschemeSq, Category.assoc]
    have hw := Over.w β₁
    have hw' := congrArg (fun f => f.hom) hw
    change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β₁ ≫
      Y.base.truncationToS 1 = X.base.truncationToS 1 at hw'
    rw [hw', Deformation.Artin.FormalBase.truncationSucc_toS X.base 0]
  let β₀iso : Deformation.Artin.truncationOver B S hS X.base X.contains 0 ≅
      Deformation.Artin.truncationOver B S hS Y.base Y.contains 0 :=
    Over.isoMk (ObjectProperty.isoMk _ (asIso gs)) (by
      apply ObjectProperty.hom_ext
      exact hcomm)
  have hβ₀map : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β₀iso.hom = gs := rfl
  have hsiteSq : β₀iso.hom ≫ Deformation.Artin.truncationOverSucc B S hS Y.base Y.contains 0 =
      Deformation.Artin.truncationOverSucc B S hS X.base X.contains 0 ≫ β₁ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hschemeSq
  let := X.transition_lift 0
  let := Y.transition_lift 0
  have hfacX := IsHomLift.fac' p
    (Deformation.Artin.truncationOverSucc B S hS X.base X.contains 0) (X.transition 0)
  have hfacY := IsHomLift.fac' p
    (Deformation.Artin.truncationOverSucc B S hS Y.base Y.contains 0) (Y.transition 0)
  obtain ⟨ρ, ⟨hρmap, hρfac⟩, -⟩ := hp.unique_lift (Y.transition 0)
    (X.transition 0 ≫ e₁.hom)
    (eqToHom (X.level_eq 0) ≫ β₀iso.hom ≫ eqToHom (Y.level_eq 0).symm) (by
      have hLHS : (eqToHom (X.level_eq 0) ≫ β₀iso.hom ≫
            eqToHom (Y.level_eq 0).symm) ≫ p.map (Y.transition 0) =
          eqToHom (X.level_eq 0) ≫ (β₀iso.hom ≫
            Deformation.Artin.truncationOverSucc B S hS Y.base Y.contains 0) ≫
            eqToHom (Y.level_eq 1).symm := by
        rw [hfacY]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
      have hRHS : p.map (X.transition 0 ≫ e₁.hom) =
          eqToHom (X.level_eq 0) ≫
            (Deformation.Artin.truncationOverSucc B S hS X.base X.contains 0 ≫ β₁) ≫
            eqToHom (Y.level_eq 1).symm := by
        rw [Functor.map_comp, hfacX]
        dsimp only [β₁]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [hLHS, hRHS, hsiteSq])
  have hρlift : p.IsHomLift β₀iso.hom ρ := by
    apply IsHomLift.of_fac' p _ _ (X.level_eq 0) (Y.level_eq 0)
    rw [hρmap]
  have : IsIso (p.map ρ) := by
    rw [hρmap]
    infer_instance
  have := stronglyCartesian_of_fibered hp ρ
  have : IsIso ρ := Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map ρ) ρ
  exact ⟨γ₀, β₀iso.hom, ρ, hβ₀map, hρlift, inferInstance, hρfac⟩

/-- An equality of objects of a slice category compares their structure morphisms. -/
theorem eqToHom_left_comp_hom {T : Scheme.{u}} {A A' : Over T} (h : A = A') :
    eqToHom (congrArg Over.left h) ≫ A'.hom = A.hom := by
  cases h
  simp

/-- An isomorphism between two field-valued points of a fibred category over a common
local base is the spectrum of an isomorphism of those residue fields as algebras over
the base. -/
theorem exists_algEquiv_of_fieldPoint_iso
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {Λ k κ : Type u} [CommRing Λ] [Field k] [Field κ] [Algebra Λ k] [Algebra Λ κ]
    (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ] {x₀ x₁ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : (p ⋙ Over.post B.inclusion).obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ))
    (ρ : x₀ ⟶ x₁) [IsIso ρ] :
    ∃ ε : κ ≃ₐ[Λ] k,
      eqToHom (congrArg Over.left hx₀).symm ≫
          ((p ⋙ Over.post B.inclusion).map ρ).left ≫
          eqToHom (congrArg Over.left hx₁) =
        Spec.map (CommRingCat.ofHom (ε.toRingHom : κ →+* k)) := by
  classical
  have : IsIso (((p ⋙ Over.post B.inclusion).map ρ).left) := by
    show IsIso ((Over.forget S).map ((p ⋙ Over.post B.inclusion).map ρ))
    infer_instance
  let w : Spec (.of k) ⟶ Spec (.of κ) :=
    eqToHom (congrArg Over.left hx₀).symm ≫
      ((p ⋙ Over.post B.inclusion).map ρ).left ≫
      eqToHom (congrArg Over.left hx₁)
  have : IsIso w := by
    dsimp only [w]
    infer_instance
  obtain ⟨ε₀, hε₀⟩ := exists_ringEquiv_of_specIso (asIso w)
  have hε₀' : Spec.map (CommRingCat.ofHom ε₀.toRingHom) = w := hε₀
  have hw1 : w ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
    dsimp only [w]
    rw [Category.assoc, Category.assoc,
      show eqToHom (congrArg Over.left hx₁) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ) =
          ((p ⋙ Over.post B.inclusion).obj x₁).hom from eqToHom_left_comp_hom hx₁,
      Over.w ((p ⋙ Over.post B.inclusion).map ρ),
      ← eqToHom_left_comp_hom hx₀, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rfl
  have hw2 : w ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := by
    rw [← cancel_mono iΛ, Category.assoc]
    exact hw1
  have hring : (ε₀.toRingHom : κ →+* k).comp (algebraMap Λ κ) = algebraMap Λ k := by
    have h := hw2
    rw [← hε₀', ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    have h2 := Spec.map_injective h
    exact congrArg (fun m : CommRingCat.of Λ ⟶ CommRingCat.of k => m.hom) h2
  refine ⟨AlgEquiv.ofRingEquiv (f := ε₀) (fun r => ?_), ?_⟩
  · exact congrArg (fun m : Λ →+* k => m r) hring
  · show w = _
    exact hε₀'.symm

/-- A ring isomorphism of local rings induces one on every adic quotient. -/
noncomputable def quotientPowRingEquivOfRingEquiv
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (e : R ≃+* T) (n : ℕ) :
    (R ⧸ maximalIdeal R ^ n) ≃+* (T ⧸ maximalIdeal T ^ n) := by
  refine Ideal.quotientEquiv (maximalIdeal R ^ n) (maximalIdeal T ^ n) e ?_
  rw [Ideal.map_pow,
    IsLocalRing.map_maximalIdeal_of_surjective (e : R →+* T) e.surjective]

/-- The induced isomorphism of adic quotients is compatible with the quotient maps. -/
private theorem quotientPowRingEquivOfRingEquiv_mk
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (e : R ≃+* T) (n : ℕ) (r : R) :
    quotientPowRingEquivOfRingEquiv e n (Ideal.Quotient.mk (maximalIdeal R ^ n) r) =
      Ideal.Quotient.mk (maximalIdeal T ^ n) (e r) := rfl

/-- A ring isomorphism of local rings commutes with the adic thickenings. -/
theorem adicThickeningι_comp_specMap
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (e : R ≃+* T) (n : ℕ) :
    AlgebraicGeometry.adicThickeningι T (maximalIdeal T) n ≫
        Spec.map (CommRingCat.ofHom (e.toRingHom : R →+* T)) =
      Spec.map (CommRingCat.ofHom
          (quotientPowRingEquivOfRingEquiv e (n + 1)).toRingHom) ≫
        AlgebraicGeometry.adicThickeningι R (maximalIdeal R) n := by
  have hring : (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))).comp (e.toRingHom : R →+* T) =
      (quotientPowRingEquivOfRingEquiv e (n + 1)).toRingHom.comp
        (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) :=
    RingHom.ext fun r => (quotientPowRingEquivOfRingEquiv_mk e (n + 1) r).symm
  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1)))) ≫
        Spec.map (CommRingCat.ofHom (e.toRingHom : R →+* T)) =
      Spec.map (CommRingCat.ofHom
          (quotientPowRingEquivOfRingEquiv e (n + 1)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    hring]

/-- An equality of complete bases is realized by a ring isomorphism of their rings. -/
theorem exists_formalBase_transport {S : Scheme.{u}}
    {A A' : Deformation.Artin.FormalBase S} (h : A = A') :
    ∃ e : A'.R ≃+* A.R,
      Spec.map (CommRingCat.ofHom (e.toRingHom : A'.R →+* A.R)) =
        eqToHom (congrArg (fun b : Deformation.Artin.FormalBase S => Spec (.of b.R)) h) := by
  cases h
  exact ⟨RingEquiv.refl _, by simp⟩

/-- Two morphisms out of the spectra of equal complete bases agree up to transport. -/
theorem heq_of_formalBase_eq_comp {S : Scheme.{u}} {W : Scheme.{u}}
    {A A' : Deformation.Artin.FormalBase S} (h : A = A')
    (f : Spec (CommRingCat.of A.R) ⟶ W) (f' : Spec (CommRingCat.of A'.R) ⟶ W)
    (hff' : f =
      eqToHom (congrArg (fun b : Deformation.Artin.FormalBase S => Spec (.of b.R)) h) ≫ f') :
    HEq f f' := by
  cases h
  simpa using hff'

/-- Reassociating a fourfold composite. -/
alias comp_assoc3 := Stacks.CategoryTheory.Hypercovering.assoc_out

/-- Reassociating an equality of composites against a further morphism. -/
theorem comp_assoc_eq_comp_assoc {C : Type*} [Category C] {V W X Y Z : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : V ⟶ Y) (d : Y ⟶ X) (h : a ≫ b = c ≫ d) (e : X ⟶ Z) :
    a ≫ b ≫ e = c ≫ d ≫ e := by
  rw [← Category.assoc, h, Category.assoc]

/-- An isomorphism of affine schemes over `S` compatible with the structure morphisms is an
isomorphism of the corresponding objects of the site. -/
noncomputable def siteObjectIsoOfSpecIso
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R T : Type u} [CommRing R] [CommRing T]
    (hR : B.Contains (Spec (.of R))) (hT : B.Contains (Spec (.of T)))
    (f : Spec (.of R) ⟶ S) (g : Spec (.of T) ⟶ S)
    (e : Spec (.of R) ≅ Spec (.of T)) (he : e.hom ≫ g = f) :
    siteObject B S hS hR f ≅ siteObject B S hS hT g :=
  Over.isoMk (ObjectProperty.isoMk _ e) (by
    apply ObjectProperty.hom_ext
    exact he)

/-- Transporting the statement that the closed point of a complete local base lies over a
given point of the base scheme along an equality of complete local bases. -/
theorem formalBase_toS_closedPoint_congr {S : Scheme.{u}}
    {A A' : Deformation.Artin.FormalBase S} (h : A = A') {s : S}
    (hs : A.toS (IsLocalRing.closedPoint A.R) = s) :
    A'.toS (IsLocalRing.closedPoint A'.R) = s := by
  cases h
  exact hs

/-- Reassociating a composite against an identification of its source. -/
theorem comp_eq_eqToHom_comp {C : Type*} [Category C] {X Y Z W : C}
    (h : X = Y) (h' : Y = X) (b : X ⟶ Z) (rest : Z ⟶ W) (a : Y ⟶ Z)
    (ha : a = eqToHom h' ≫ b) : b ≫ rest = eqToHom h ≫ a ≫ rest := by
  subst h
  simp [ha]

/-- An isomorphism of complete local algebras is surjective. -/
private theorem surjective_of_isIso_complete
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R T : Deformation.CompleteLocalAlgCat Λ k} (f : R ⟶ T) [IsIso f] :
    Function.Surjective f.hom := by
  intro t
  exact ⟨(inv f).hom t, congrArg (fun m : T ⟶ T => m.hom t) (IsIso.inv_hom_id f)⟩

/-- The composite of the canonical surjection onto an adic truncation with an isomorphism
out of that truncation is surjective. -/
theorem surjective_formalBaseQuotient_comp
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R T : Deformation.CompleteLocalAlgCat Λ k} (n : ℕ)
    (φ : Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj R n) ⟶ T)
    [IsIso φ] : Function.Surjective (formalBaseQuotient R n ≫ φ).hom := by
  intro y
  obtain ⟨z, hz⟩ := surjective_of_isIso_complete φ y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (I := Deformation.AdicTruncation.ideal R n) z
  exact ⟨r, by rw [← hz, ← hr]; rfl⟩

/-- The first adic quotient of the canonical surjection onto an adic quotient is the
quotient map of that quotient. -/
private theorem adicTruncation_functor_map_formalBaseQuotient_apply
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : Deformation.CompleteLocalAlgCat Λ k) (n : ℕ)
    (y : Deformation.AdicTruncation.obj R n) :
    ((Deformation.AdicTruncation.functor n).map (formalBaseQuotient R n)).hom y =
      Ideal.Quotient.mk (Deformation.AdicTruncation.ideal
        (Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj R n)) n) y := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

/-- The canonical surjections onto the adic quotients are natural for arbitrary maps of
those quotients. -/
private theorem adicTruncation_map_formalBaseQuotient_natural
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R T : Deformation.CompleteLocalAlgCat Λ k) (n : ℕ)
    (w : Deformation.AdicTruncation.obj R n ⟶ Deformation.AdicTruncation.obj T n) :
    (Deformation.AdicTruncation.functor n).map (formalBaseQuotient R n) ≫
        (Deformation.AdicTruncation.functor n).map (Deformation.artinianToComplete.map w) =
      w ≫ (Deformation.AdicTruncation.functor n).map (formalBaseQuotient T n) := by
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  have hL := adicTruncation_functor_map_formalBaseQuotient_apply R n x
  have hR := adicTruncation_functor_map_formalBaseQuotient_apply T n (w.hom x)
  show ((Deformation.AdicTruncation.functor n).map (Deformation.artinianToComplete.map w)).hom
      (((Deformation.AdicTruncation.functor n).map (formalBaseQuotient R n)).hom x) =
    ((Deformation.AdicTruncation.functor n).map (formalBaseQuotient T n)).hom (w.hom x)
  rw [hL, hR]
  rfl

/-- The first adic quotient of the canonical surjection followed by a transported
isomorphism, read as a composite with that isomorphism. -/
theorem adicTruncation_map_formalBaseQuotient_comp_eqToHom
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (A A' : Deformation.CompleteLocalAlgCat Λ k)
    (w : Deformation.AdicTruncation.obj A 1 ⟶ Deformation.AdicTruncation.obj A' 1)
    {T : Deformation.CompleteLocalAlgCat Λ k}
    (h : Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj A' 1) = T) :
    (Deformation.AdicTruncation.functor 1).map
        (formalBaseQuotient A 1 ≫
          (Deformation.artinianToComplete.map w ≫ eqToHom h)) =
      w ≫ (Deformation.AdicTruncation.functor 1).map
        (formalBaseQuotient A' 1 ≫ eqToHom h) := by
  simp only [Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (Deformation.AdicTruncation.functor 1).map (eqToHom h))
        (adicTruncation_map_formalBaseQuotient_natural A A' 1 w)).trans
      (Category.assoc _ _ _))

/-- A morphism of deformations is determined by its arrow. -/
theorem deformationMorphism_ext_of_arrow
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {d d' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (f g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ d d')
    (h : f.arrow = g.arrow) : f = g := by
  have hspec : Spec.map (CommRingCat.ofHom f.ringHom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom g.ringHom.hom.toRingHom) := by
    rw [← f.arrow_base, ← g.arrow_base, h]
  have hr : f.ringHom = g.ringHom := by
    apply Deformation.ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg
      (fun m : CommRingCat.of d.algebra ⟶ CommRingCat.of d'.algebra => m.hom x)
      (Spec.map_injective hspec)
  exact DeformationMorphism.ext_of_components iΛ q x₀ hx₀ hr h

/-- An arrow between the points of two deformations which is compatible with their
structure arrows is a morphism of deformations. Its ring map is the `Spec`-preimage of the
induced map of affine bases; it is `Λ`-linear because `iΛ` is a monomorphism. -/
noncomputable def deformationMorphismOfArrow
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ] {x₀ : F}
    {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (d d' : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (arr : d'.point ⟶ d.point) (htri : d'.arrow ≫ arr = d.arrow) :
    Deformation.Artin.DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ d d' := by
  classical
  let ω : Spec (CommRingCat.of d'.algebra) ⟶ Spec (CommRingCat.of d.algebra) :=
    eqToHom (congrArg Over.left d'.base).symm ≫
      ((p ⋙ Over.post B.inclusion).map arr).left ≫
      eqToHom (congrArg Over.left d.base)
  let φ : CommRingCat.of d.algebra ⟶ CommRingCat.of d'.algebra :=
    AlgebraicGeometry.Spec.preimage ω
  have hφ : Spec.map φ = ω := AlgebraicGeometry.Spec.map_preimage ω
  have hΛlin : φ.hom.comp (algebraMap Λ d.algebra) = algebraMap Λ d'.algebra := by
    have hw1 : ω ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) ≫ iΛ) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ d'.algebra)) ≫ iΛ := by
      dsimp only [ω]
      rw [Category.assoc, Category.assoc,
        show eqToHom (congrArg Over.left d.base) ≫
              (Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) ≫ iΛ) =
            ((p ⋙ Over.post B.inclusion).obj d.point).hom from
          eqToHom_left_comp_hom d.base,
        Over.w ((p ⋙ Over.post B.inclusion).map arr),
        ← eqToHom_left_comp_hom d'.base, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rfl
    have hw2 : ω ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ d'.algebra)) := by
      rw [← cancel_mono iΛ, Category.assoc]
      exact hw1
    rw [← hφ, ← Spec.map_comp] at hw2
    exact congrArg (fun m : CommRingCat.of Λ ⟶ CommRingCat.of d'.algebra => m.hom)
      (Spec.map_injective hw2)
  have hres : (Deformation.Artin.residueMap d'.algebra).comp φ.hom =
      Deformation.Artin.residueMap d.algebra := by
    have h3 : Spec.map (CommRingCat.ofHom
          ((Deformation.Artin.residueMap d'.algebra).comp φ.hom)) =
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap d.algebra)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hφ,
        ← d.arrow_base, ← d'.arrow_base]
      dsimp only [ω]
      rw [← htri]
      simp only [Functor.map_comp, Over.comp_left, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
    exact congrArg (fun m : CommRingCat.of d.algebra ⟶ CommRingCat.of k => m.hom)
      (Spec.map_injective h3)
  have hresapp : ∀ a : d.algebra,
      d'.algebra.residueEquiv (residue d'.algebra (φ.hom a)) =
        d.algebra.residueEquiv (residue d.algebra a) := fun a =>
    congrArg (fun m : d.algebra →+* k => m a) hres
  have hlocal : IsLocalHom φ.hom := by
    refine ⟨fun a hu => ?_⟩
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff] at hu
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    intro h0
    refine hu (d'.algebra.residueEquiv.injective ?_)
    rw [hresapp a, h0, map_zero, map_zero]
  exact
    { ringHom :=
        { hom := { __ := φ.hom
                   commutes' := fun r =>
                     congrArg (fun m : Λ →+* d'.algebra => m r) hΛlin }
          isLocal := hlocal
          residue_comm := hresapp }
      arrow := arr
      triangle := htri
      arrow_base := hφ.symm }

theorem deformationMorphismOfArrow_arrow
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ] {x₀ : F}
    {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (d d' : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (arr : d'.point ⟶ d.point) (htri : d'.arrow ≫ arr = d.arrow) :
    (deformationMorphismOfArrow iΛ d d' arr htri).arrow = arr := rfl

/-- **Stacks 0CXK**, in the direction used below: versality of the formal object attached to
a Cartesian restriction over the completed local ring gives versality at the point. -/
theorem isVersalAt_of_formalObject_isVersal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left)
    [IsLocallyNoetherian S] [LocallyOfFiniteType U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R)
    (g : Spec (.of ξ.base.R) ⟶ U.left)
    (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
      U.left.fromSpecStalk u₀)
    (hbase : ξ.base.toS = g ≫ U.hom)
    (r : xR.obj.1 ⟶ x)
    (hr : p.IsCartesian (p.map r) r)
    (hrbase : HEq
      ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
        p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
    (hΛstalk : CommRingCat.of Λ = S.presheaf.stalk (Deformation.Artin.basePoint U u₀))
    (iΛ : Spec (.of Λ) ⟶ S)
    (hiΛ : HEq iΛ (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)))
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : Deformation.Artin.FormalObject.IsVersal B S hS p hp ξ Λ iΛ hΛ) :
    Deformation.Artin.IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx :=
  (Deformation.Artin.isVersalAt_iff_isVersal B S hS p hp U x hx u₀ hu₀ xR ξ hξ e g hg
    hbase r hr hrbase Λ hΛstalk iΛ hiΛ hΛ).2 hversal

/-! ### The complete local restriction of an object at a finite type point -/

/-- **The complete local restriction of an object at a finite type point.** Let `x` be an
object of a category fibred in groupoids over the big fppf site of `S`, lying over a scheme
`U` of finite type over `S`, and let `u₀` be a finite type point of `U` whose completed local
ring `𝒪_{U,u₀}^∧` is small enough to belong to the site. Then `x` restricts to an object over
the completion: there is an object `xR` of `Deformation.Artin.CompleteLocalObjects` together
with a Cartesian arrow `r : xR ⟶ x`, a ring isomorphism `e` from `𝒪_{U,u₀}^∧` onto the chosen
complete local base of `xR`, and the two identifications of that base over `U` and over `S`
which say that the base arrow of `r` is the canonical morphism
`Spec 𝒪_{U,u₀}^∧ ⟶ Spec 𝒪_{U,u₀} ⟶ U` read through `e`.

The three conjuncts are, in order, the hypotheses `_hr`, `hrbase` and `hbase` of the
versality comparison `Deformation.Artin.isVersalAt_iff_isVersal` of **Stacks 0CXK**: that
comparison asks for exactly this package at `u₀`, and before this lemma the only construction
of it was the one buried in the proof of `Stacks 07XH`
(`Deformation.Artin.exists_finiteType_versal_approximation`), which runs the other way and
manufactures its own `U`, `u₀` and `x` from an effective versal formal object. Here nothing is
manufactured: `U`, `u₀` and `x` are given, and the completion of `Stacks 07XF` is formed at
`u₀` directly.

Site containment of `Spec 𝒪_{U,u₀}^∧` is a hypothesis because
`AlgebraicGeometry.BigFppfSite.Contains` is a bound on the size of a scheme, which no
geometric hypothesis on `U` supplies. It is the only such hypothesis: the containments of the
infinitesimal thickenings of the completion follow from it by
`Deformation.Artin.truncationContains`, so membership in
`Deformation.Artin.IsCompleteLocalObject` needs nothing beyond it. -/
public theorem exists_completeLocalObject_of_isFiniteTypePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : B.Contains
      (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)))) :
    ∃ (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
      (r : xR.obj.1 ⟶ x)
      (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
        (Deformation.Artin.chosenBase B S hS p xR.obj).R),
      p.IsCartesian (p.map r) r ∧
      ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
            p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀ ∧
      (Deformation.Artin.chosenBase B S hS p xR.obj).toS =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀ ≫ U.hom := by
  classical
  let C := AlgebraicGeometry.Scheme.completedLocalRing U.left u₀
  let g : Spec (.of C) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀) C)) ≫
      U.left.fromSpecStalk u₀
  let Cbase := completedFormalBase U u₀ hu₀
  -- The underlying scheme of the site object `x` lies over is `U.left`, and its structure
  -- morphism is `U.hom`, both read through `hx`.
  have hUL : ((p ⋙ Over.post B.inclusion).obj x).left = U.left := congrArg Over.left hx
  have hUhom : eqToHom hUL ≫ U.hom = ((p ⋙ Over.post B.inclusion).obj x).hom :=
    eqToHom_left_comp_hom hx
  have hgCbase : (g ≫ eqToHom hUL.symm) ≫ ((p ⋙ Over.post B.inclusion).obj x).hom =
      Cbase.toS := by
    rw [← hUhom, Category.assoc, ← Category.assoc (eqToHom hUL.symm), eqToHom_trans,
      eqToHom_refl, Category.id_comp]
    exact Category.assoc _ _ _
  -- The completion, as an object of the site over the given one.
  let iC : AlgebraicGeometry.siteObject B S hS hC Cbase.toS ⟶ p.obj x :=
    Over.homMk (ObjectProperty.homMk (X := B.obj hC) (Y := (p.obj x).left)
      (g ≫ eqToHom hUL.symm)) (by
        apply ObjectProperty.hom_ext
        exact hgCbase)
  obtain ⟨xC, rC, hrC⟩ := hp.exists_lift iC x rfl
  have hcartC : p.IsCartesian (p.map rC) rC := by
    let := stronglyCartesian_of_fibered hp rC
    infer_instance
  have hxC : p.obj xC = Deformation.Artin.baseOver B S hS Cbase hC :=
    domain_eq_of_isHomLift p iC rC hrC
  let xCF : Deformation.Artin.CompleteLocalObjectsFull B S hS p := ⟨xC, ⟨Cbase, hC, hxC⟩⟩
  let xCR : Deformation.Artin.CompleteLocalObjects B S hS p := ⟨xCF⟩
  obtain ⟨er, her⟩ := exists_chosenBase_ringEquiv p xCF Cbase hC hxC
  refine ⟨xCR, rC, er, hcartC, ?_, ?_⟩
  · -- Both sides are rewritten in the spelling `er` carries, which is the one the chosen
    -- base is stated in; `change` performs that identification once and for all, so that no
    -- later rewrite has to see through the two names of the completion.
    show ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xCR.obj).symm ≫
        p.map rC).left.hom ≫ eqToHom hUL) =
      Spec.map (CommRingCat.ofHom er.toRingHom) ≫ g
    have hrC' : p.map rC = eqToHom hxC ≫ iC ≫ eqToHom (rfl : p.obj x = p.obj x).symm :=
      map_eq_of_isHomLift p iC rC hrC hxC rfl
    have hnorm : (eqToHom (Deformation.Artin.chosenBase_eq B S hS p xCF).symm ≫
        p.map rC ≫ eqToHom (rfl : p.obj x = p.obj x)).left.hom =
          Spec.map (CommRingCat.ofHom er.toRingHom) ≫ (g ≫ eqToHom hUL.symm) := by
      rw [her, hrC']
      exact left_hom_normalize _ _ iC _ _
    have hnorm' : (eqToHom (Deformation.Artin.chosenBase_eq B S hS p xCR.obj).symm ≫
        p.map rC).left.hom =
          Spec.map (CommRingCat.ofHom er.toRingHom) ≫ (g ≫ eqToHom hUL.symm) := by
      simpa using hnorm
    have cancel : ∀ {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (h : W = Z),
        (a ≫ b ≫ eqToHom h.symm) ≫ eqToHom h = a ≫ b := by
      intro X Y Z W a b h
      subst h
      simp
    exact (congrArg (fun t => t ≫ eqToHom hUL) hnorm').trans
      (cancel (Spec.map (CommRingCat.ofHom er.toRingHom)) g hUL)
  · -- The two presentations of the base agree over `S` as well.
    have hbb : Deformation.Artin.baseOver B S hS
          (Deformation.Artin.chosenBase B S hS p xCF)
          (Deformation.Artin.chosenContains B S hS p xCF) =
        Deformation.Artin.baseOver B S hS Cbase hC :=
      (Deformation.Artin.chosenBase_eq B S hS p xCF).symm.trans hxC
    have hbbpost := congrArg ((Over.post B.inclusion).obj) hbb
    have hmap : (eqToHom hbb).left.hom = eqToHom (congrArg Over.left hbbpost) := by
      show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (eqToHom hbb) = _
      simp only [eqToHom_map]
      rfl
    have her' : Spec.map (CommRingCat.ofHom er.toRingHom) =
        eqToHom (congrArg Over.left hbbpost) := by
      rw [her, ← hmap, eqToHom_trans]
    have h3 := eqToHom_left_comp_hom hbbpost
    rw [← her'] at h3
    exact h3.symm.trans (Category.assoc _ _ _).symm

end Deformation.Artin

end
