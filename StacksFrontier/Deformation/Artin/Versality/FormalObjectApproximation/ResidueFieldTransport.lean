module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.Realization
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# Algebraization of a versal formal object: transport along a change of residue field

A part of `StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation`: transport of
deformation objects, predeformation categories, formal objects and versality along a change
of residue field.
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

section ResidueFieldTransport

attribute [local implicit_reducible] artinianChangeResidueField

section ChangeOfResidueField

/-- The change-of-residue-field functor on complete local algebras. -/
noncomputable def completeChangeResidueField {Λ : Type u} {k : Type v}
    {k' : Type w} [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') :
    Deformation.CompleteLocalAlgCat.{u, u, v} Λ k ⥤
      Deformation.CompleteLocalAlgCat.{u, u, w} Λ k' where
  obj A :=
    { carrier := A
      completeLocal := A.completeLocal
      residueEquiv := A.residueEquiv.trans e }
  map f :=
    { hom := f.hom
      isLocal := f.isLocal
      residue_comm := fun a => congrArg e (f.residue_comm a) }
  map_id _ := Deformation.CompleteLocalAlgCat.Hom.ext rfl
  map_comp _ _ := Deformation.CompleteLocalAlgCat.Hom.ext rfl

private theorem completeChangeResidueField_faithful {Λ : Type u} {k : Type v}
    {k' : Type w} [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') : (completeChangeResidueField e).Faithful := by
  refine ⟨fun {A B} f g h => ?_⟩
  exact Deformation.CompleteLocalAlgCat.Hom.ext
    (congrArg (fun m : (completeChangeResidueField e).obj A ⟶
      (completeChangeResidueField e).obj B => m.hom) h)

private theorem completeChangeResidueField_full {Λ : Type u} {k : Type v}
    {k' : Type w} [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') : (completeChangeResidueField e).Full where
  map_surjective f := ⟨{
      hom := f.hom
      isLocal := f.isLocal
      residue_comm := fun a => e.injective (f.residue_comm a) },
    Deformation.CompleteLocalAlgCat.Hom.ext rfl⟩

/-- The inverse change of residue field, used only to see that the change
functor is injective on objects. -/
private noncomputable def artinianUnchangeResidueField {Λ k κ : Type u}
    [CommRing Λ] [Field k] [Field κ] [Algebra Λ k] [Algebra Λ κ]
    (e : κ ≃ₐ[Λ] k) (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Deformation.ArtinianLocalAlgCat.{u, u, u} Λ κ :=
  { carrier := A, residueEquiv := A.residueEquiv.trans e.symm }

private theorem artinianUnchangeResidueField_change {Λ k κ : Type u} [CommRing Λ]
    [Field k] [Field κ] [Algebra Λ k] [Algebra Λ κ] (e : κ ≃ₐ[Λ] k)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ κ) :
    artinianUnchangeResidueField e
        ((artinianChangeResidueField e).obj A) = A := by
  have h : ((A.residueEquiv.trans e).trans e.symm) = A.residueEquiv := by
    ext x
    exact e.symm_apply_apply _
  exact congrArg (fun E =>
    ({ carrier := A, residueEquiv := E } :
      Deformation.ArtinianLocalAlgCat.{u, u, u} Λ κ)) h

private theorem artinianChangeResidueField_injective {Λ k κ : Type u} [CommRing Λ]
    [Field k] [Field κ] [Algebra Λ k] [Algebra Λ κ] (e : κ ≃ₐ[Λ] k) :
    Function.Injective (artinianChangeResidueField e).obj := fun A B hAB =>
  (artinianUnchangeResidueField_change e A).symm.trans
    ((congrArg (artinianUnchangeResidueField e) hAB).trans
      (artinianUnchangeResidueField_change e B))

/-- A commuting square whose base functor is injective on objects and faithful
reflects `Functor.IsHomLift`. -/
private theorem isHomLift_of_map_of_commSq {C : Type*} {D : Type*} {X : Type*}
    {Y : Type*} [Category* C] [Category* D] [Category* X] [Category* Y]
    (p : X ⥤ C) (q : Y ⥤ D) (F : X ⥤ Y) (G : C ⥤ D)
    (h : F ⋙ q = p ⋙ G) [G.Faithful] (hinj : Function.Injective G.obj)
    {A B : C} {a b : X} (f : A ⟶ B) (r : a ⟶ b)
    (hr : q.IsHomLift (G.map f) (F.map r)) : p.IsHomLift f r := by
  have := hr
  have hqa : q.obj (F.obj a) = G.obj (p.obj a) := Functor.congr_obj h a
  have hqb : q.obj (F.obj b) = G.obj (p.obj b) := Functor.congr_obj h b
  have hd : q.obj (F.obj a) = G.obj A := IsHomLift.domain_eq q (G.map f) (F.map r)
  have hc : q.obj (F.obj b) = G.obj B := IsHomLift.codomain_eq q (G.map f) (F.map r)
  have ha : p.obj a = A := hinj (hqa.symm.trans hd)
  have hb : p.obj b = B := hinj (hqb.symm.trans hc)
  have hnat : q.map (F.map r) =
      eqToHom hqa ≫ G.map (p.map r) ≫ eqToHom hqb.symm := Functor.congr_hom h r
  have hfac := IsHomLift.fac q (G.map f) (F.map r)
  refine IsHomLift.of_fac p f r ha hb (G.map_injective ?_)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hfac, hnat]
  simp

/-- An identity flanked by inverse coherence isomorphisms. -/
private theorem eqToHom_id_eqToHom {C : Type*} [Category* C] {Y Z : C}
    (h : Y = Z) (h' : Z = Y) : eqToHom h ≫ 𝟙 Z ≫ eqToHom h' = 𝟙 Y := by
  cases h
  simp

/-- Read a conjugated identity of morphisms as an identity. -/
private theorem eq_of_eqToHom_conj {C : Type*} [Category* C] {W X Y Z : C}
    (hXW : X = W) (hYZ : Y = Z) {u : W ⟶ Y} {v : X ⟶ Z}
    (h : eqToHom hXW ≫ u ≫ eqToHom hYZ = v) :
    u = eqToHom hXW.symm ≫ v ≫ eqToHom hYZ.symm := by
  cases hXW
  cases hYZ
  simpa using h

/-- A morphism conjugated by two chains of coherence isomorphisms. -/
private theorem eqToHom_conj_collapse {C : Type*} [Category* C]
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C} (h₁ : A₁ = A₂) (h₂ : A₂ = A₃) (h₃ : A₃ = A₄)
    (h₄ : B₁ = B₂) (h₅ : B₂ = B₃) (h₆ : B₃ = B₄) (u : A₄ ⟶ B₁)
    (p : A₁ = A₄) (p' : B₁ = B₄) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ (eqToHom h₃ ≫ u ≫ eqToHom h₄) ≫ eqToHom h₅) ≫
        eqToHom h₆ =
      eqToHom p ≫ u ≫ eqToHom p' := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  cases h₅
  cases h₆
  simp

/-- `Functor.IsHomLift` only depends on the two morphisms. -/
private theorem isHomLift_congr {C : Type*} {X : Type*} [Category* C] [Category* X]
    (p : X ⥤ C) {A B : C} {a b : X} {f f' : A ⟶ B} {r r' : a ⟶ b} (hf : f = f')
    (hr : r = r') (h : p.IsHomLift f r) : p.IsHomLift f' r' := by
  cases hf
  cases hr
  exact h

private theorem artinianChangeResidueField_adicTruncation_obj {Λ k k' : Type u}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k')
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (n : ℕ) :
    (artinianChangeResidueField e).obj (Deformation.AdicTruncation.obj R n) =
      Deformation.AdicTruncation.obj ((completeChangeResidueField e).obj R) n := rfl

private theorem artinianChangeResidueField_transitionNat {Λ k k' : Type u} [CommRing Λ] [Field k]
    [Field k'] [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (n : ℕ) :
    (artinianChangeResidueField e).map
        ((Deformation.AdicTruncation.transitionNat n).app R) =
      (Deformation.AdicTruncation.transitionNat n).app
        ((completeChangeResidueField e).obj R) := rfl

private theorem artinianChangeResidueField_surjective {Λ k k' : Type u} [CommRing Λ] [Field k]
    [Field k'] [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ A')
    (hf : Function.Surjective f.hom) :
    Function.Surjective ((artinianChangeResidueField e).map f).hom := hf

theorem heq_comp_of_heq {C : Type*} [Category* C] {a b b' c : C}
    (h : b = b') {f : a ⟶ b} {g : a ⟶ b'} (hfg : HEq f g) (uu : c ⟶ a) :
    HEq (uu ≫ f) (uu ≫ g) := by
  cases h
  cases eq_of_heq hfg
  exact HEq.rfl

private theorem heq_map_of_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hA
  cases hB
  cases eq_of_heq h
  exact HEq.rfl

section ObjectExt
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
  {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

private theorem deformationMorphism_heq
    {a b a' b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a = a') (hb : b = b')
    (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b)
    (g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a' b')
    (hr : HEq f.ringHom g.ringHom) (har : HEq f.arrow g.arrow) : HEq f g := by
  cases ha
  cases hb
  exact heq_of_eq (DeformationMorphism.ext_of_components iΛ q x₀ hx₀
    (eq_of_heq hr) (eq_of_heq har))

private theorem predeformation_ringHom_heq
    (D : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {a b : D.carrier} (f : a ⟶ b)
      {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (g : A ⟶ A'),
      D.projection.IsHomLift g f →
      (D.objects a).algebra = A → (D.objects b).algebra = A' →
      HEq (D.morphisms a b f).ringHom g := by
  let := D.category
  intro a b f A A' g hf hA hA'
  cases hA
  cases hA'
  have := hf
  exact heq_of_eq ((IsHomLift.fac D.projection g f).trans
    (D.morphism_projection f)).symm

private theorem predeformation_algebra_eq_adicTruncation
    (D : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    (ζ : letI := D.category; Deformation.FormalObject D.projection) (n : ℕ) :
    letI := D.category
    (D.objects (ζ.level n)).algebra = Deformation.AdicTruncation.obj ζ.base n :=
  (D.object_projection _).symm.trans (ζ.level_eq n)

private theorem predeformation_transition_ringHom_heq
    (D : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    (ζ : letI := D.category; Deformation.FormalObject D.projection) (n : ℕ) :
    letI := D.category
    HEq (D.morphisms (ζ.level (n + 1)) (ζ.level n) (ζ.transition n)).ringHom
      ((Deformation.AdicTruncation.transitionNat n).app ζ.base) :=
  predeformation_ringHom_heq D (ζ.transition n) _ (ζ.transition_lift n)
    (predeformation_algebra_eq_adicTruncation D ζ (n + 1))
    (predeformation_algebra_eq_adicTruncation D ζ n)

private theorem predeformation_heq_of_morphisms_heq
    (D : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {a b a' b' : D.carrier} (_ha : a = a') (_hb : b = b')
      (f : a ⟶ b) (g : a' ⟶ b'),
      HEq (D.morphisms a b f) (D.morphisms a' b' g) → HEq f g := by
  let := D.category
  intro a b a' b' ha hb f g h
  cases ha
  cases hb
  exact heq_of_eq ((D.morphisms a b).injective (eq_of_heq h))

end ObjectExt
end ChangeOfResidueField

/-- A morphism conjugated by coherence isomorphisms is heterogeneously equal to it. -/
private theorem heq_eqToHom_comp_eqToHom {C : Type*} [Category C] {a b c d : C}
    (h₁ : a = c) (h₂ : d = b) (f : c ⟶ d) :
    HEq (eqToHom h₁ ≫ f ≫ eqToHom h₂) f := by
  cases h₁
  cases h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact HEq.rfl

section Transport

variable {Λ k κ : Type u} [CommRing Λ] [Field k] [Field κ] [Algebra Λ k]
  [Algebra Λ κ] (e : κ ≃ₐ[Λ] k)
variable {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S) (x₀ x₁ : X)
variable (hx₀ : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx₁ : q.obj x₁ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ))
  (ρ : x₀ ⟶ x₁)
  (hρ : eqToHom (congrArg Over.left hx₀).symm ≫ (q.map ρ).left ≫
    eqToHom (congrArg Over.left hx₁) =
      Spec.map (CommRingCat.ofHom (e.toRingHom : κ →+* k)))

include hρ in
/-- Transport a deformation object at `x₁` over `κ` to one at `x₀` over `k`. -/
noncomputable def changeDeformationObject
    (a : Deformation.Artin.DeformationObject iΛ q x₁ hx₁) :
    Deformation.Artin.DeformationObject iΛ q x₀ hx₀ where
  algebra := (artinianChangeResidueField e).obj a.algebra
  point := a.point
  arrow := ρ ≫ a.arrow
  base := a.base
  arrow_base := by
    rw [artinianChangeResidueField_residueMap e a.algebra, CommRingCat.ofHom_comp,
      Spec.map_comp, ← hρ, ← a.arrow_base]
    simp only [Functor.map_comp, Over.comp_left, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

include hρ in
private theorem changeDeformationObject_algebra
    (a : Deformation.Artin.DeformationObject iΛ q x₁ hx₁) :
    (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ a).algebra =
      (artinianChangeResidueField e).obj a.algebra := rfl

include hρ in
private theorem changeDeformationObject_point
    (a : Deformation.Artin.DeformationObject iΛ q x₁ hx₁) :
    (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ a).point = a.point := rfl

include hρ in
private theorem changeDeformationObject_arrow
    (a : Deformation.Artin.DeformationObject iΛ q x₁ hx₁) :
    (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ a).arrow = ρ ≫ a.arrow := rfl

include hρ in
/-- Transport a deformation morphism along the same change. -/
noncomputable def changeDeformationMorphism
    {a b : Deformation.Artin.DeformationObject iΛ q x₁ hx₁}
    (f : Deformation.Artin.DeformationMorphism iΛ q x₁ hx₁ a b) :
    Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀
      (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ a)
      (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ b) where
  ringHom := (artinianChangeResidueField e).map f.ringHom
  arrow := f.arrow
  triangle := by
    change (ρ ≫ b.arrow) ≫ f.arrow = ρ ≫ a.arrow
    rw [Category.assoc, f.triangle]
  arrow_base := f.arrow_base


include hρ in
private theorem changeDeformationMorphism_ringHom
    {a b : Deformation.Artin.DeformationObject iΛ q x₁ hx₁}
    (f : Deformation.Artin.DeformationMorphism iΛ q x₁ hx₁ a b) :
    (changeDeformationMorphism e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ f).ringHom =
      (artinianChangeResidueField e).map f.ringHom := rfl

include hρ in
private theorem changeDeformationMorphism_arrow
    {a b : Deformation.Artin.DeformationObject iΛ q x₁ hx₁}
    (f : Deformation.Artin.DeformationMorphism iΛ q x₁ hx₁ a b) :
    (changeDeformationMorphism e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ f).arrow = f.arrow := rfl

variable (DΛ : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
  (Dκ : Deformation.Artin.PredeformationConstruction iΛ q x₁ hx₁)

include hρ in
/-- The functor between predeformation categories induced by `ρ` and the
change of residue field. -/
noncomputable def changePredeformation :
    letI := Dκ.category
    letI := DΛ.category
    Dκ.carrier ⥤ DΛ.carrier := by
  letI := Dκ.category
  letI := DΛ.category
  let obj (a : Dκ.carrier) := DΛ.objects.symm
    (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects a))
  let map {a b : Dκ.carrier} (f : a ⟶ b) : obj a ⟶ obj b :=
    (DΛ.morphisms _ _).symm
      (transportDeformationMorphism
        (DΛ.objects.apply_symm_apply _) (DΛ.objects.apply_symm_apply _)
        (changeDeformationMorphism e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.morphisms a b f)))
  exact {
    obj := obj
    map := map
    map_id := by
      intro a
      apply (DΛ.morphisms _ _).injective
      apply DeformationMorphism.ext_of_components
      · simp only [map, Equiv.apply_symm_apply,
          transportDeformationMorphism_ringHom, changeDeformationMorphism,
          predeformation_ringHom_id]
        exact eqToHom_id_eqToHom _ _
      · simp only [map, Equiv.apply_symm_apply,
          transportDeformationMorphism_arrow, changeDeformationMorphism,
          Dκ.reversed_identity, DΛ.reversed_identity]
        exact eqToHom_id_eqToHom _ _
    map_comp := by
      intro a b c f g
      apply (DΛ.morphisms _ _).injective
      apply DeformationMorphism.ext_of_components
      · simp only [map, Equiv.apply_symm_apply, transportDeformationMorphism_ringHom,
          changeDeformationMorphism, predeformation_ringHom_comp, Functor.map_comp]
        exact eqToHom_middle_cancel _ _ _ _ _ _
      · simp only [map, Equiv.apply_symm_apply, transportDeformationMorphism_arrow,
          changeDeformationMorphism, Dκ.reversed_composition,
          DΛ.reversed_composition]
        exact eqToHom_middle_cancel _ _ _ _ _ _ }


include hρ in
theorem changePredeformation_objects (a : letI := Dκ.category; Dκ.carrier) :
    letI := Dκ.category
    letI := DΛ.category
    DΛ.objects ((changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).obj a) =
      changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects a) :=
  DΛ.objects.apply_symm_apply _

include hρ in
private theorem changePredeformation_morphisms
    {a b : letI := Dκ.category; Dκ.carrier} (f : letI := Dκ.category; a ⟶ b) :
    letI := Dκ.category
    letI := DΛ.category
    DΛ.morphisms _ _ ((changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map f) =
      transportDeformationMorphism
        (DΛ.objects.apply_symm_apply _) (DΛ.objects.apply_symm_apply _)
        (changeDeformationMorphism e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.morphisms a b f)) :=
  (DΛ.morphisms _ _).apply_symm_apply _

include hρ in
/-- The transport functor lies over the change-of-residue-field functor. -/
theorem changePredeformation_comp_projection :
    letI := Dκ.category
    letI := DΛ.category
    changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ⋙ DΛ.projection =
      Dκ.projection ⋙ artinianChangeResidueField e := by
  let := Dκ.category
  let := DΛ.category
  refine CategoryTheory.Functor.ext (fun a => ?_) ?_
  · rw [Functor.comp_obj, DΛ.object_projection,
      changePredeformation_objects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ a,
      changeDeformationObject_algebra]
    exact congrArg (artinianChangeResidueField e).obj (Dκ.object_projection a).symm
  · intro a b f
    have h := DΛ.morphism_projection
      ((changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map f)
    rw [changePredeformation_morphisms e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ f,
      transportDeformationMorphism_ringHom, changeDeformationMorphism_ringHom] at h
    conv_rhs at h => rw [← Dκ.morphism_projection f]
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map] at h
    have h' := eq_of_eqToHom_conj _ _ h
    rw [Functor.comp_map, Functor.comp_map, h']
    exact eqToHom_conj_collapse _ _ _ _ _ _ _ _ _

include hρ in
private theorem changePredeformation_faithful :
    letI := Dκ.category
    letI := DΛ.category
    (changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).Faithful := by
  let := Dκ.category
  let := DΛ.category
  refine ⟨fun {a b} f g h => ?_⟩
  apply (Dκ.morphisms a b).injective
  have hh := congrArg (DΛ.morphisms _ _) h
  rw [changePredeformation_morphisms e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ f,
    changePredeformation_morphisms e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ g] at hh
  have hm := transportDeformationMorphism_injective
    (DΛ.objects.apply_symm_apply _) (DΛ.objects.apply_symm_apply _) hh
  apply DeformationMorphism.ext_of_components iΛ q x₁ hx₁
  · exact (artinianChangeResidueField_faithful e).map_injective
      (congrArg (fun m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀
        (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects a))
        (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects b)) =>
        m.ringHom) hm)
  · exact congrArg (fun m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀
      (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects a))
      (changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects b)) =>
      m.arrow) hm

include hρ in
/-- With `ρ` an epimorphism the transport functor is full. -/
private theorem changePredeformation_full [Epi ρ] :
    letI := Dκ.category
    letI := DΛ.category
    (changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).Full := by
  let := Dκ.category
  let := DΛ.category
  have := artinianChangeResidueField_full e
  refine ⟨fun {a b} g => ?_⟩
  let G' := transportDeformationMorphism
    (changePredeformation_objects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ a).symm
    (changePredeformation_objects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ b).symm
    (DΛ.morphisms _ _ g)
  have hr : ((artinianChangeResidueField e).preimage G'.ringHom).hom.toRingHom =
      G'.ringHom.hom.toRingHom :=
    congrArg (fun m : (artinianChangeResidueField e).obj (Dκ.objects a).algebra ⟶
        (artinianChangeResidueField e).obj (Dκ.objects b).algebra =>
      m.hom.toRingHom)
      (Functor.map_preimage (artinianChangeResidueField e) G'.ringHom)
  let H : Deformation.Artin.DeformationMorphism iΛ q x₁ hx₁ (Dκ.objects a) (Dκ.objects b) :=
    { ringHom := (artinianChangeResidueField e).preimage G'.ringHom
      arrow := G'.arrow
      triangle := by
        have ht : ρ ≫ (Dκ.objects b).arrow ≫ G'.arrow =
            ρ ≫ (Dκ.objects a).arrow :=
          (Category.assoc _ _ _).symm.trans G'.triangle
        exact (cancel_epi ρ).mp ht
      arrow_base := by
        rw [hr]
        exact G'.arrow_base }
  refine ⟨(Dκ.morphisms a b).symm H, ?_⟩
  apply (DΛ.morphisms _ _).injective
  rw [changePredeformation_morphisms e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ]
  have hHG : changeDeformationMorphism e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ
      (Dκ.morphisms a b ((Dκ.morphisms a b).symm H)) = G' := by
    rw [Equiv.apply_symm_apply]
    apply DeformationMorphism.ext_of_components iΛ q x₀ hx₀
    · rw [changeDeformationMorphism_ringHom]
      exact Functor.map_preimage _ _
    · rfl
  rw [hHG]
  exact transportDeformationMorphism_symm _ _ _

section FormalObjects

include hρ in
/-- Transport of a formal object along the change of predeformation category. -/
noncomputable def changeFormalObject
    (ξ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) :
    letI := DΛ.category
    Deformation.FormalObject DΛ.projection :=
  letI := Dκ.category
  letI := DΛ.category
  let Ψ := changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  let hsq := changePredeformation_comp_projection e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  { base := (completeChangeResidueField e).obj ξ.base
    level := fun n => Ψ.obj (ξ.level n)
    level_eq := fun n =>
      (Functor.congr_obj hsq (ξ.level n)).trans
        (congrArg (artinianChangeResidueField e).obj (ξ.level_eq n))
    transition := fun n => Ψ.map (ξ.transition n)
    transition_lift := fun n =>
      isHomLift_map_of_commSq Dκ.projection DΛ.projection Ψ
        (artinianChangeResidueField e) hsq
        ((Deformation.AdicTruncation.transitionNat n).app ξ.base) (ξ.transition n)
        (ξ.transition_lift n) }

include hρ in
private theorem changeFormalObject_base
    (ξ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) :
    letI := Dκ.category
    letI := DΛ.category
    (changeFormalObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ξ).base =
      (completeChangeResidueField e).obj ξ.base := rfl

include hρ in
private theorem changeFormalObject_level
    (ξ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) (n : ℕ) :
    letI := Dκ.category
    letI := DΛ.category
    (changeFormalObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ξ).level n =
      (changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).obj (ξ.level n) := rfl

include hρ in
private theorem changeFormalObject_transition
    (ξ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) (n : ℕ) :
    letI := Dκ.category
    letI := DΛ.category
    (changeFormalObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ξ).transition n =
      (changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map
        (ξ.transition n) := rfl

include hρ in
/-- The functor on formal objects induced by the change of residue field. -/
noncomputable def changeFormalObjects :
    letI := Dκ.category
    letI := DΛ.category
    Deformation.FormalObject Dκ.projection ⥤ Deformation.FormalObject DΛ.projection :=
  letI := Dκ.category
  letI := DΛ.category
  let Ψ := changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  let hsq := changePredeformation_comp_projection e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  { obj := changeFormalObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
    map := fun {ξ η} f =>
      { base := (completeChangeResidueField e).map f.base
        app := fun n => Ψ.map (f.app n)
        app_lift := fun n =>
          isHomLift_map_of_commSq Dκ.projection DΛ.projection Ψ
            (artinianChangeResidueField e) hsq
            ((Deformation.AdicTruncation.functor n).map f.base) (f.app n)
            (f.app_lift n)
        naturality := fun n =>
          (Ψ.map_comp (ξ.transition n) (f.app n)).symm.trans
            ((congrArg Ψ.map (f.naturality n)).trans
              (Ψ.map_comp (f.app (n + 1)) (η.transition n))) }
    map_id := fun ξ => by
      refine Deformation.FormalObject.Hom.ext ?_ (fun n => ?_)
      · exact (completeChangeResidueField e).map_id ξ.base
      · exact Ψ.map_id (ξ.level n)
    map_comp := fun f g => by
      refine Deformation.FormalObject.Hom.ext ?_ (fun n => ?_)
      · exact (completeChangeResidueField e).map_comp f.base g.base
      · exact Ψ.map_comp (f.app n) (g.app n) }

include hρ in
/-- The change-of-residue-field functor on formal objects acts on complete local bases by
the change-of-residue-field functor on those bases. -/
theorem changeFormalObjects_obj_base
    (ξ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) :
    letI := Dκ.category
    letI := DΛ.category
    ((changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).obj ξ).base =
      (completeChangeResidueField e).obj ξ.base := rfl

include hρ in
private theorem changeFormalObjects_faithful :
    letI := Dκ.category
    letI := DΛ.category
    (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).Faithful := by
  let := Dκ.category
  let := DΛ.category
  have := changePredeformation_faithful e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  have := completeChangeResidueField_faithful e
  refine ⟨fun {ξ η} f g h => ?_⟩
  refine Deformation.FormalObject.Hom.ext ?_ (fun n => ?_)
  · exact (completeChangeResidueField e).map_injective
      (congrArg (fun m : (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ
        Dκ).obj ξ ⟶ _ => m.base) h)
  · exact (changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map_injective
      (congrArg (fun m : (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ
        Dκ).obj ξ ⟶ _ => m.app n) h)

include hρ in
private theorem changeFormalObjects_full [Epi ρ] :
    letI := Dκ.category
    letI := DΛ.category
    (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).Full := by
  let := Dκ.category
  let := DΛ.category
  have hΨfull := changePredeformation_full e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  have hΨfaithful := changePredeformation_faithful e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  have := completeChangeResidueField_full e
  have := artinianChangeResidueField_faithful e
  have hsq := changePredeformation_comp_projection e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  refine ⟨fun {ξ η} h => ?_⟩
  let Ψ := changePredeformation e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  let b₀ := (completeChangeResidueField e).preimage h.base
  have hb₀ : (completeChangeResidueField e).map b₀ = h.base :=
    Functor.map_preimage _ _
  have ha (n : ℕ) : Ψ.map (Ψ.preimage (h.app n)) = h.app n :=
    Functor.map_preimage _ _
  refine ⟨{ base := b₀
            app := fun n => Ψ.preimage (h.app n)
            app_lift := fun n => ?_
            naturality := fun n => ?_ }, ?_⟩
  · refine isHomLift_of_map_of_commSq Dκ.projection DΛ.projection Ψ
      (artinianChangeResidueField e) hsq
      (artinianChangeResidueField_injective e) _ _ ?_
    exact isHomLift_congr DΛ.projection
      (congrArg (Deformation.AdicTruncation.functor n).map hb₀).symm (ha n).symm
      (h.app_lift n)
  · apply Ψ.map_injective
    rw [Ψ.map_comp, Ψ.map_comp, ha n, ha (n + 1)]
    exact h.naturality n
  · refine Deformation.FormalObject.Hom.ext hb₀ (fun n => ha n)

include hρ in
private theorem changeFormalObjects_obj_eq :
    letI := Dκ.category
    letI := DΛ.category
    ∀ (ζ : Deformation.FormalObject Dκ.projection)
      (η : Deformation.FormalObject DΛ.projection),
      (completeChangeResidueField e).obj ζ.base = η.base →
      (∀ n, (Dκ.objects (ζ.level n)).point = (DΛ.objects (η.level n)).point) →
      (∀ n, HEq (ρ ≫ (Dκ.objects (ζ.level n)).arrow)
        (DΛ.objects (η.level n)).arrow) →
      (∀ n, HEq (Dκ.morphisms (ζ.level (n + 1)) (ζ.level n) (ζ.transition n)).arrow
        (DΛ.morphisms (η.level (n + 1)) (η.level n) (η.transition n)).arrow) →
      (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).obj ζ = η := by
  let := Dκ.category
  let := DΛ.category
  intro ζ η hbase hpoint harrow htrans
  have hAC := predeformation_algebra_eq_adicTruncation Dκ ζ
  have hAD := predeformation_algebra_eq_adicTruncation DΛ η
  have halg : ∀ n, (artinianChangeResidueField e).obj
      (Dκ.objects (ζ.level n)).algebra = (DΛ.objects (η.level n)).algebra := by
    intro n
    rw [hAC n, hAD n, ← hbase]
    exact artinianChangeResidueField_adicTruncation_obj e ζ.base n
  have hobj : ∀ n, changeDeformationObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ
      (Dκ.objects (ζ.level n)) = DΛ.objects (η.level n) := fun n =>
    deformationObject_ext (halg n) (hpoint n) (harrow n)
  have hlevel : ∀ n,
      ((changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).obj ζ).level n =
        η.level n := fun n =>
    DΛ.objects.injective
      ((changePredeformation_objects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
        (ζ.level n)).trans (hobj n))
  have hring : ∀ n, HEq ((artinianChangeResidueField e).map
      (Dκ.morphisms (ζ.level (n + 1)) (ζ.level n) (ζ.transition n)).ringHom)
      (DΛ.morphisms (η.level (n + 1)) (η.level n) (η.transition n)).ringHom := by
    intro n
    refine HEq.trans (HEq.trans (heq_map_of_heq
      (artinianChangeResidueField e) (hAC (n + 1)) (hAC n)
      (predeformation_transition_ringHom_heq Dκ ζ n)) ?_)
      (predeformation_transition_ringHom_heq DΛ η n).symm
    refine HEq.trans (heq_of_eq (artinianChangeResidueField_transitionNat e ζ.base n)) ?_
    exact congr_arg_heq
      (fun R => (Deformation.AdicTruncation.transitionNat n).app R) hbase
  refine Deformation.FormalObject.ext hbase hlevel
    (fun n => (CategoryTheory.conj_eqToHom_iff_heq _ _ (hlevel (n + 1)) (hlevel n)).2 ?_)
  refine predeformation_heq_of_morphisms_heq DΛ (hlevel (n + 1)) (hlevel n) _ _ ?_
  refine HEq.trans (heq_of_eq (changePredeformation_morphisms
    e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ (ζ.transition n))) ?_
  refine HEq.trans (transportDeformationMorphism_heq _ _ _) ?_
  exact deformationMorphism_heq (hobj (n + 1)) (hobj n) _ _ (hring n) (htrans n)

include hρ in
private theorem changeFormalObjects_comp_projection :
    letI := Dκ.category
    letI := DΛ.category
    changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ⋙
        Deformation.FormalObject.projection =
      Deformation.FormalObject.projection ⋙ completeChangeResidueField e := rfl

include hρ in
theorem isVersal_of_changeFormalObjects [Epi ρ] :
    letI := Dκ.category
    letI := DΛ.category
    ∀ (hκ : Deformation.IsCofiberedInGroupoids Dκ.projection)
      (hΛ : Deformation.IsCofiberedInGroupoids DΛ.projection)
      (ζ : Deformation.FormalObject Dκ.projection)
      (η : Deformation.FormalObject DΛ.projection),
      (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).obj ζ = η →
      Deformation.IsVersal hΛ η → Deformation.IsVersal hκ ζ := by
  let := Dκ.category
  let := DΛ.category
  intro hκ hΛ ζ η hζη hversal
  have hfull := changeFormalObjects_full e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  have hfaithful := changeFormalObjects_faithful e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  have hsq := changeFormalObjects_comp_projection e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
  rw [Deformation.isVersal_iff_lifts_artinian] at hversal
  rw [Deformation.isVersal_iff_lifts_artinian]
  intro A A' f hsurj y x g hg a
  obtain ⟨b, hb⟩ := hversal ((artinianChangeResidueField e).map f)
    (artinianChangeResidueField_surjective e f hsurj)
    ((changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map g)
    (isHomLift_map_of_commSq Deformation.FormalObject.projection
      Deformation.FormalObject.projection
      (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ)
      (completeChangeResidueField e) hsq
      (Deformation.artinianToComplete.map f) g hg)
    (eqToHom hζη.symm ≫
      (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map a)
  refine ⟨(changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).preimage
    (eqToHom hζη ≫ b), ?_⟩
  apply (changeFormalObjects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ).map_injective
  rw [Functor.map_comp, Functor.map_preimage, Category.assoc, hb,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

include hρ in
/-- The transported formal object has the same points as the original. -/
theorem changeFormalObject_objects_point
    (ζ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) (n : ℕ) :
    letI := Dκ.category
    letI := DΛ.category
    (DΛ.objects
        ((changeFormalObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ζ).level n)).point =
      (Dκ.objects (ζ.level n)).point := by
  let := Dκ.category
  let := DΛ.category
  rw [changeFormalObject_level e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ζ n,
    changePredeformation_objects e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ (ζ.level n),
    changeDeformationObject_point e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ (Dκ.objects (ζ.level n))]

include hρ in
/-- The transported formal object has the same transition arrows as the original. -/
theorem changeFormalObject_morphisms_arrow
    (ζ : letI := Dκ.category; Deformation.FormalObject Dκ.projection) (n : ℕ) :
    letI := Dκ.category
    letI := DΛ.category
    HEq (DΛ.morphisms _ _
        ((changeFormalObject e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ ζ).transition n)).arrow
      (Dκ.morphisms (ζ.level (n + 1)) (ζ.level n) (ζ.transition n)).arrow := by
  let := Dκ.category
  let := DΛ.category
  refine HEq.trans (heq_of_eq (congrArg
    (fun m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ _ _ => m.arrow)
    (changePredeformation_morphisms e iΛ q x₀ x₁ hx₀ hx₁ ρ hρ DΛ Dκ
      (ζ.transition n)))) ?_
  rw [transportDeformationMorphism_arrow, changeDeformationMorphism_arrow]
  exact heq_eqToHom_comp_eqToHom _ _ _

end FormalObjects

end Transport

end ResidueFieldTransport

end Deformation.Artin

end
