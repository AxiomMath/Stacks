module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.Deformation.Artin.Versality.Openness
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# Smoothness on predeformation categories from formal smoothness on objects

A 1-morphism `p : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of a
scheme `S` which is formally smooth on objects induces, at every finite type field-valued
point of `𝒳`, a smooth functor of predeformation categories.

Smoothness is tested on small extensions in `𝒞_Λ`. A small extension is a surjection with
square-zero kernel, so the morphism of affine schemes it induces is a first-order thickening,
and formal smoothness on objects applies to it directly: it extends the given deformation
upstairs along the thickening and produces the comparison isomorphism with the deformation
downstairs.

## Main results

* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects` —
  **Stacks 07WK**, case (1): formal smoothness on objects.
* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelyFormallySmooth` —
  **Stacks 07WK**, case (2): representability by algebraic spaces together with formal
  smoothness.
* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth` —
  **Stacks 07WK**, case (3): representability by algebraic spaces together with smoothness.

## Implementation notes

Case (3) carries the implication of Stacks 04AM from smoothness to formal smoothness, for a
morphism representable by algebraic spaces, as a hypothesis: the library proves the converse
implication and proves this one only for a morphism representable by schemes, and the torsor
argument that closes the general case needs the sheaf of relative differentials of a morphism
of algebraic spaces and the vanishing of Stacks 03DW in positive degrees, neither of which is
available.

The two objects of the site entering the lifting problem are the images under `𝒴.val.p` of the
two deformations downstairs; they are spectra of Artinian local algebras, hence affine, and the
morphism between them is the spectrum of the arrow of `𝒞_Λ` underlying the given morphism of
deformations. The object produced upstairs is turned into a deformation by
`Deformation.Artin.DeformationObject.extend`, which appends an arrow over the spectrum of a map
of Artinian local algebras to an existing deformation.

## References

* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Thickenings

namespace Deformation.Artin

/- The constructions below reason about morphisms of the fibre categories of the structure
functors `𝒳.val.p`, whose spellings are built from definitions that the `implicit`
transparency level does not unfold. Naming the unfolding chain here is what lets the ordinary
tactics act on those goals; this is the same list as in
`StacksFrontier/AlgebraicGeometry/Stacks/Criteria/FormallySmoothOnObjects.lean`. -/
attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

/-! ### Isomorphisms and small extensions in `𝒞_Λ` -/

section Algebra

universe u

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An isomorphism of Artinian local `Λ`-algebras is bijective on elements. -/
private lemma bijective_hom_of_iso {A C : ArtinianLocalAlgCat.{u, u, u} Λ k} (e : A ≅ C) :
    Function.Bijective e.hom.hom := by
  have hleft : e.inv.hom.comp e.hom.hom = AlgHom.id _ _ := by
    have h := congrArg ArtinianLocalAlgCat.Hom.hom (Iso.hom_inv_id e)
    simpa only [ArtinianLocalAlgCat.comp_hom, ArtinianLocalAlgCat.id_hom] using h
  have hright : e.hom.hom.comp e.inv.hom = AlgHom.id _ _ := by
    have h := congrArg ArtinianLocalAlgCat.Hom.hom (Iso.inv_hom_id e)
    simpa only [ArtinianLocalAlgCat.comp_hom, ArtinianLocalAlgCat.id_hom] using h
  refine ⟨fun a b hab => ?_, fun c => ⟨e.inv.hom c, ?_⟩⟩
  · calc
      a = e.inv.hom (e.hom.hom a) := by
        simpa using (congrArg (fun F => F a) hleft).symm
      _ = e.inv.hom (e.hom.hom b) := congrArg e.inv.hom hab
      _ = b := by simpa using congrArg (fun F => F b) hleft
  · simpa using congrArg (fun F => F c) hright

/-- A morphism of `𝒞_Λ` which is a small extension up to isomorphisms at both ends is a
surjection with square-zero kernel. -/
private lemma surjective_and_ker_sq_of_eq_iso_comp
    {A₁ A₂ A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} {f : A₁ ⟶ A₂}
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom))
    (e₁ : A ≅ A₁) (e₂ : A₂ ≅ A') {r : A ⟶ A'} (hr : r = e₁.hom ≫ f ≫ e₂.hom) :
    Function.Surjective r.hom ∧ RingHom.ker r.hom.toRingHom ^ 2 = ⊥ := by
  have hsurjf : Function.Surjective f.hom := by
    simpa using hf.isSquareZeroSurjection.2.2.1
  have hkerf : RingHom.ker f.hom.toRingHom ^ 2 = ⊥ := by
    simpa using hf.isSquareZeroSurjection.2.2.2
  have hval (a : A) : r.hom a = e₂.hom.hom (f.hom (e₁.hom.hom a)) := by
    rw [hr]
    simp [ArtinianLocalAlgCat.comp_hom]
  refine ⟨fun c => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := (bijective_hom_of_iso e₂).2 c
    obtain ⟨a₁, ha₁⟩ := hsurjf b
    obtain ⟨a, ha⟩ := (bijective_hom_of_iso e₁).2 a₁
    exact ⟨a, by rw [hval, ha, ha₁, hb]⟩
  · have hker : RingHom.ker r.hom.toRingHom =
        (RingHom.ker f.hom.toRingHom).comap e₁.hom.hom.toRingHom := by
      ext a
      simp only [RingHom.mem_ker, Ideal.mem_comap]
      change r.hom a = 0 ↔ f.hom (e₁.hom.hom a) = 0
      rw [hval]
      refine ⟨fun ha => (bijective_hom_of_iso e₂).1 (by simpa using ha), fun ha => ?_⟩
      rw [ha, map_zero]
    rw [hker]
    refine le_antisymm ?_ bot_le
    have hle := Ideal.le_comap_pow (K := RingHom.ker f.hom.toRingHom)
      (f := e₁.hom.hom.toRingHom) 2
    have hcomap : Ideal.comap e₁.hom.hom.toRingHom (⊥ : Ideal A₁) = ⊥ :=
      Ideal.comap_bot_of_injective _ (by simpa using (bijective_hom_of_iso e₁).1)
    rw [hkerf, hcomap] at hle
    exact hle

end Algebra

/-! ### Transport along equalities -/

section Transport

universe u v w

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A first-order thickening remains one after transporting its source and target along
equalities of schemes. -/
private lemma isFirstOrderThickening_eqToHom_conj {X X' Y Y' : Scheme.{u}} (hX : X = X')
    (f : X' ⟶ Y) (hY : Y = Y') (hf : IsFirstOrderThickening f) :
    IsFirstOrderThickening (eqToHom hX ≫ f ≫ eqToHom hY) := by
  cases hX
  cases hY
  simpa using hf

/-- The spectrum of the identification of two equal Artinian local algebras is the
identification of their spectra. -/
private lemma specMap_eqToHom_hom {A C : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = C) :
    Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) =
      eqToHom (congrArg (fun T : ArtinianLocalAlgCat.{u, u, u} Λ k =>
        Spec (.of (↑T))) h).symm := by
  cases h
  simp

/-- A morphism conjugated by `eqToHom`s depends only on its endpoints. -/
private lemma eqToHom_conj_collapse {C : Type*} [Category C] {V W X Y Z Z' : C}
    (h₁ : V = W) (h₂ : W = X) (f : X ⟶ Y) (h₃ : Y = Z) (h₄ : Z = Z')
    (h₅ : V = X) (h₆ : Y = Z') :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ f ≫ eqToHom h₃) ≫ eqToHom h₄ =
      eqToHom h₅ ≫ f ≫ eqToHom h₆ := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  simp

/-- A morphism conjugated by `eqToHom`s whose right-hand frame cancels. -/
private lemma eqToHom_conj_collapse_comp {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    (h₁ : O₁ = O₂) (h₂ : O₂ = O₃) (f : O₃ ⟶ O₄) (h₃ : O₄ = O₅) (h₄ : O₅ = O₄)
    (h₅ : O₁ = O₃) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ f ≫ eqToHom h₃) ≫ eqToHom h₄ = eqToHom h₅ ≫ f := by
  cases h₁
  cases h₂
  cases h₃
  simp

/-- An identification of objects of `𝒞_Λ` is the identity up to the identifications of its
endpoints with a common object. -/
private lemma eqToHom_eq_id_conj {C : Type*} [Category C] {X Y Z : C} (h : X = Y)
    (h₁ : X = Z) (h₂ : Y = Z) : eqToHom h = eqToHom h₁ ≫ 𝟙 Z ≫ eqToHom h₂.symm := by
  cases h
  cases h₁
  simp

/-- Equal functors agree on morphisms, up to the identifications of their values on
objects. -/
private lemma functor_map_eq_of_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (h : F = G) {Z W : C} (f : Z ⟶ W) :
    eqToHom (congrArg (fun H : C ⥤ D => H.obj Z) h).symm ≫ F.map f ≫
      eqToHom (congrArg (fun H : C ⥤ D => H.obj W) h) = G.map f := by
  cases h
  simp

variable {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S} {X : Type v} [Category.{w} X]
  {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Transporting a morphism of deformations along an equality of its source composes its
arrow of `𝒞_Λ` with the induced identification. -/
private lemma deformationMorphism_ringHom_cast {a b c : DeformationObject iΛ q x₀ hx₀}
    (h : a = b) (m : DeformationMorphism iΛ q x₀ hx₀ b c) :
    (h.symm ▸ m).ringHom = eqToHom (congrArg DeformationObject.algebra h) ≫ m.ringHom := by
  cases h
  simp

/-- Transporting a morphism of deformations along an equality of its source composes its
reversed arrow with the induced identification. -/
private lemma deformationMorphism_arrow_cast {a b c : DeformationObject iΛ q x₀ hx₀}
    (h : a = b) (m : DeformationMorphism iΛ q x₀ hx₀ b c) :
    (h.symm ▸ m).arrow = m.arrow ≫ eqToHom (congrArg DeformationObject.point h).symm := by
  cases h
  simp

/-- Equal deformations have the same arrow out of the distinguished point. -/
private lemma deformationObject_arrow_comp_eqToHom {a b : DeformationObject iΛ q x₀ hx₀}
    (h : a = b) :
    a.arrow ≫ eqToHom (congrArg DeformationObject.point h) = b.arrow := by
  cases h
  simp

/-- Appending to a deformation an arrow lying over the spectrum of a map of Artinian local
algebras produces a deformation over the source of that map. -/
private def DeformationObject.extend (d : DeformationObject iΛ q x₀ hx₀)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (r : A ⟶ d.algebra) (z : X) (φ : d.point ⟶ z)
    (hbase : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hφ : eqToHom (congrArg Over.left d.base).symm ≫ (q.map φ).left ≫
        eqToHom (congrArg Over.left hbase) =
      Spec.map (CommRingCat.ofHom r.hom.toRingHom)) :
    DeformationObject iΛ q x₀ hx₀ where
  algebra := A
  point := z
  arrow := d.arrow ≫ φ
  base := hbase
  arrow_base := by
    have hres : (residueMap d.algebra).comp r.hom.toRingHom = residueMap A := by
      ext a
      exact r.residue_comm a
    calc
      _ = (eqToHom (congrArg Over.left hx₀).symm ≫ (q.map d.arrow).left ≫
              eqToHom (congrArg Over.left d.base)) ≫
            (eqToHom (congrArg Over.left d.base).symm ≫ (q.map φ).left ≫
              eqToHom (congrArg Over.left hbase)) := by
          simp [Functor.map_comp, Over.comp_left, Category.assoc, eqToHom_refl]
      _ = Spec.map (CommRingCat.ofHom (residueMap d.algebra)) ≫
            Spec.map (CommRingCat.ofHom r.hom.toRingHom) := by
          rw [d.arrow_base, hφ]
      _ = Spec.map (CommRingCat.ofHom ((residueMap d.algebra).comp r.hom.toRingHom)) := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom (residueMap A)) := by rw [hres]

/-- The extended deformation maps to the original one by the appended arrow. -/
private def DeformationObject.extendHom (d : DeformationObject iΛ q x₀ hx₀)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (r : A ⟶ d.algebra) (z : X) (φ : d.point ⟶ z)
    (hbase : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hφ : eqToHom (congrArg Over.left d.base).symm ≫ (q.map φ).left ≫
        eqToHom (congrArg Over.left hbase) =
      Spec.map (CommRingCat.ofHom r.hom.toRingHom)) :
    DeformationMorphism iΛ q x₀ hx₀ (d.extend A r z φ hbase hφ) d where
  ringHom := r
  arrow := φ
  triangle := rfl
  arrow_base := hφ

attribute [local implicit_reducible] DeformationObject.extend DeformationObject.extendHom

end Transport

/-! ### Generalities on presentations of predeformation categories -/

section Construction

universe u v w

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S} {X : Type v} [Category.{w} X]
  {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

attribute [local instance] categoryOfConstruction

/-- The projection of a presentation of the predeformation category on a morphism is the
arrow of `𝒞_Λ` carried by the corresponding morphism of deformations. -/
private lemma projection_map_eq (C : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : C.carrier} (φ : a ⟶ b) :
    C.projection.map φ = eqToHom (C.object_projection a) ≫ (C.morphisms a b φ).ringHom ≫
      eqToHom (C.object_projection b).symm := by
  rw [← C.morphism_projection φ]
  simp [Category.assoc]

/-- The arrow of `𝒞_Λ` carried by a composite is the composite of the two arrows. -/
private lemma morphisms_comp_ringHom (C : PredeformationConstruction iΛ q x₀ hx₀)
    {a b c : C.carrier} (φ : a ⟶ b) (ψ : b ⟶ c) :
    (C.morphisms a c (φ ≫ ψ)).ringHom =
      (C.morphisms a b φ).ringHom ≫ (C.morphisms b c ψ).ringHom := by
  rw [← C.morphism_projection φ, ← C.morphism_projection ψ, ← C.morphism_projection (φ ≫ ψ),
    Functor.map_comp]
  simp [Category.assoc]

/-- A morphism whose arrow of `𝒞_Λ` is a given `f` up to the canonical identifications lies
over `f`. -/
private lemma isHomLift_of_ringHom_eq (C : PredeformationConstruction iΛ q x₀ hx₀)
    {A₁ A₂ : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A₁ ⟶ A₂) {a b : C.carrier} (φ : a ⟶ b)
    (hdom : (C.objects a).algebra = A₁) (hcod : (C.objects b).algebra = A₂)
    (h : (C.morphisms a b φ).ringHom = eqToHom hdom ≫ f ≫ eqToHom hcod.symm) :
    C.projection.IsHomLift f φ := by
  refine IsHomLift.of_fac' C.projection f φ ((C.object_projection a).trans hdom)
    ((C.object_projection b).trans hcod) ?_
  rw [projection_map_eq C φ, h]
  exact eqToHom_conj_collapse _ _ f _ _ _ _

end Construction

/-! ### Generalities on the induced functor -/

section Induced

universe u v₁ v₂ w₁ w₂

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S) {X : Type v₁} [Category.{w₁} X] (qX : X ⥤ Over S)
  {Y : Type v₂} [Category.{w₂} Y] (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = qX)
  (x₀ : X)
  (hx₀ : qX.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

attribute [local instance] categoryOfConstruction

/-- The induced functor does not change the Artinian local algebra of a deformation. -/
private lemma inducedFunctor_algebra
    (G : InducedPredeformationFunctor iΛ qX qY F hF x₀ hx₀)
    (a : (predeformationCategory iΛ qX x₀ hx₀).carrier) :
    ((predeformationCategory iΛ qY (F.obj x₀)
        (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).objects
      (G.toFunctor.obj a)).algebra =
      ((predeformationCategory iΛ qX x₀ hx₀).objects a).algebra :=
  (((predeformationCategory iΛ qY (F.obj x₀)
        (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).object_projection
      (G.toFunctor.obj a)).symm.trans
    (congrArg (fun H => H.obj a) G.projection_comm)).trans
    ((predeformationCategory iΛ qX x₀ hx₀).object_projection a)

/-- The induced functor carries a morphism to one with the same arrow of `𝒞_Λ`. -/
private lemma inducedFunctor_ringHom
    (G : InducedPredeformationFunctor iΛ qX qY F hF x₀ hx₀)
    {a b : (predeformationCategory iΛ qX x₀ hx₀).carrier} (φ : a ⟶ b) :
    ((predeformationCategory iΛ qY (F.obj x₀)
          (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).morphisms
        (G.toFunctor.obj a) (G.toFunctor.obj b) (G.toFunctor.map φ)).ringHom =
      eqToHom (inducedFunctor_algebra iΛ qX qY F hF x₀ hx₀ G a) ≫
        ((predeformationCategory iΛ qX x₀ hx₀).morphisms a b φ).ringHom ≫
        eqToHom (inducedFunctor_algebra iΛ qX qY F hF x₀ hx₀ G b).symm := by
  rw [← (predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).morphism_projection (G.toFunctor.map φ),
    ← (predeformationCategory iΛ qX x₀ hx₀).morphism_projection φ,
    ← functor_map_eq_of_eq G.projection_comm φ]
  simp [Functor.comp_map, Category.assoc, eqToHom_trans]

end Induced

/-! ### The lifting property along a first-order thickening -/

section Geometry

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴)

/-- The left component of the image of the arrow of a morphism of deformations is the spectrum
of its arrow of `𝒞_Λ`, up to the identifications of the base objects. -/
private lemma map_arrow_left_eq {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S} {x₀ : 𝒴.val.obj}
    {hx₀ : (𝒴.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : DeformationObject iΛ (𝒴.val.p ⋙ Over.post B.inclusion) x₀ hx₀}
    (m : DeformationMorphism iΛ (𝒴.val.p ⋙ Over.post B.inclusion) x₀ hx₀ a b) :
    ((𝒴.val.p ⋙ Over.post B.inclusion).map m.arrow).left =
      eqToHom (congrArg Over.left b.base) ≫
        Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
  rw [← m.arrow_base]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- The morphism of affine schemes underlying a morphism of deformations whose arrow of
`𝒞_Λ` is a surjection with square-zero kernel is a first-order thickening. -/
private lemma isFirstOrderThickening_map_arrow {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S} {x₀ : 𝒴.val.obj}
    {hx₀ : (𝒴.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : DeformationObject iΛ (𝒴.val.p ⋙ Over.post B.inclusion) x₀ hx₀}
    (m : DeformationMorphism iΛ (𝒴.val.p ⋙ Over.post B.inclusion) x₀ hx₀ a b)
    (hsurj : Function.Surjective m.ringHom.hom)
    (hker : RingHom.ker m.ringHom.hom.toRingHom ^ 2 = ⊥) :
    IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (𝒴.val.p.map m.arrow)) := by
  have hiSpec := Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom m.ringHom.hom.toRingHom) (by simpa using hsurj) (by simpa using hker)
  change IsFirstOrderThickening
    (((𝒴.val.p ⋙ Over.post B.inclusion).map m.arrow).left)
  rw [map_arrow_left_eq B S hS 𝒴 m]
  exact isFirstOrderThickening_eqToHom_conj _ _ _ hiSpec

/-- A morphism of the source category lying over an identity of the site, followed by an
identification of objects, has the corresponding identification of spectra as its base. -/
private lemma arrow_base_of_isHomLift_id {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {U : BigFppfOver B S hS} {c d e : 𝒴.val.obj} (ψ : c ⟶ d)
    (hψ : 𝒴.val.p.IsHomLift (𝟙 U) ψ) (hde : d = e)
    {A C : ArtinianLocalAlgCat.{u, u, u} Λ k} (hAC : C = A)
    (hc : (𝒴.val.p ⋙ Over.post B.inclusion).obj c =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (he : (𝒴.val.p ⋙ Over.post B.inclusion).obj e =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ)) :
    eqToHom (congrArg Over.left hc).symm ≫
        ((𝒴.val.p ⋙ Over.post B.inclusion).map (ψ ≫ eqToHom hde)).left ≫
        eqToHom (congrArg Over.left he) =
      Spec.map (CommRingCat.ofHom (eqToHom hAC).hom.toRingHom) := by
  let : 𝒴.val.p.IsHomLift (𝟙 U) ψ := hψ
  rw [specMap_eqToHom_hom hAC]
  cases hde
  rw [eqToHom_refl, Category.comp_id, Functor.comp_map,
    IsHomLift.fac' 𝒴.val.p (𝟙 U) ψ, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_map,
    CategoryTheory.Functor.map_id]
  simp

variable [instX : 𝒳.val.p.IsFibered] [instY : 𝒴.val.p.IsFibered]

/-- The commuting square supplied by formal smoothness on objects, read as a factorization of
the chosen pullback of the object downstairs through the image of the chosen pullback of the
lifted object. -/
private theorem pullbackMap_fac_of_compare {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    {x : 𝒳.val.p.Fiber U} {y' : 𝒴.val.p.Fiber U'}
    {γ : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
        (CatFiberedInGroupoids.homFunctor_comp_p p) U).obj x ≅
      Functor.pullbackFiber 𝒴.val.p y' i}
    {x' : 𝒳.val.p.Fiber U'} {β : Functor.pullbackFiber 𝒳.val.p x' i ≅ x}
    {γ' : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
        (CatFiberedInGroupoids.homFunctor_comp_p p) U').obj x' ≅ y'}
    {cmp : Functor.pullbackFiber 𝒴.val.p
        ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
          (CatFiberedInGroupoids.homFunctor_comp_p p) U').obj x') i ≅
      (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
        (CatFiberedInGroupoids.homFunctor_comp_p p) U).obj
          (Functor.pullbackFiber 𝒳.val.p x' i)}
    (hcmp : Functor.Fiber.fiberInclusion.map cmp.hom ≫
        (CatFiberedInGroupoids.homFunctor p).map (Functor.IsPreFibered.pullbackMap x'.2 i) =
      Functor.IsPreFibered.pullbackMap
        ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
          (CatFiberedInGroupoids.homFunctor_comp_p p) U').obj x').2 i)
    (hsq : (cmp.hom ≫
        (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
          (CatFiberedInGroupoids.homFunctor_comp_p p) U).map β.hom) ≫ γ.hom =
      Functor.pullbackFiberHom (p := 𝒴.val.p) γ'.hom i) :
    Functor.Fiber.fiberInclusion.map γ.hom ≫
        Functor.IsPreFibered.pullbackMap y'.2 i =
      (CatFiberedInGroupoids.homFunctor p).map
          (Functor.Fiber.fiberInclusion.map β.inv ≫
            Functor.IsPreFibered.pullbackMap x'.2 i) ≫
        Functor.Fiber.fiberInclusion.map γ'.hom := by
  set F := CatFiberedInGroupoids.homFunctor p with hFdef
  set pbY := Functor.IsPreFibered.pullbackMap y'.2 i with hpbY
  set pbX := Functor.IsPreFibered.pullbackMap x'.2 i with hpbX
  have hsqMap := congrArg Functor.Fiber.fiberInclusion.map hsq
  have h := congrArg (fun t => t ≫ pbY) hsqMap
  rw [Functor.Fiber.fiberInclusion.map_comp, Functor.Fiber.fiberInclusion.map_comp] at h
  rw [Functor.Fiber.fiberInclusion_map_mapOfComp_map 𝒳.val.p 𝒴.val.p F
    (CatFiberedInGroupoids.homFunctor_comp_p p) U β.hom] at h
  have h' : (Functor.Fiber.fiberInclusion.map cmp.hom ≫ F.map
        (Functor.Fiber.fiberInclusion.map β.hom) ≫
        Functor.Fiber.fiberInclusion.map γ.hom) ≫ pbY =
      Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom γ'.hom i) ≫ pbY := by
    simpa [Category.assoc] using h
  rw [Functor.pullbackFiberHom_fac γ'.hom i, ← hcmp] at h'
  have hcancel := (cancel_epi (Functor.Fiber.fiberInclusion.map cmp.hom)).mp
    (by simp only [Category.assoc] at h' ⊢; exact h')
  have hβ : F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
      F.map (Functor.Fiber.fiberInclusion.map β.hom) = 𝟙 _ := by
    simp
  calc
    Functor.Fiber.fiberInclusion.map γ.hom ≫ pbY =
        (F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
          F.map (Functor.Fiber.fiberInclusion.map β.hom)) ≫
            (Functor.Fiber.fiberInclusion.map γ.hom ≫ pbY) := by
        rw [hβ, Category.id_comp]
    _ = F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
          (F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
            Functor.Fiber.fiberInclusion.map γ.hom ≫ pbY) := by
        simp only [Category.assoc]
    _ = F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
          (F.map pbX ≫ Functor.Fiber.fiberInclusion.map γ'.hom) := by
        rw [hcancel]
    _ = F.map (Functor.Fiber.fiberInclusion.map β.inv ≫ pbX) ≫
          Functor.Fiber.fiberInclusion.map γ'.hom := by
        rw [F.map_comp, Category.assoc]

end Geometry

/-! ### Smoothness on predeformation categories -/

section Main

universe u v w

attribute [local instance] categoryOfConstruction

/-- **Stacks 07WK**, case (1). A 1-morphism of categories fibred in groupoids over the big
fppf category of `S` which is formally smooth on objects induces a smooth functor of
predeformation categories at every finite type field-valued point of the source.

This is also the formally-smooth-on-objects clause of Stacks 07XW — the condition the
openness-of-versality statement is about — so both tags are registered here, on the declaration
that carries the proof. -/
@[stacks 07WK "formally smooth on objects",
  stacks 07XW "the formally-smooth-on-objects clause: formally smooth on objects implies smooth \
on predeformation categories"]
public theorem isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) := by
  classical
  dsimp [IsSmoothOnPredeformationCategories]
  intro Λ k instComm instField instAlg iΛ x₀ hx₀ hLFT hQC hOpen
  let : CommRing Λ := instComm
  let : Field k := instField
  let : Algebra Λ k := instAlg
  let qX := 𝒳.val.p ⋙ Over.post B.inclusion
  let qY := 𝒴.val.p ⋙ Over.post B.inclusion
  let F := CatFiberedInGroupoids.homFunctor p
  let hF' : F ⋙ qY = qX := by
    dsimp [qX, qY]
    simpa only [Functor.assoc] using
      congrArg (fun q => q ⋙ Over.post B.inclusion)
        (CatFiberedInGroupoids.homFunctor_comp_p p)
  let hx₀' := hx₀
  let Cx := predeformationCategory iΛ qX x₀ hx₀'
  let hy₀ := imageBasePoint (qY := qY) iΛ qX F hF' x₀ hx₀'
  let Cy := predeformationCategory iΛ qY (F.obj x₀) hy₀
  let G := mapPredeformationCategory iΛ qX qY F hF' x₀ hx₀'
  have hpreX := predeformationCategory_isPredeformationCategory B hS iΛ 𝒳.val.p x₀ hx₀'
    𝒳.isFiberedInGroupoids
  have hcofX : Deformation.IsCofiberedInGroupoids Cx.projection := by
    simpa [Cx, qX] using hpreX.cofibered
  have hpreY := predeformationCategory_isPredeformationCategory B hS iΛ 𝒴.val.p (F.obj x₀) hy₀
    𝒴.isFiberedInGroupoids
  have hcofY : Deformation.IsCofiberedInGroupoids Cy.projection := by
    simpa [Cy, qY, F, hy₀] using hpreY.cofibered
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hsmall : ∀ ⦃A₁ A₂ : ArtinianLocalAlgCat.{u, u, u} Λ k⦄ (f : A₁ ⟶ A₂),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (y : Cy.carrier) (x : Cx.carrier) (g : y ⟶ G.toFunctor.obj x),
        Cy.projection.IsHomLift f g →
          ∃ (x' : Cx.carrier) (lift : x' ⟶ x) (a : G.toFunctor.obj x' ⟶ y),
            Cx.projection.IsHomLift f lift ∧
              Cy.projection.IsHomLift (𝟙 A₁) a ∧ G.toFunctor.map lift = a ≫ g := by
    intro A₁ A₂ f hf y x g hg
    let : Cy.projection.IsHomLift f g := hg
    let dx := Cx.objects x
    let dFx := Cy.objects (G.toFunctor.obj x)
    let dy := Cy.objects y
    let m := Cy.morphisms y (G.toFunctor.obj x) g
    have hpoint : dFx.point = F.obj dx.point := G.object_point x
    have hAlg : dFx.algebra = dx.algebra :=
      inducedFunctor_algebra iΛ qX qY F hF' x₀ hx₀' G x
    -- The arrow of `𝒞_Λ` carried by `m` is a surjection with square-zero kernel.
    let eDy : Cy.projection.obj y ≅ dy.algebra := eqToIso (Cy.object_projection y)
    let eFx : Cy.projection.obj (G.toFunctor.obj x) ≅ dFx.algebra :=
      eqToIso (Cy.object_projection (G.toFunctor.obj x))
    have hdomA : Cy.projection.obj y = A₁ := IsHomLift.domain_eq Cy.projection f g
    have hcodA : Cy.projection.obj (G.toFunctor.obj x) = A₂ :=
      IsHomLift.codomain_eq Cy.projection f g
    have hA1 : dy.algebra = A₁ := (Cy.object_projection y).symm.trans hdomA
    have hAFx : dFx.algebra = A₂ :=
      (Cy.object_projection (G.toFunctor.obj x)).symm.trans hcodA
    have hA2 : dx.algebra = A₂ := hAlg.symm.trans hAFx
    have hring : m.ringHom = eDy.inv ≫ Cy.projection.map g ≫ eFx.hom := by
      simpa [m, eDy, eFx] using (Cy.morphism_projection g).symm
    have hringf : m.ringHom = eqToHom hA1 ≫ f ≫ eqToHom hAFx.symm := by
      rw [hring, IsHomLift.fac' Cy.projection f g]
      simp only [eDy, eFx, eqToIso.inv, eqToIso.hom]
      exact eqToHom_conj_collapse _ _ f _ _ _ _
    obtain ⟨hsurj, hkerSq⟩ := surjective_and_ker_sq_of_eq_iso_comp hf
      (eqToIso hA1) (eqToIso hAFx.symm) hringf
    -- The lifting problem in the site.
    let U := 𝒴.val.p.obj dFx.point
    let U' := 𝒴.val.p.obj dy.point
    let i : U ⟶ U' := 𝒴.val.p.map m.arrow
    have hUfiber : U = 𝒳.val.p.obj dx.point := by
      dsimp only [U]
      calc
        𝒴.val.p.obj dFx.point = 𝒴.val.p.obj (F.obj dx.point) :=
          congrArg (fun z => 𝒴.val.p.obj z) hpoint
        _ = 𝒳.val.p.obj dx.point :=
          congrArg (fun H => H.obj dx.point) (CatFiberedInGroupoids.homFunctor_comp_p p)
    let xFiber : 𝒳.val.p.Fiber U := ⟨dx.point, hUfiber.symm⟩
    let yFiber : 𝒴.val.p.Fiber U' := ⟨dy.point, rfl⟩
    let pU := Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F
      (CatFiberedInGroupoids.homFunctor_comp_p p) U
    let pU' := Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F
      (CatFiberedInGroupoids.homFunctor_comp_p p) U'
    have hmapObj : pU.obj xFiber = ⟨dFx.point, rfl⟩ := Subtype.ext hpoint.symm
    let : 𝒴.val.p.IsHomLift i m.arrow := inferInstance
    let : 𝒴.val.p.IsStronglyCartesian i m.arrow :=
      𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i m.arrow
    let targetCompare : Functor.pullbackFiber 𝒴.val.p yFiber i ≅ ⟨dFx.point, rfl⟩ :=
      Functor.fiberIsoOfCartesian i (Functor.IsPreFibered.pullbackMap yFiber.2 i) m.arrow
        inferInstance inferInstance
    let gamma : pU.obj xFiber ≅ Functor.pullbackFiber 𝒴.val.p yFiber i :=
      eqToIso hmapObj ≪≫ targetCompare.symm
    have haff (d : DeformationObject iΛ qY (F.obj x₀) hy₀) :
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.p.obj d.point)) := by
      have hbase : (BigFppfOver.toScheme B S hS).obj (𝒴.val.p.obj d.point) =
          Spec (.of (↑d.algebra)) := by
        change B.inclusion.obj (𝒴.val.p.obj d.point).left = _
        simpa [qY, BigFppfOver.toScheme, BigFppfOver.forget] using
          congrArg (fun z => z.left) d.base
      exact hbase ▸ (inferInstance : IsAffine (Spec (.of (↑d.algebra))))
    have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := haff dFx
    have hU'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj U') := haff dy
    have hi : IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) :=
      isFirstOrderThickening_map_arrow B S hS 𝒴 m hsurj hkerSq
    unfold Stack.IsFormallySmoothOnObjects at hp
    obtain ⟨x', β, γ', hsq⟩ := hp U U' i hUaff hU'aff hi xFiber yFiber gamma
    -- The lifted arrow upstairs and its base.
    let pbXMap := Functor.IsPreFibered.pullbackMap x'.2 i
    let liftArrow : dx.point ⟶ x'.1 := Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap
    have hpbX : 𝒳.val.p.IsHomLift i pbXMap :=
      (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 i).toIsHomLift
    have hLift : 𝒳.val.p.IsHomLift i liftArrow := by
      have hcomp := @IsHomLift.comp _ _ _ _ 𝒳.val.p U U U'
        xFiber.1 (Functor.pullbackFiber 𝒳.val.p x' i).1 x'.1
        (𝟙 U) i (Functor.Fiber.fiberInclusion.map β.inv) pbXMap β.inv.2 hpbX
      simpa [liftArrow, Category.id_comp, Functor.Fiber.fiberInclusion] using hcomp
    let : 𝒳.val.p.IsHomLift i liftArrow := hLift
    have hnewBase : qX.obj x'.1 =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ dy.algebra)) ≫ iΛ) := by
      calc
        qX.obj x'.1 = (Over.post B.inclusion).obj U' :=
          congrArg (Over.post B.inclusion).obj x'.2
        _ = qY.obj dy.point := rfl
        _ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ dy.algebra)) ≫ iΛ) := dy.base
    have hSpecAlg : Spec (.of (↑dFx.algebra)) = Spec (.of (↑dx.algebra)) :=
      congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (.of (↑A))) hAlg
    have hpostEq : qX.map liftArrow = (Over.post B.inclusion).map
        (eqToHom (IsHomLift.domain_eq 𝒳.val.p i liftArrow) ≫ i ≫
          eqToHom (IsHomLift.codomain_eq 𝒳.val.p i liftArrow).symm) := by
      change (Over.post B.inclusion).map (𝒳.val.p.map liftArrow) = _
      exact congrArg (fun t : 𝒳.val.p.obj dx.point ⟶ 𝒳.val.p.obj x'.1 =>
        (Over.post B.inclusion).map t) (IsHomLift.fac' 𝒳.val.p i liftArrow)
    have hmleft := map_arrow_left_eq B S hS 𝒴 m
    have hLiftBase :
        eqToHom (congrArg Over.left dx.base).symm ≫ (qX.map liftArrow).left ≫
            eqToHom (congrArg Over.left hnewBase) =
          eqToHom hSpecAlg.symm ≫ Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) := by
      rw [hpostEq, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
        show (Over.post B.inclusion).map i = qY.map m.arrow from rfl]
      simp only [Over.comp_left, Over.eqToHom_left, Category.assoc]
      rw [hmleft]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id]
    have hcast : Spec.map (CommRingCat.ofHom (m.ringHom ≫ eqToHom hAlg).hom.toRingHom) =
        eqToHom hSpecAlg.symm ≫ Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) := by
      have hc : ((eqToHom hAlg).hom.comp m.ringHom.hom).toRingHom =
          (eqToHom hAlg).hom.toRingHom.comp m.ringHom.hom.toRingHom :=
        rfl
      rw [← specMap_eqToHom_hom hAlg, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ArtinianLocalAlgCat.comp_hom, hc]
    have hLiftBase' :
        eqToHom (congrArg Over.left dx.base).symm ≫ (qX.map liftArrow).left ≫
            eqToHom (congrArg Over.left hnewBase) =
          Spec.map (CommRingCat.ofHom (m.ringHom ≫ eqToHom hAlg).hom.toRingHom) := by
      rw [hcast]
      exact hLiftBase
    -- The new deformation and the morphism down to the given one.
    let newDeformation : DeformationObject iΛ qX x₀ hx₀' :=
      dx.extend dy.algebra (m.ringHom ≫ eqToHom hAlg) x'.1 liftArrow hnewBase hLiftBase'
    let liftDataNew : DeformationMorphism iΛ qX x₀ hx₀' newDeformation dx :=
      dx.extendHom dy.algebra (m.ringHom ≫ eqToHom hAlg) x'.1 liftArrow hnewBase hLiftBase'
    let xNew : Cx.carrier := Cx.objects.symm newDeformation
    have hxNew : Cx.objects xNew = newDeformation := Cx.objects.apply_symm_apply _
    let liftData : DeformationMorphism iΛ qX x₀ hx₀' (Cx.objects xNew) dx :=
      hxNew.symm ▸ liftDataNew
    let lift : xNew ⟶ x := (Cx.morphisms xNew x).symm liftData
    have hAlgNew : (Cx.objects xNew).algebra = newDeformation.algebra :=
      congrArg DeformationObject.algebra hxNew
    have hdomX : (Cx.objects xNew).algebra = A₁ := hAlgNew.trans hA1
    have hlift : Cx.morphisms xNew x lift = liftData := (Cx.morphisms xNew x).apply_symm_apply _
    have hliftRing0 : (Cx.morphisms xNew x lift).ringHom =
        eqToHom hAlgNew ≫ m.ringHom ≫ eqToHom hAlg := by
      rw [hlift]
      exact deformationMorphism_ringHom_cast hxNew liftDataNew
    have hliftRing : (Cx.morphisms xNew x lift).ringHom =
        eqToHom hdomX ≫ f ≫ eqToHom hA2.symm := by
      rw [hliftRing0, hringf]
      exact eqToHom_conj_collapse _ _ f _ _ _ _
    have hLiftProp : Cx.projection.IsHomLift f lift :=
      isHomLift_of_ringHom_eq Cx f lift hdomX hA2 hliftRing
    -- The comparison isomorphism downstairs.
    have hEqPoint : Functor.Fiber.fiberInclusion.map (eqToIso hmapObj).hom =
        eqToHom hpoint.symm := by
      rw [eqToIso.hom, eqToHom_map]
    have himage : eqToHom hpoint.symm ≫ m.arrow =
        F.map liftArrow ≫ Functor.Fiber.fiberInclusion.map γ'.hom := by
      have htc : Functor.Fiber.fiberInclusion.map targetCompare.inv ≫
          Functor.IsPreFibered.pullbackMap yFiber.2 i = m.arrow :=
        Functor.fiberIsoOfCartesian_inv_fac (p := 𝒴.val.p) (b := i) (a := dy.point)
          (z := Functor.pullbackFiber 𝒴.val.p yFiber i) (z' := ⟨dFx.point, rfl⟩)
          (φ := Functor.IsPreFibered.pullbackMap yFiber.2 i) (φ' := m.arrow)
          (hφ := Functor.IsPreFibered.pullbackMap.IsCartesian _ _) (hφ' := inferInstance)
      have hfac : Functor.Fiber.fiberInclusion.map gamma.hom ≫
          Functor.IsPreFibered.pullbackMap yFiber.2 i =
            F.map (Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap) ≫
              Functor.Fiber.fiberInclusion.map γ'.hom := by
        refine pullbackMap_fac_of_compare B S hS 𝒳 𝒴 p i ?_ hsq
        apply Functor.fiberIsoOfCartesian_hom_fac
      calc
        eqToHom hpoint.symm ≫ m.arrow = Functor.Fiber.fiberInclusion.map gamma.hom ≫
            Functor.IsPreFibered.pullbackMap yFiber.2 i := by
          rw [← hEqPoint]
          dsimp only [gamma]
          rw [Iso.trans_hom, Iso.symm_hom, Functor.Fiber.fiberInclusion.map_comp,
            Category.assoc, htc]
        _ = F.map (Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap) ≫
            Functor.Fiber.fiberInclusion.map γ'.hom := hfac
        _ = F.map liftArrow ≫ Functor.Fiber.fiberInclusion.map γ'.hom := rfl
    -- The comparison morphism `G xNew ⟶ y`.
    let dFNew := Cy.objects (G.toFunctor.obj xNew)
    have hpointCx : (Cx.objects xNew).point = x'.1 :=
      congrArg DeformationObject.point hxNew
    have hpointNew : dFNew.point = F.obj x'.1 :=
      (G.object_point xNew).trans (congrArg F.obj hpointCx)
    have hcastPoint : eqToHom (congrArg F.obj hpointCx).symm ≫
        eqToHom (G.object_point xNew).symm = eqToHom hpointNew.symm := by
      rw [eqToHom_trans]
    have hAlgImage : dFNew.algebra = dy.algebra :=
      (inducedFunctor_algebra iΛ qX qY F hF' x₀ hx₀' G xNew).trans hAlgNew
    have hγcancel : Functor.Fiber.fiberInclusion.map γ'.hom ≫
        Functor.Fiber.fiberInclusion.map γ'.inv = 𝟙 _ := by
      simp
    let aArrow : dy.point ⟶ dFNew.point :=
      Functor.Fiber.fiberInclusion.map γ'.inv ≫ eqToHom hpointNew.symm
    have hFxArrow : dFx.arrow = F.map dx.arrow ≫ eqToHom hpoint.symm := G.object_arrow x
    have hnewArrow : dFNew.arrow =
        F.map dx.arrow ≫ F.map liftArrow ≫ eqToHom hpointNew.symm := by
      have hmapArrow : F.map ((Cx.objects xNew).arrow) ≫ eqToHom (congrArg F.obj hpointCx) =
          F.map (dx.arrow ≫ liftArrow) := by
        have h := congrArg F.map (deformationObject_arrow_comp_eqToHom hxNew)
        rw [Functor.map_comp, eqToHom_map] at h
        exact h
      rw [G.object_arrow xNew]
      calc
        F.map ((Cx.objects xNew).arrow) ≫ eqToHom (G.object_point xNew).symm =
            (F.map ((Cx.objects xNew).arrow) ≫ eqToHom (congrArg F.obj hpointCx)) ≫
              eqToHom (congrArg F.obj hpointCx).symm ≫
                eqToHom (G.object_point xNew).symm := by
          simp [Category.assoc]
        _ = F.map (dx.arrow ≫ liftArrow) ≫ eqToHom hpointNew.symm := by
          rw [hmapArrow, hcastPoint]
        _ = F.map dx.arrow ≫ F.map liftArrow ≫ eqToHom hpointNew.symm := by
          rw [Functor.map_comp, Category.assoc]
    let aData : DeformationMorphism iΛ qY (F.obj x₀) hy₀ dFNew dy :=
      { ringHom := eqToHom hAlgImage
        arrow := aArrow
        triangle := by
          calc
            dy.arrow ≫ aArrow = (dFx.arrow ≫ m.arrow) ≫ aArrow := by rw [m.triangle]
            _ = (F.map dx.arrow ≫ eqToHom hpoint.symm ≫ m.arrow) ≫ aArrow := by
                rw [hFxArrow]
                simp only [Category.assoc]
            _ = (F.map dx.arrow ≫ F.map liftArrow ≫
                  Functor.Fiber.fiberInclusion.map γ'.hom) ≫ aArrow := by rw [himage]
            _ = F.map dx.arrow ≫ F.map liftArrow ≫ eqToHom hpointNew.symm := by
                simp only [aArrow, Category.assoc]
                rw [← Category.assoc (Functor.Fiber.fiberInclusion.map γ'.hom),
                  hγcancel, Category.id_comp]
            _ = dFNew.arrow := hnewArrow.symm
        arrow_base :=
          arrow_base_of_isHomLift_id B S hS 𝒴 (Functor.Fiber.fiberInclusion.map γ'.inv)
            γ'.inv.2 hpointNew.symm hAlgImage dy.base dFNew.base }
    let a : G.toFunctor.obj xNew ⟶ y := (Cy.morphisms (G.toFunctor.obj xNew) y).symm aData
    have ha : Cy.morphisms (G.toFunctor.obj xNew) y a = aData :=
      (Cy.morphisms (G.toFunctor.obj xNew) y).apply_symm_apply _
    have haLift : Cy.projection.IsHomLift (𝟙 A₁) a := by
      refine isHomLift_of_ringHom_eq Cy (𝟙 A₁) a (hAlgImage.trans hA1) hA1 ?_
      rw [ha]
      exact eqToHom_eq_id_conj hAlgImage (hAlgImage.trans hA1) hA1
    refine ⟨xNew, lift, a, hLiftProp, haLift, ?_⟩
    -- The two morphisms `G xNew ⟶ G x` agree.
    apply (Cy.morphisms (G.toFunctor.obj xNew) (G.toFunctor.obj x)).injective
    apply DeformationMorphism.ext_of_components
    · rw [inducedFunctor_ringHom iΛ qX qY F hF' x₀ hx₀' G lift,
        morphisms_comp_ringHom Cy a g, hliftRing0, ha]
      exact eqToHom_conj_collapse_comp _ _ m.ringHom _ _ hAlgImage
    · have hliftArrow : (Cx.morphisms xNew x lift).arrow =
          liftArrow ≫ eqToHom hpointCx.symm := by
        rw [hlift]
        exact deformationMorphism_arrow_cast hxNew liftDataNew
      have hpointEq : G.object_point x = hpoint := Subsingleton.elim _ _
      have hMArrow : m.arrow ≫ Functor.Fiber.fiberInclusion.map γ'.inv =
          eqToHom hpoint ≫ F.map liftArrow := by
        calc
          m.arrow ≫ Functor.Fiber.fiberInclusion.map γ'.inv =
              eqToHom hpoint ≫ (eqToHom hpoint.symm ≫ m.arrow) ≫
                Functor.Fiber.fiberInclusion.map γ'.inv := by simp [Category.assoc]
          _ = eqToHom hpoint ≫ (F.map liftArrow ≫
                Functor.Fiber.fiberInclusion.map γ'.hom) ≫
                Functor.Fiber.fiberInclusion.map γ'.inv := by rw [himage]
          _ = eqToHom hpoint ≫ F.map liftArrow := by
              simp only [Category.assoc, hγcancel]
              exact congrArg (fun t => eqToHom hpoint ≫ t)
                (Category.comp_id (F.map liftArrow))
      calc
        (Cy.morphisms (G.toFunctor.obj xNew) (G.toFunctor.obj x)
              (G.toFunctor.map lift)).arrow =
            eqToHom hpoint ≫ F.map (liftArrow ≫ eqToHom hpointCx.symm) ≫
              eqToHom (G.object_point xNew).symm := by
          rw [G.morphism_arrow lift, hpointEq, hliftArrow]
        _ = eqToHom hpoint ≫ F.map liftArrow ≫ eqToHom (congrArg F.obj hpointCx).symm ≫
            eqToHom (G.object_point xNew).symm := by
          rw [Functor.map_comp, eqToHom_map]
          simp [Category.assoc]
        _ = (m.arrow ≫ Functor.Fiber.fiberInclusion.map γ'.inv) ≫
            eqToHom (congrArg F.obj hpointCx).symm ≫
              eqToHom (G.object_point xNew).symm := by
          rw [hMArrow]
          simp [Category.assoc]
        _ = m.arrow ≫ aData.arrow := by simp [aData, aArrow, Category.assoc]
        _ = (Cy.morphisms (G.toFunctor.obj xNew) (G.toFunctor.obj x) (a ≫ g)).arrow := by
          have hrev := Cy.reversed_composition (f := a) (g := g)
          rw [hrev, ha]
  exact Deformation.isSmooth_of_lifts_smallExtensions hcofX hcofY G.toBasedFunctor hsmall

/-- **Stacks 07WK**, case (2). A 1-morphism of categories fibred in groupoids over the big fppf
category of `S` which is representable by algebraic spaces and formally smooth induces a smooth
functor of predeformation categories at every finite type field-valued point of the source. -/
@[stacks 07WK "representably formally smooth"]
public theorem isSmoothOnPredeformationCategories_of_isRelativelyFormallySmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hform : BigFppfOver.IsRelativelyFormallySmooth B S hS p) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) :=
  isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects B S hS p
    (BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth B S hS p hrep hform)

/-- A special case of `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`,
with the implication of Stacks 04AM from smoothness to formal smoothness as an extra hypothesis
`hFS`. The full version is not available in this module: its own module imports this one. -/
public theorem isSmoothOnPredeformationCategories_of_isRelativelySmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hsmooth : Stack.IsRelativelySmooth B S hS p)
    (hFS : ∀ {X Y : AlgebraicSpaces B S hS} (m : X ⟶ Y),
      Space.IsSmooth B S hS m.hom → Space.FormallySmooth m.hom) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) := by
  obtain ⟨hrep, hP⟩ := hsmooth
  refine isSmoothOnPredeformationCategories_of_isRelativelyFormallySmooth B S hS p hrep ?_
  intro U y hy F hF hE
  exact hFS _ (hP U y hy F hF hE)

end Main

end Deformation.Artin


end
