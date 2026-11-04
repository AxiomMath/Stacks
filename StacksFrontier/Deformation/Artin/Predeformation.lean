module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Basic

/-!
# The predeformation category of a point of a fibred category

Fix a category `X` over schemes over `S`, a point `x₀` of `X` lying over `Spec k`, and a
factorization of that point through `Spec Λ`. A *deformation* of `x₀` is an arrow
`x₀ ⟶ x` of `X` whose image in schemes over `S` is the canonical closed-point map
`Spec k ⟶ Spec A`, for `A` an Artinian local `Λ`-algebra with residue field identified
with `k`. Arrows between deformations reverse the arrows of `X`, so that the resulting
category `𝓕_{𝓧,k,x₀}` lies *covariantly* over the category `𝒞_Λ` of Artinian local
algebras.

This file constructs that category together with its projection to `𝒞_Λ`, records the
Artinian local factorizations of a finite-type field-valued point that the construction
starts from, and shows that a morphism over the base induces a functor of predeformation
categories over `𝒞_Λ`.

## Main definitions

* `Deformation.Artin.ArtinianLocalFactorization` — a factorization
  `Spec k ⟶ Spec A ⟶ S` of a finite-type field-valued point of a locally Noetherian
  scheme, with `A` Artinian local and residue field identified with `k`.
* `Deformation.Artin.residueMap` — the map to the fixed residue field attached to an
  object of `𝒞_Λ`.
* `Deformation.Artin.DeformationObject` — an object of the predeformation category.
* `Deformation.Artin.DeformationMorphism` — one of its reversed arrows.
* `Deformation.Artin.PredeformationConstruction` — the category, its projection, and the
  descriptions of its objects and morphisms.
* `Deformation.Artin.InducedPredeformationFunctor` — the induced functor of
  predeformation categories, together with its action on objects and reversed arrows.

## Main results

* `Deformation.Artin.predeformationCategory` constructs the category and its projection
  to `𝒞_Λ`.
* `Deformation.Artin.mapPredeformationCategory` constructs the induced functor over
  `𝒞_Λ`.

## References

* [Stacks Project, Tag 07T2](https://stacks.math.columbia.edu/tag/07T2)
* [Stacks Project, Tag 07T3](https://stacks.math.columbia.edu/tag/07T3)
* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
* [Stacks Project, Tag 07WJ](https://stacks.math.columbia.edu/tag/07WJ)
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Artinian local factorizations of a field-valued point -/

section

open CategoryTheory AlgebraicGeometry

universe u

/-- A factorization `Spec(k) ⟶ Spec(A) ⟶ S` of a finite-type field-valued point
of a locally Noetherian scheme, where `A` is an Artinian local ring and the first arrow
identifies `k` with its residue field. -/
@[stacks 07T3]
public structure ArtinianLocalFactorization (S : Scheme.{u}) (k : Type u) [Field k]
    (x : Spec (CommRingCat.of k) ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType x]
    [QuasiCompact x] where
  /-- The Artinian local ring through whose spectrum the point factors. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [isArtinianRing : IsArtinianRing carrier]
  [isLocalRing : IsLocalRing carrier]
  /-- The specified identification of the residue field of `A` with `k`. -/
  residueEquiv : IsLocalRing.ResidueField carrier ≃+* k
  /-- The second arrow `Spec(A) ⟶ S` in the factorization. -/
  toBase : Spec (CommRingCat.of carrier) ⟶ S
  /-- The two arrows compose to the original field-valued point. -/
  fac : Scheme.Spec.map (CommRingCat.ofHom
      (residueEquiv.toRingHom.comp (IsLocalRing.residue carrier))).op ≫ toBase = x

namespace ArtinianLocalFactorization

variable {S : Scheme.{u}} {k : Type u} [Field k] {x : Spec (CommRingCat.of k) ⟶ S}
  [IsLocallyNoetherian S] [LocallyOfFiniteType x] [QuasiCompact x]

attribute [instance] commRing isArtinianRing isLocalRing

instance : CoeSort (ArtinianLocalFactorization S k x) (Type u) := ⟨carrier⟩

attribute [coe] carrier

end ArtinianLocalFactorization

end

/-! ### The predeformation category of a point -/

section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
variable (x₀ : X)
variable (hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The map to the fixed residue field attached to an object of `𝒞_Λ`. -/
public noncomputable def residueMap
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) : A →+* k :=
  A.residueEquiv.toAlgHom.toRingHom.comp (residue A)

/-- The residue maps are compatible with the arrows of `𝒞_Λ`. -/
public theorem residueMap_comp {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : B ⟶ A) :
    (residueMap A).comp f.hom.toRingHom = residueMap B :=
  RingHom.ext f.residue_comm

/-- An arrow `x₀ ⟶ x` over the canonical closed-point map
`Spec k ⟶ Spec A`, where `A` belongs to `𝒞_Λ`. -/
public structure DeformationObject where
  /-- The Artinian local `Λ`-algebra the deformation lives over. -/
  algebra : ArtinianLocalAlgCat.{u, u, u} Λ k
  /-- The object of `X` that `x₀` deforms to. -/
  point : X
  /-- The arrow of `X` exhibiting the deformation. -/
  arrow : x₀ ⟶ point
  /-- The deformed object lies over `Spec` of the chosen algebra. -/
  base : q.obj point = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ algebra)) ≫ iΛ)
  /-- The arrow lies over the canonical closed-point map. -/
  arrow_base :
    eqToHom (congrArg Over.left hx₀).symm ≫ (q.map arrow).left ≫
      eqToHom (congrArg Over.left base) =
        Spec.map (CommRingCat.ofHom (residueMap algebra))

section Ext

variable {iΛ : Spec (.of Λ) ⟶ S} {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {a b : DeformationObject iΛ q x₀ hx₀}

/-- Two deformations are equal when their algebras and deformed objects agree and
`a.arrow = b.arrow ≫ eqToHom hpoint.symm`. -/
public theorem deformationObject_ext_of_arrow (halg : a.algebra = b.algebra)
    (hpoint : a.point = b.point) (harrow : a.arrow = b.arrow ≫ eqToHom hpoint.symm) : a = b := by
  cases a
  cases b
  cases halg
  cases hpoint
  simp only [eqToHom_refl, Category.comp_id] at harrow
  cases harrow
  rfl

/-- Two deformations are equal when their algebras and deformed objects agree and
`a.arrow ≫ eqToHom hpoint = b.arrow`. -/
public theorem deformationObject_ext_of_arrow_comp (halg : a.algebra = b.algebra)
    (hpoint : a.point = b.point) (harrow : a.arrow ≫ eqToHom hpoint = b.arrow) : a = b :=
  deformationObject_ext_of_arrow halg hpoint (by simp [← harrow])

end Ext

/-- A morphism between deformations consists of a reversed arrow in `X`, commuting
with the maps from `x₀`, and the corresponding arrow of `𝒞_Λ`. -/
public structure DeformationMorphism
    (a b : DeformationObject iΛ q x₀ hx₀) where
  /-- The arrow of `𝒞_Λ` the morphism lies over. -/
  ringHom : a.algebra ⟶ b.algebra
  /-- The reversed arrow of `X`. -/
  arrow : b.point ⟶ a.point
  /-- The reversed arrow commutes with the two arrows out of `x₀`. -/
  triangle : b.arrow ≫ arrow = a.arrow
  /-- The reversed arrow lies over the spectrum of the given arrow of `𝒞_Λ`. -/
  arrow_base :
    eqToHom (congrArg Over.left b.base).symm ≫ (q.map arrow).left ≫
      eqToHom (congrArg Over.left a.base) =
        Spec.map (CommRingCat.ofHom ringHom.hom.toRingHom)

/-- A category and projection realizing exactly the specified deformation objects and
reversed morphisms. The equations also fix the projection on objects and arrows. -/
public structure PredeformationConstruction where
  /-- The underlying type of the predeformation category. -/
  carrier : Type (max (u + 1) v w)
  [category : Category.{max u w} carrier]
  /-- The projection to `𝒞_Λ`. -/
  projection : carrier ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k
  /-- Its objects are exactly the deformations of `x₀`. -/
  objects : carrier ≃ DeformationObject iΛ q x₀ hx₀
  /-- Its arrows are exactly the morphisms of deformations. -/
  morphisms : ∀ a b : carrier,
    (a ⟶ b) ≃ DeformationMorphism iΛ q x₀ hx₀ (objects a) (objects b)
  /-- The projection sends a deformation to its Artinian local algebra. -/
  object_projection : ∀ a : carrier, projection.obj a = (objects a).algebra
  /-- The projection sends a morphism to its arrow of `𝒞_Λ`. -/
  morphism_projection : ∀ {a b : carrier} (f : a ⟶ b),
    eqToHom (object_projection a).symm ≫ projection.map f ≫
      eqToHom (object_projection b) = (morphisms a b f).ringHom
  /-- The reversed arrow of an identity is an identity. -/
  reversed_identity : ∀ a : carrier,
    (morphisms a a (𝟙 a)).arrow = 𝟙 (objects a).point
  /-- The reversed arrow of a composite is the composite in the opposite order. -/
  reversed_composition : ∀ {a b c : carrier} (f : a ⟶ b) (g : b ⟶ c),
    (morphisms a c (f ≫ g)).arrow =
      (morphisms b c g).arrow ≫ (morphisms a b f).arrow

/-- Two morphisms of deformations are equal as soon as their arrow of `𝒞_Λ` and their
reversed arrow of `X` agree. -/
public theorem DeformationMorphism.ext_of_components
    {a b : DeformationObject iΛ q x₀ hx₀}
    {f g : DeformationMorphism iΛ q x₀ hx₀ a b}
    (hr : f.ringHom = g.ringHom) (ha : f.arrow = g.arrow) : f = g := by
  cases f; cases g; cases hr; cases ha; rfl

/-- The predeformation category `𝓕_{𝓧,k,x₀}` and its canonical functor to `𝒞_Λ`. -/
@[stacks 07T4]
public noncomputable def predeformationCategory :
    PredeformationConstruction iΛ q x₀ hx₀ := by
  let C : Type (max (u + 1) v w) := DeformationObject iΛ q x₀ hx₀
  letI : Category.{max u w} C := {
    Hom := fun a b ↦ DeformationMorphism iΛ q x₀ hx₀ a b
    id := fun a ↦ {
      ringHom := 𝟙 a.algebra
      arrow := 𝟙 a.point
      triangle := by simp
      arrow_base := by simp
    }
    comp := fun {a b c} f g ↦ {
      ringHom := f.ringHom ≫ g.ringHom
      arrow := g.arrow ≫ f.arrow
      triangle := by rw [← Category.assoc, g.triangle, f.triangle]
      arrow_base := by
        rw [show (f.ringHom ≫ g.ringHom).hom.toRingHom =
            g.ringHom.hom.toRingHom.comp f.ringHom.hom.toRingHom from rfl,
          CommRingCat.ofHom_comp, Spec.map_comp, ← g.arrow_base, ← f.arrow_base]
        simp
    }
    id_comp := by intro a b f; apply DeformationMorphism.ext_of_components <;> simp
    comp_id := by intro a b f; apply DeformationMorphism.ext_of_components <;> simp
    assoc := by
      intro a b c d f g h
      apply DeformationMorphism.ext_of_components <;> simp [Category.assoc]
  }
  exact {
    carrier := C
    category := inferInstance
    projection := {
      obj := fun a ↦ a.algebra
      map := fun f ↦ f.ringHom
      map_id := by intro a; rfl
      map_comp := by intro a b c f g; rfl
    }
    objects := Equiv.refl _
    morphisms := fun a b ↦ Equiv.refl _
    object_projection := fun _ ↦ rfl
    morphism_projection := by intro a b f; rfl
    reversed_identity := by intro a; rfl
    reversed_composition := by intro a b c f g; rfl
  }

end

add_to_stacks 07T2 "the construction of the category 𝓕_{𝓧,k,x₀} of deformations of x₀, its \
objects and its reversed morphisms, together with its projection to 𝒞_Λ"
  Deformation.Artin.predeformationCategory

/-! ### Transport of a morphism of deformations along equalities of its endpoints -/

section Transport

open AlgebraicGeometry CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
variable {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
variable {hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Transport a morphism of deformations along equalities of its source and target, by
conjugating its arrows with the induced identifications. -/
public def transportDeformationMorphism
    {a a' b b' : DeformationObject iΛ q x₀ hx₀} (ha : a' = a) (hb : b' = b)
    (m : DeformationMorphism iΛ q x₀ hx₀ a b) :
    DeformationMorphism iΛ q x₀ hx₀ a' b' where
  ringHom := eqToHom (congrArg DeformationObject.algebra ha) ≫ m.ringHom ≫
    eqToHom (congrArg DeformationObject.algebra hb).symm
  arrow := eqToHom (congrArg DeformationObject.point hb) ≫ m.arrow ≫
    eqToHom (congrArg DeformationObject.point ha).symm
  triangle := by
    cases ha
    cases hb
    simpa using m.triangle
  arrow_base := by
    cases ha
    cases hb
    simpa using m.arrow_base

/-- The arrow of `𝒞_Λ` of a transported morphism of deformations is the original one
conjugated by the identifications of the algebras. -/
@[simp]
public theorem transportDeformationMorphism_ringHom
    {a a' b b' : DeformationObject iΛ q x₀ hx₀} (ha : a' = a) (hb : b' = b)
    (m : DeformationMorphism iΛ q x₀ hx₀ a b) :
    (transportDeformationMorphism ha hb m).ringHom =
      eqToHom (congrArg DeformationObject.algebra ha) ≫ m.ringHom ≫
        eqToHom (congrArg DeformationObject.algebra hb).symm := rfl

/-- The reversed arrow of a transported morphism of deformations is the original one
conjugated by the identifications of the deformed objects. -/
@[simp]
public theorem transportDeformationMorphism_arrow
    {a a' b b' : DeformationObject iΛ q x₀ hx₀} (ha : a' = a) (hb : b' = b)
    (m : DeformationMorphism iΛ q x₀ hx₀ a b) :
    (transportDeformationMorphism ha hb m).arrow =
      eqToHom (congrArg DeformationObject.point hb) ≫ m.arrow ≫
        eqToHom (congrArg DeformationObject.point ha).symm := rfl

/-- Transporting back along the reversed equalities returns the original morphism. -/
public theorem transportDeformationMorphism_symm
    {a a' b b' : DeformationObject iΛ q x₀ hx₀} (ha : a' = a) (hb : b' = b)
    (m : DeformationMorphism iΛ q x₀ hx₀ a b) :
    transportDeformationMorphism ha.symm hb.symm
        (transportDeformationMorphism ha hb m) = m := by
  cases ha
  cases hb
  apply DeformationMorphism.ext_of_components <;> simp

/-- A transported morphism of deformations is heterogeneously equal to the original. -/
public theorem transportDeformationMorphism_heq
    {a a' b b' : DeformationObject iΛ q x₀ hx₀} (ha : a' = a) (hb : b' = b)
    (m : DeformationMorphism iΛ q x₀ hx₀ a b) :
    HEq (transportDeformationMorphism ha hb m) m := by
  cases ha
  cases hb
  exact heq_of_eq (DeformationMorphism.ext_of_components iΛ q x₀ hx₀ (by simp) (by simp))

/-- Transport of morphisms of deformations is injective. -/
public theorem transportDeformationMorphism_injective
    {a a' b b' : DeformationObject iΛ q x₀ hx₀} (ha : a' = a) (hb : b' = b)
    {f g : DeformationMorphism iΛ q x₀ hx₀ a b}
    (h : transportDeformationMorphism ha hb f = transportDeformationMorphism ha hb g) :
    f = g := by
  rw [← transportDeformationMorphism_symm ha hb f, ← transportDeformationMorphism_symm ha hb g,
    h]

end Transport

/-! ### Functoriality of predeformation categories -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v₁ v₂ w₁ w₂

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type v₁} [Category.{w₁} X] (qX : X ⥤ Over S)
variable {Y : Type v₂} [Category.{w₂} Y] (qY : Y ⥤ Over S)
variable (F : X ⥤ Y) (hF : F ⋙ qY = qX)
variable (x₀ : X)
variable (hx₀ : qX.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

include hF hx₀ in
/-- The image of the distinguished point lies over the same `Spec k`. -/
public theorem imageBasePoint : qY.obj (F.obj x₀) = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  (congrArg (fun G : X ⥤ Over S ↦ G.obj x₀) hF).trans hx₀

local instance : Category.{max u w₁}
    (predeformationCategory iΛ qX x₀ hx₀).carrier :=
  (predeformationCategory iΛ qX x₀ hx₀).category

local instance : Category.{max u w₂}
    (predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).carrier :=
  (predeformationCategory iΛ qY (F.obj x₀)
    (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).category

/-- The canonical map of predeformation categories, characterized on objects,
reversed arrows, and the common projection to `𝒞_Λ`. -/
public structure InducedPredeformationFunctor where
  /-- The underlying functor between the predeformation categories. -/
  toFunctor :
    (predeformationCategory iΛ qX x₀ hx₀).carrier ⥤
      (predeformationCategory iΛ qY (F.obj x₀)
        (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).carrier
  /-- It commutes with the projections to `𝒞_Λ`. -/
  projection_comm : toFunctor ⋙
      (predeformationCategory iΛ qY (F.obj x₀)
        (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).projection =
      (predeformationCategory iΛ qX x₀ hx₀).projection
  /-- It sends a deformation to the image of its deformed object. -/
  object_point : ∀ a,
    ((predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).objects (toFunctor.obj a)).point =
    F.obj ((predeformationCategory iΛ qX x₀ hx₀).objects a).point
  /-- It sends the arrow of a deformation to the image of that arrow. -/
  object_arrow : ∀ a,
    ((predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).objects (toFunctor.obj a)).arrow =
      F.map ((predeformationCategory iΛ qX x₀ hx₀).objects a).arrow ≫
        eqToHom (object_point a).symm
  /-- It sends a reversed arrow to the image of that reversed arrow. -/
  morphism_arrow : ∀ {a b} (f : a ⟶ b),
    ((predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).morphisms
      (toFunctor.obj a) (toFunctor.obj b) (toFunctor.map f)).arrow =
      eqToHom (object_point b) ≫
        F.map ((predeformationCategory iΛ qX x₀ hx₀).morphisms a b f).arrow ≫
          eqToHom (object_point a).symm

/-- The induced functor viewed directly as a morphism over `𝒞_Λ`. -/
public def InducedPredeformationFunctor.toBasedFunctor
    (G : InducedPredeformationFunctor iΛ qX qY F hF x₀ hx₀) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (predeformationCategory iΛ qX x₀ hx₀).projection)
      (BasedCategory.ofFunctor
        (predeformationCategory iΛ qY (F.obj x₀)
          (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).projection) where
  toFunctor := G.toFunctor
  w := G.projection_comm

/-- A morphism over the base induces a canonical functor of predeformation
categories over `𝒞_Λ`. -/
@[stacks 07WJ]
public def mapPredeformationCategory :
    InducedPredeformationFunctor iΛ qX qY F hF x₀ hx₀ := by
  let Cx := predeformationCategory iΛ qX x₀ hx₀
  let y₀base := imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀
  let Cy := predeformationCategory iΛ qY (F.obj x₀) y₀base
  letI : Category.{max u w₁} Cx.carrier := Cx.category
  letI : Category.{max u w₂} Cy.carrier := Cy.category
  have hobj (x : X) : qY.obj (F.obj x) = qX.obj x := by
    simpa using congrArg (fun G : X ⥤ Over S ↦ G.obj x) hF
  have hmap {x y : X} (f : x ⟶ y) :
      eqToHom (hobj x) ≫ qX.map f ≫ eqToHom (hobj y).symm =
        qY.map (F.map f) := by
    cases hF
    simp [Functor.comp_map]
  let data (a : Cx.carrier) :
      DeformationObject iΛ qY (F.obj x₀) y₀base := by
    let d := Cx.objects a
    refine ⟨d.algebra, F.obj d.point, F.map d.arrow,
      (hobj d.point).trans d.base, ?_⟩
    have hm := congrArg
      (fun g : qY.obj (F.obj x₀) ⟶ qY.obj (F.obj d.point) ↦ g.left)
      (hmap d.arrow)
    rw [← hm]
    simp [Over.comp_left, Over.eqToHom_left, Category.assoc, d.arrow_base]
  let obj (a : Cx.carrier) : Cy.carrier := Cy.objects.symm (data a)
  let objectEq (a : Cx.carrier) : Cy.objects (obj a) = data a :=
    Cy.objects.apply_symm_apply (data a)
  let pointEq (a : Cx.carrier) :
      (Cy.objects (obj a)).point = F.obj (Cx.objects a).point :=
    congrArg DeformationObject.point (objectEq a)
  have objectEq_arrow {A B : DeformationObject
      iΛ qY (F.obj x₀) y₀base} (h : A = B) :
      A.arrow = B.arrow ≫ eqToHom (congrArg DeformationObject.point h).symm := by
    cases h
    simp
  have projectionObjEq (a : Cx.carrier) :
      Cy.projection.obj (obj a) = Cx.projection.obj a := by
    rw [Cy.object_projection, Cx.object_projection, objectEq]
  let morphismData {a b : Cx.carrier} (f : a ⟶ b) :
      DeformationMorphism iΛ qY (F.obj x₀) y₀base
        (Cy.objects (obj a)) (Cy.objects (obj b)) := by
    let da := data a
    let db := data b
    let m := Cx.morphisms a b f
    have hdata : DeformationMorphism iΛ qY (F.obj x₀) y₀base da db := by
      refine ⟨?_, F.map m.arrow, ?_, ?_⟩
      · simpa only [da, db, data] using m.ringHom
      · simpa only [Functor.map_comp] using congrArg F.map m.triangle
      · have hm := congrArg
          (fun g : qY.obj (F.obj (Cx.objects b).point) ⟶
              qY.obj (F.obj (Cx.objects a).point) ↦ g.left)
          (hmap m.arrow)
        rw [← hm]
        simp [Over.comp_left, Over.eqToHom_left, Category.assoc, m.arrow_base]
    exact transportDeformationMorphism (objectEq a) (objectEq b) hdata
  let mapHom {a b : Cx.carrier} (f : a ⟶ b) : obj a ⟶ obj b :=
    (Cy.morphisms (obj a) (obj b)).symm (morphismData f)
  have sourceRingId (a : Cx.carrier) :
      (Cx.morphisms a a (𝟙 a)).ringHom = 𝟙 (Cx.objects a).algebra := by
    simpa using (Cx.morphism_projection (𝟙 a)).symm
  have targetRingId (a : Cx.carrier) :
      (Cy.morphisms (obj a) (obj a) (𝟙 (obj a))).ringHom =
        𝟙 (Cy.objects (obj a)).algebra := by
    simpa using (Cy.morphism_projection (𝟙 (obj a))).symm
  have sourceRingComp {a b c : Cx.carrier} (f : a ⟶ b) (g : b ⟶ c) :
      (Cx.morphisms a c (f ≫ g)).ringHom =
        (Cx.morphisms a b f).ringHom ≫ (Cx.morphisms b c g).ringHom := by
    have h := Cx.morphism_projection (f ≫ g)
    simp only [Functor.map_comp] at h
    rw [← h, ← Cx.morphism_projection f, ← Cx.morphism_projection g]
    simp
  have targetRingComp {a b c : Cx.carrier} (f : obj a ⟶ obj b)
      (g : obj b ⟶ obj c) :
      (Cy.morphisms (obj a) (obj c) (f ≫ g)).ringHom =
        (Cy.morphisms (obj a) (obj b) f).ringHom ≫
          (Cy.morphisms (obj b) (obj c) g).ringHom := by
    have h := Cy.morphism_projection (f ≫ g)
    simp only [Functor.map_comp] at h
    rw [← h, ← Cy.morphism_projection f, ← Cy.morphism_projection g]
    simp
  refine {
    toFunctor := {
      obj := obj
      map := mapHom
      map_id := by
        intro a
        apply (Cy.morphisms (obj a) (obj a)).injective
        apply DeformationMorphism.ext_of_components
        · simp [mapHom, morphismData, sourceRingId, targetRingId, objectEq, data]
        · simp [mapHom, morphismData, Cx.reversed_identity, Cy.reversed_identity, objectEq, data]
      map_comp := by
        intro a b c f g
        apply (Cy.morphisms (obj a) (obj c)).injective
        apply DeformationMorphism.ext_of_components
        · simp [mapHom, morphismData, sourceRingComp, targetRingComp, data]
        · simp [mapHom, morphismData, Cx.reversed_composition, Cy.reversed_composition, data] }
    projection_comm := by
      refine CategoryTheory.Functor.ext projectionObjEq fun a b f ↦ ?_
      have hsMap : Cx.projection.map f =
          eqToHom (Cx.object_projection a) ≫ (Cx.morphisms a b f).ringHom ≫
            eqToHom (Cx.object_projection b).symm := by
        simpa [Category.assoc] using congrArg (fun h ↦ eqToHom (Cx.object_projection a) ≫ h ≫
          eqToHom (Cx.object_projection b).symm) (Cx.morphism_projection f)
      calc
        Cy.projection.map (mapHom f) =
            eqToHom (Cy.object_projection (obj a)) ≫
              (Cy.morphisms (obj a) (obj b) (mapHom f)).ringHom ≫
                eqToHom (Cy.object_projection (obj b)).symm := by
          simpa [Category.assoc] using congrArg
            (fun h ↦ eqToHom (Cy.object_projection (obj a)) ≫ h ≫
              eqToHom (Cy.object_projection (obj b)).symm) (Cy.morphism_projection (mapHom f))
        _ = eqToHom (projectionObjEq a) ≫ Cx.projection.map f ≫
              eqToHom (projectionObjEq b).symm := by
          rw [hsMap]
          simp [mapHom, morphismData, data, Category.assoc, eqToHom_trans]
    object_point := pointEq
    object_arrow a := by simpa [data, pointEq] using objectEq_arrow (objectEq a)
    morphism_arrow := by
      intro a b f
      change (Cy.morphisms (obj a) (obj b)
        ((Cy.morphisms (obj a) (obj b)).symm (morphismData f))).arrow = _
      have hm := (Cy.morphisms (obj a) (obj b)).apply_symm_apply
        (morphismData f)
      rw [congrArg DeformationMorphism.arrow hm]
      simp [morphismData, data]
      rfl }

end

end Deformation.Artin
