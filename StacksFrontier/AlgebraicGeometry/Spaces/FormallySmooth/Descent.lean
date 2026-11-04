module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent data for a family of morphisms of algebraic spaces

For a family of algebraic spaces mapping to a common target over a scheme, a descent datum
consists of algebraic spaces over the family members, isomorphisms on pairwise fibre
products, and a cocycle condition on triple fibre products. Its morphisms are compatible
families of maps, and they make the descent data into a category.

## Main definitions

* `AlgebraicGeometry.Space.Descent.structureMap` views the structure morphism of a space
  over `A` as a map of spaces over `T`.
* `AlgebraicGeometry.Space.Descent.DescentData` is a descent datum for a family of
  algebraic-space morphisms, and `AlgebraicGeometry.Space.Descent.DescentData.Hom` is a
  morphism of descent data.

## Main results

* `AlgebraicGeometry.Space.Descent.DescentData.id_hom` and
  `AlgebraicGeometry.Space.Descent.DescentData.comp_hom`: the components of identity and
  composite morphisms of descent data.

## References

* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ T)

/-- The map of spaces over `T` induced by a space over `X i`. -/
public abbrev structureMap {A T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : A ⟶ T)
    (V : Over A) : (Over.map g).obj V ⟶ Over.mk g :=
  Over.homMk V.hom

/-- A descent datum relative to a family of morphisms of algebraic spaces over a scheme. -/
@[stacks 0ADI "part (1), descent data",
  stacks 0ADG "parts (1) and (2): a descent datum relative to one morphism Y → X",
  stacks 0ADJ "the gluing isomorphisms and the cocycle condition in pullback form",
  sga "3 IV 2.1" "descent datum"]
public structure DescentData
    (hT : IsAlgebraicSpace B S hS T)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i)) where
  /-- The algebraic space over each member of the family. -/
  obj (i : ι) : Over (X i)
  /-- Each of those spaces is an algebraic space. -/
  obj_isAlgebraicSpace (i : ι) : IsAlgebraicSpace B S hS (obj i).left
  /-- The gluing isomorphism over `X i ×_T X j`. -/
  gluing (i j : ι) :
    Over.mk (prod.map (structureMap (f i) (obj i)) (𝟙 (Over.mk (f j)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (obj j)))
  /-- The cocycle condition on every triple fibre product. -/
  cocycle (i j k : ι) :
    prod.map (gluing i j).hom.left (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (gluing j k).hom.left =
      prodMapFirstThird (gluing i k).hom.left

namespace DescentData

variable {f} {hT : IsAlgebraicSpace B S hS T}
    {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}

/-- A morphism of descent data is a compatible family of maps over the family members. -/
@[ext,
  stacks 0ADI "part (2), morphisms of descent data",
  stacks 0ADG "parts (1) and (2): a descent datum relative to one morphism Y → X"]
public structure Hom (D E : DescentData f hT hX) where
  /-- The map over each member of the family. -/
  hom (i : ι) : D.obj i ⟶ E.obj i
  /-- Compatibility with the pairwise gluing isomorphisms. -/
  comm (i j : ι) :
    prod.map ((Over.map (f i)).map (hom i)) (𝟙 (Over.mk (f j))) ≫
        (E.gluing i j).hom.left =
      (D.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (hom j))

/-- Descent data form a category, with componentwise identities and composition. -/
public instance : Category (DescentData f hT hX) where
  Hom := Hom
  id D := { hom := fun i ↦ 𝟙 (D.obj i), comm := by intros; simp }
  comp φ ψ :=
    { hom := fun i ↦ φ.hom i ≫ ψ.hom i
      comm := by
        intro i j
        simp only [Functor.map_comp]
        rw [prod.map_comp_id, prod.map_id_comp, Category.assoc, ψ.comm, ← Category.assoc, φ.comm,
          Category.assoc] }
  id_comp _ := Hom.ext <| funext fun _ ↦ Category.id_comp _
  comp_id _ := Hom.ext <| funext fun _ ↦ Category.comp_id _
  assoc _ _ _ := Hom.ext <| funext fun _ ↦ Category.assoc _ _ _

/-- The component of the identity morphism of a descent datum is the identity. -/
@[simp]
public lemma id_hom (D : DescentData f hT hX) (i : ι) :
    (𝟙 D : D ⟶ D).hom i = 𝟙 (D.obj i) := rfl

/-- The component of a composite of morphisms of descent data is the composite of the
components. -/
@[simp]
public lemma comp_hom {D E F : DescentData f hT hX}
    (φ : D ⟶ E) (ψ : E ⟶ F) (i : ι) :
    (φ ≫ ψ).hom i = φ.hom i ≫ ψ.hom i := rfl

end DescentData

end AlgebraicGeometry.Space.Descent

end
