module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import StacksFrontier.Topology.Algebra.RingColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally topologically ringed spaces

A *locally topologically ringed space* is a topological space equipped with a sheaf of
topological rings whose stalks, after forgetting the topologies, are local rings; a morphism is
a pair `(f, f^♯)` with `f^♯` continuous on sections and a local homomorphism on stalks. This is
the category denoted `LTRS` in the discussion of formal schemes à la EGA of [Stacks, Tag 0AHY].

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`, with the abbreviation
  `AlgebraicGeometry.LTRS`: the objects of the category `LTRS`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.Hom`: the morphisms, together with the
  `CategoryTheory.Category` instance they assemble into.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.forgetToSheafedSpace` and
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace.forgetToTop`: the forgetful functors to
  sheaves of topological rings and to topological spaces.

## Implementation notes

The definition mirrors `AlgebraicGeometry.LocallyRingedSpace`: a `SheafedSpace TopCommRingCat`
together with locality of the stalks. It is not a full subcategory of
`AlgebraicGeometry.SheafedSpace`, because morphisms are required to be local on stalks. A single
universe `u` is used for the underlying space and the rings of sections.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCommRingCat

/-- An isomorphism of topological commutative rings is a local homomorphism of the underlying
rings: a unit in the target pulls back to a unit. -/
theorem isLocalHom_val_of_isIso {R S : TopCommRingCat.{u}} (φ : R ⟶ S) [IsIso φ] :
    IsLocalHom φ.1 := by
  have e : ((inv φ).1).comp φ.1 = RingHom.id R.α :=
    congrArg (fun m : R ⟶ R => m.1) (IsIso.hom_inv_id φ)
  have h : IsLocalHom (((inv φ).1).comp φ.1) := by rw [e]; exact isLocalHom_id R.α
  exact isLocalHom_of_comp φ.1 (inv φ).1

end TopCommRingCat

namespace AlgebraicGeometry

/-- A *locally topologically ringed space* is a topological space `X` together with a sheaf
`𝒪_X` of topological rings whose stalks are local rings when one forgets the topology. -/
structure LocallyTopologicallyRingedSpace extends SheafedSpace TopCommRingCat.{u} where
  /-- Forgetting the topologies, the stalks of a locally topologically ringed space are local
  rings. -/
  isLocalRing : ∀ x, IsLocalRing (presheaf.stalk x).α

/-- `LTRS` is notation for the type of locally topologically ringed spaces. -/
abbrev LTRS := LocallyTopologicallyRingedSpace

namespace LocallyTopologicallyRingedSpace

attribute [instance] isLocalRing

/-- A locally topologically ringed space is coerced to the type of points of its underlying
space. -/
instance : CoeSort LTRS.{u} (Type u) :=
  ⟨fun X => (X.carrier : Type u)⟩

/-- A morphism of locally topologically ringed spaces is a pair `(f, f^♯)` consisting of a
continuous map `f` and an `f`-map `f^♯` of sheaves of topological rings — so `f^♯` is continuous
on sections, that being part of the data of a morphism of `TopCommRingCat` — which is in
addition a local homomorphism on each stalk. -/
@[ext, ega "I 10.4.5" "more general", sga "3 VIIB 1.1" "more general"]
structure Hom (X Y : LTRS.{u}) : Type u
    extends X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  /-- The map induced on stalks is a local homomorphism of local rings. -/
  isLocalHom : ∀ x, IsLocalHom (toHom.stalkMap x).1

/-- Morphisms of locally topologically ringed spaces as the arrows of a quiver. -/
instance : Quiver LTRS.{u} := ⟨Hom⟩

/-- Two morphisms of locally topologically ringed spaces agree as soon as their underlying
morphisms of presheafed spaces do, the locality of the stalk maps being a proposition. -/
@[ext]
theorem Hom.ext' {X Y : LTRS.{u}} {f g : X ⟶ Y} (h : f.toHom = g.toHom) : f = g := by
  cases f; cases g; congr

/-- The stalk map of a morphism of locally topologically ringed spaces is a local
homomorphism. -/
instance (X Y : LTRS.{u}) (f : X ⟶ Y) (x : X) : IsLocalHom (f.toHom.stalkMap x).1 :=
  f.isLocalHom x

/-- The identity morphism of a locally topologically ringed space. -/
def id (X : LTRS.{u}) : X ⟶ X where
  toHom := 𝟙 X.toPresheafedSpace
  isLocalHom x := by
    rw [show (𝟙 X.toPresheafedSpace : X.toPresheafedSpace ⟶ _).stalkMap x = 𝟙 _ from
      PresheafedSpace.stalkMap.id X.toPresheafedSpace x]
    exact isLocalHom_id _

/-- Composition of morphisms of locally topologically ringed spaces, which is the composition of
the underlying morphisms of presheafed spaces. -/
def comp {X Y Z : LTRS.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z where
  toHom := (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
  isLocalHom x := by
    have hf : IsLocalHom (f.toHom.stalkMap x).1 := f.isLocalHom x
    have hg : IsLocalHom (g.toHom.stalkMap (f.toHom.base x)).1 := g.isLocalHom _
    rw [PresheafedSpace.stalkMap.comp]
    exact RingHom.isLocalHom_comp (f.toHom.stalkMap x).1 (g.toHom.stalkMap _).1

/-- The category `LTRS` of locally topologically ringed spaces. -/
instance : Category LTRS.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g

/-- The underlying morphism of presheafed spaces of an identity morphism is the identity. -/
@[simp]
theorem id_toHom (X : LTRS.{u}) : Hom.toHom (𝟙 X) = 𝟙 X.toPresheafedSpace := rfl

/-- The underlying morphism of presheafed spaces of a composite is the composite of the
underlying morphisms. -/
@[simp]
theorem comp_toHom {X Y Z : LTRS.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace) := rfl

/-- The forgetful functor from `LTRS` to sheaves of topological rings on a space. -/
@[simps]
def forgetToSheafedSpace : LTRS.{u} ⥤ SheafedSpace TopCommRingCat.{u} where
  obj X := X.toSheafedSpace
  map f := InducedCategory.homMk f.toHom

/-- The forgetful functor from `LTRS` to topological spaces. -/
@[simps!]
def forgetToTop : LTRS.{u} ⥤ TopCat.{u} :=
  forgetToSheafedSpace ⋙ SheafedSpace.forget _

end LocallyTopologicallyRingedSpace

end AlgebraicGeometry
