module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# Group algebraic spaces and their actions

A *group algebraic space* over an algebraic space `B` is an algebraic space over `B` whose
points over every test scheme over `B` form a group, and its morphisms are the morphisms
over `B` preserving those group structures.  Such a group algebraic space *acts* on an
algebraic space `X` over `B` through a morphism `G ×_B X ⟶ X` obeying the unit and
associativity laws, and the action is *free* when the induced action on the points over
every test scheme over `B` is free.

## Main definitions

* `AlgebraicGeometry.Space.GroupAlgebraicSpace` is the category of group algebraic spaces
  over a fixed algebraic space.
* `AlgebraicGeometry.Space.IsFreeAction` is freeness of an action, tested on the points of
  every scheme over the base.
* `AlgebraicGeometry.Space.actionSpace` is the algebraic space `G ×_B X` on which a group
  algebraic space acts, with `AlgebraicGeometry.Space.projection` and
  `AlgebraicGeometry.Space.action` its second projection and its action morphism, and
  `AlgebraicGeometry.Space.actionMap` the morphism `1_G × f` induced by a morphism of
  acted-on objects.

## Main results

The morphisms of `AlgebraicGeometry.Space.GroupAlgebraicSpace` are inherited group-object
morphisms over the base, hence give group homomorphisms on every scheme of points over the
base.

## Implementation notes

An internal group object in the slice category of presheaves over `B` packages
multiplication, identity and inverse on `B`-points together with their naturality.
Requiring its underlying presheaf to be an algebraic space is the definition of a group
algebraic space, and the full subcategory on that condition inherits precisely the
group-object morphisms, so clients may use the existing group-object and slice APIs through
the full-subcategory inclusion without a conversion.

The slice category carries the pullback cartesian monoidal structure, in which the tensor
product is the fibre product over `B`; `AlgebraicGeometry.Space.overCartesianMonoidalCategory`
registers it so that the group-object API applies without a local instance.  Actions and
equivariance are then the existing monoidal-category notions `CategoryTheory.ModObj` and
`CategoryTheory.IsModHom`: the unit and associativity laws of the former are equivalent to
the action laws on all points, and the latter is the commuting square of a natural
transformation with the two action maps, equivalently equivariance on every test scheme.

An action is stated in the slice of presheaves over `B`, where the tensor product is the fibre
product over `B`, while the quasi-coherent sheaves of **Stacks 043T** live on an *algebraic
space*.  `AlgebraicGeometry.Space.actionSpace`, `AlgebraicGeometry.Space.underlyingSpace` and
`AlgebraicGeometry.Space.groupSpace` are the three objects of that slice read as objects of
`AlgebraicGeometry.AlgebraicSpaces`, and `AlgebraicGeometry.Space.asSpaceHom` reads a morphism
over `B` as a morphism of algebraic spaces.  `AlgebraicGeometry.Space.actionAt` and
`AlgebraicGeometry.Space.projectionAt` are the two composites along a test object over the
action space, which is the shape in which the cocycle condition of **Stacks 043T** quantifies
over base changes.  Algebraicity of `G ×_B X` is **Stacks 02X2**, so the fibre product is taken
in `AlgebraicGeometry.AlgebraicSpaces` rather than reproved.

Freeness quantifies over the representable test objects only, as in the source definition.
An object `T` of the big fppf site over `S` together with a morphism from its Yoneda
presheaf to `B` is a scheme over `B`, the hom sets out of it in the slice are the
corresponding `G(T)` and `X(T)`, and `IsCancelSMul` is freeness of the induced action on
them.  All three declarations are abbreviations, so the pointwise APIs are available
without an unfolding lemma.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
* [Stacks Project, Tag 06P8](https://stacks.math.columbia.edu/tag/06P8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Space

/-- The pullback monoidal structure on presheaves over a fixed base.  This instance allows
the group-object API for a group algebraic space to be used directly. -/
noncomputable instance overCartesianMonoidalCategory (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    CartesianMonoidalCategory (Over B) :=
  Over.cartesianMonoidalCategory B

/-- **Stacks Project, Tag 043H.** Group algebraic spaces over an algebraic space `B`.  An
object is a group object in presheaves over `B` whose underlying presheaf is an algebraic
space; morphisms are group-object morphisms over `B`. -/
@[stacks 043H, stacks 06DX "the situation: this notion at the base Spec k for a field k over S"]
noncomputable abbrev GroupAlgebraicSpace (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (_hB : IsAlgebraicSpace 𝒞 S hS B) :=
  (show ObjectProperty (Grp (Over B)) from
    fun G => IsAlgebraicSpace 𝒞 S hS G.X.left).FullSubcategory

add_to_stacks 043Q "part (1): action of a group algebraic space" CategoryTheory.ModObj
add_to_stacks 043Q "part (2): equivariant morphism" CategoryTheory.IsModHom
add_to_stacks 043R "the unit and associativity diagrams of a group action" CategoryTheory.ModObj

/-- **Stacks Project, Tag 06P8.** A group object over `B` acts freely on `X` when its
action is free on the points of every scheme over `B`. -/
@[stacks 06P8]
abbrev IsFreeAction (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (G X : Over B) [GrpObj G] [ModObj G X] : Prop :=
  ∀ (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B),
    IsCancelSMul ((Over.mk b) ⟶ G) ((Over.mk b) ⟶ X)

/-! ### The action space -/

section ActionSpace

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}

/-- The underlying algebraic space of a group algebraic space. -/
abbrev groupSpace (G : GroupAlgebraicSpace 𝒞 S hS B hB) : AlgebraicSpaces 𝒞 S hS :=
  ⟨G.obj.X.left, G.property⟩

/-- An algebraic space over `B`, read as an object of the category of algebraic spaces
over `S`. -/
abbrev underlyingSpace (X : Over B) (hX : IsAlgebraicSpace 𝒞 S hS X.left) :
    AlgebraicSpaces 𝒞 S hS :=
  ⟨X.left, hX⟩

/-- A morphism of algebraic spaces over `B`, read as a morphism of algebraic spaces
over `S`. -/
abbrev asSpaceHom {Y Z : Over B} (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
    (hZ : IsAlgebraicSpace 𝒞 S hS Z.left) (f : Y ⟶ Z) :
    underlyingSpace (hS := hS) Y hY ⟶ underlyingSpace (hS := hS) Z hZ :=
  ObjectProperty.homMk f.left

/-- The algebraic space `G ×_B X` on which a group algebraic space `G` acts, the fibre product
of the two structure morphisms to `B`. -/
noncomputable abbrev actionSpace (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) : AlgebraicSpaces 𝒞 S hS :=
  AlgebraicSpaces.fiberProduct 𝒞 S hS
    (ObjectProperty.homMk G.obj.X.hom : groupSpace G ⟶ ⟨B, hB⟩)
    (ObjectProperty.homMk X.hom : underlyingSpace (hS := hS) X hX ⟶ ⟨B, hB⟩)

/-- The presheaf underlying the action space is the one underlying the fibre product `G ×_B X`
taken in the slice over `B`.

The identification holds by definition, but only after the fibre product of algebraic spaces is
unfolded through the chosen limit cone, which is why it is recorded: it is what makes the type of
`AlgebraicGeometry.Space.actionMap` agree with its ascribed one, and the elaborator does not
perform the unfolding while it is also solving for the objects of a general lemma. -/
theorem actionSpace_obj (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) :
    (actionSpace (hB := hB) G X hX).obj = (G.obj.X ⊗ X).left :=
  rfl

/-- The action space, read as an algebraic space over `S` through the presheaf underlying
`G ×_B X`, is the action space.

This is `AlgebraicGeometry.Space.actionSpace_obj` at the level of objects of
`AlgebraicGeometry.AlgebraicSpaces`; it is the spelling a consumer needs when a test object over
the action space is instantiated at the action space itself. -/
theorem underlyingSpace_actionSpace (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) :
    underlyingSpace (hS := hS) (G.obj.X ⊗ X) (actionSpace (hB := hB) G X hX).property =
      actionSpace (hB := hB) G X hX :=
  rfl

/-- The projection `G ×_B X ⟶ X`. -/
noncomputable abbrev projection (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) :
    actionSpace (hB := hB) G X hX ⟶ underlyingSpace (hS := hS) X hX :=
  ObjectProperty.homMk (snd G.obj.X X).left

/-- The action morphism `G ×_B X ⟶ X`. -/
noncomputable abbrev action (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) :
    actionSpace (hB := hB) G X hX ⟶ underlyingSpace (hS := hS) X hX :=
  letI : ModObj G.obj.X X := A
  ObjectProperty.homMk (ModObj.smul (M := G.obj.X) (X := X)).left

/-- The action morphism read along a test object over the action space. -/
noncomputable abbrev actionAt (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X) :
    underlyingSpace (hS := hS) T hT ⟶ underlyingSpace (hS := hS) X hX :=
  letI : ModObj G.obj.X X := A
  asSpaceHom hT hX (f ≫ ModObj.smul (M := G.obj.X) (X := X))

/-- The projection read along a test object over the action space. -/
noncomputable abbrev projectionAt (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X) :
    underlyingSpace (hS := hS) T hT ⟶ underlyingSpace (hS := hS) X hX :=
  asSpaceHom hT hX (f ≫ snd G.obj.X X)

/-- The morphism `1_G × f : G ×_B X ⟶ G ×_B Y` of action spaces induced by a morphism `f` of
algebraic spaces over `B`. -/
noncomputable abbrev actionMap (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left) (f : X ⟶ Y) :
    actionSpace (hB := hB) G X hX ⟶ actionSpace (hB := hB) G Y hY :=
  asSpaceHom (actionSpace (hB := hB) G X hX).property
    (actionSpace (hB := hB) G Y hY).property
    (lift (fst G.obj.X X) (snd G.obj.X X ≫ f))

end ActionSpace

end AlgebraicGeometry.Space

end
