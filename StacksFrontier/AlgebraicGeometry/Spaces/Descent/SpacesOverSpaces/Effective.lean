module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.FamilyPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.HomDescent

/-!
# Effective descent data for algebraic spaces

An algebraic space over the target of a morphism, or of a family of morphisms, carries a
canonical descent datum: pull back the trivial descent datum of the identity. A descent datum
is *effective* when it is isomorphic to one of these canonical data.

## Main definitions

* `AlgebraicGeometry.Space.Descent.AlgebraicSpacesOver` is the category of algebraic spaces
  over a fixed algebraic space.
* `AlgebraicGeometry.Space.Descent.trivialDescentFunctor` assigns to an algebraic space over
  `X` its trivial descent datum for the identity of `X`.
* `AlgebraicGeometry.Space.Descent.canonicalDescentFunctor` and
  `AlgebraicGeometry.Space.Descent.familyCanonicalDescentFunctor` pull those data back along a
  morphism, respectively along a family of morphisms.
* `AlgebraicGeometry.Space.Descent.HomDescentData.IsEffective` and
  `AlgebraicGeometry.Space.Descent.DescentData.IsEffective` express effectivity.

## Implementation notes

The one-member family is indexed by `PUnit`. For the identity morphism the gluing isomorphism
is the symmetry of `U ×_X X` and `X ×_X U`, which is the identity on `U` under the canonical
identifications. Effectivity is membership in the essential image, so it records both an
algebraic space over the target and an isomorphism of descent data.

## References

* [Stacks Project, Tag 0ADQ](https://stacks.math.columbia.edu/tag/0ADQ)
* [Stacks Project, Tag 0ADR](https://stacks.math.columbia.edu/tag/0ADR)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Algebraic spaces over `X`, as a full subcategory of the spaces over `X`. -/
public abbrev AlgebraicSpacesOver (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ObjectProperty.FullSubcategory (fun U : Over X ↦ IsAlgebraicSpace B S hS U.left)

/-- An algebraic space over `X` carries its trivial descent datum for the identity of `X`. -/
@[stacks 0ADQ "part (1), trivial descent datum", implicit_reducible]
public def trivialDescentFunctor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X ⥤
      HomDescentData.{u, v} (𝟙 X) hX hX where
  obj U :=
    { obj := fun _ ↦ U.obj
      obj_isAlgebraicSpace := fun _ ↦ U.property
      gluing := fun _ _ ↦ Over.isoMk (prod.braiding _ _) (by
        apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext)
      cocycle := by
        intros
        apply prod.hom_ext
        · apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext
        · simp [prodMapLastTwo, prodMapFirstThird] }
  map g :=
    { hom := fun _ ↦ g.hom
      comm := by intros; simp }

/-- Pulling the trivial descent datum back along a morphism gives the canonical descent
datum of an algebraic space over the target. -/
@[stacks 0ADQ "part (2), canonical descent datum", implicit_reducible]
public def canonicalDescentFunctor {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X ⥤ HomDescentData.{u, v} f hX hY :=
  trivialDescentFunctor.{u, v} X hX ⋙
    (pullbackDescentDataFunctor.{u, v, v} (𝟙 X) f (𝟙 X) f (by simp) hX hX hX hY).val

/-- A descent datum for one morphism is effective if it is isomorphic to the canonical descent
datum of an algebraic space over the target. -/
@[stacks 0ADQ "part (3), effectivity"]
public abbrev HomDescentData.IsEffective {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    (D : HomDescentData.{u, v} f hX hY) : Prop :=
  (canonicalDescentFunctor.{u, v} f hX hY).essImage D

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pulling the trivial descent datum over `T` back to each member of a family gives the
canonical descent datum of an algebraic space over `T`. -/
@[stacks 0ADR "part (1), canonical descent datum", implicit_reducible]
public def familyCanonicalDescentFunctor (f : ∀ i, X i ⟶ T)
    (hT : IsAlgebraicSpace B S hS T) (hX : ∀ i, IsAlgebraicSpace B S hS (X i)) :
    AlgebraicSpacesOver (B := B) (S := S) (hS := hS) T ⥤ DescentData f hT hX :=
  trivialDescentFunctor.{u, v} T hT ⋙
    (pullbackFunctor (fun _ : PUnit.{v + 1} ↦ 𝟙 T) f hT (fun _ ↦ hT) hT hX
      (fun _ ↦ PUnit.unit) (𝟙 T) f (by simp)).functor

/-- A descent datum for a family is effective if it is isomorphic to the canonical descent
datum of an algebraic space over the target. -/
@[stacks 0ADR "part (2), effectivity"]
public abbrev DescentData.IsEffective {f : ∀ i, X i ⟶ T} {hT : IsAlgebraicSpace B S hS T}
    {hX : ∀ i, IsAlgebraicSpace B S hS (X i)} (D : DescentData f hT hX) : Prop :=
  (familyCanonicalDescentFunctor f hT hX).essImage D

end AlgebraicGeometry.Space.Descent

end
