module

public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.Groupoid.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Prorepresentable groupoids in functors

Prorepresentability for a groupoid in functors on the base category.

## Main definitions

* `artinianToComplete` regards an Artinian local algebra as a complete
  local algebra.
* `GroupoidInFunctors.restrict` restricts a groupoid in functors along
  a functor.
* `IsProrepresentable` is the predicate that a groupoid in functors on
  Artinian local algebras is the restriction of a representable one on complete
  local algebras.

## Implementation notes

The canonical inclusion of Artinian local algebras into complete local algebras
is `artinianToComplete`. Restriction of all the groupoid data is
implemented by composition with this inclusion, retaining an independent
universe for the values of the functors.
The categorical isomorphism in `IsProrepresentable` preserves the object and
arrow functors and all the groupoid operations through the category structure
of `GroupoidInFunctors`.

## References

* [Stacks Project, Tag 06KD](https://stacks.math.columbia.edu/tag/06KD)
-/

@[expose] public section

namespace Deformation

/-! ### Prorepresentable groupoids in functors -/

section
open CategoryTheory IsLocalRing
universe u v w x y z


/-- The canonical inclusion of Artinian local algebras among complete local algebras. -/
@[implicit_reducible]
public def artinianToComplete {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] :
    ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ CompleteLocalAlgCat.{u, v, w} Λ k where
  obj A :=
    { carrier := A
      completeLocal :=
        { isNoetherian := inferInstance
          isLocal := inferInstance
          isComplete := inferInstance }
      residueEquiv := A.residueEquiv }
  map f :=
    { hom := f.hom
      isLocal := f.isLocal
      residue_comm := f.residue_comm }
  map_id _ := rfl
  map_comp _ _ := rfl

namespace GroupoidInFunctors

/-- Restriction of a groupoid in functors along a functor of source categories. The restriction
`(U, R, s, t, c)|_{C'}` of a groupoid in functors to a subcategory `C' ⊆ C` is the case where the
functor is the inclusion of `C'`. -/
@[stacks 06K9, implicit_reducible]
public def restrict {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    (G : GroupoidInFunctors.{v, x, y} D) (F : C ⥤ D) :
    GroupoidInFunctors.{u, w, y} C where
  objects := F ⋙ G.objects
  arrows := F ⋙ G.arrows
  source := {
    app := fun X ↦ G.source.app (F.obj X)
    naturality := by
      intro X Y f
      exact G.source.naturality (F.map f) }
  target := {
    app := fun X ↦ G.target.app (F.obj X)
    naturality := by
      intro X Y f
      exact G.target.naturality (F.map f) }
  comp := {
    app := fun X ↦ G.comp.app (F.obj X)
    naturality := by
      intro X Y f
      exact G.comp.naturality (F.map f) }
  pointwiseGroupoid T := G.pointwiseGroupoid (F.obj T)

end GroupoidInFunctors

/-- A groupoid in functors on Artinian local `Λ`-algebras is prorepresentable
if it is isomorphic to the restriction of a representable groupoid in functors
on Noetherian complete local `Λ`-algebras. -/
@[stacks 06KD, sga "7 VI 2.13" "prorepresentable"]
public abbrev GroupoidInFunctors.IsProrepresentable {Λ : Type u} {k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, v, max v z}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) : Prop :=
  ∃ H : GroupoidInFunctors.{_, v, max v z}
      (CompleteLocalAlgCat.{u, v, w} Λ k),
    IsRepresentable H ∧
      Nonempty (G ≅ GroupoidInFunctors.restrict H
        artinianToComplete)

end

end Deformation
