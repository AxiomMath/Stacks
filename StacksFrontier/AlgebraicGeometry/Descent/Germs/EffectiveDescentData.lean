module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare

/-!
# Effective descent data for schemes

For a morphism of schemes `f : X ⟶ S`, a scheme over `S` carries a trivial descent datum
relative to the identity of `S`. Pulling that datum back along `f` gives the canonical descent
datum of the scheme relative to `f`. A descent datum is effective when it is isomorphic to one
obtained in this way.

## Main definitions

* `AlgebraicGeometry.DescentData.trivialFunctor` sends an `S`-scheme to its trivial descent
  datum.
* `AlgebraicGeometry.DescentData.canonicalFunctor` sends an `S`-scheme to its canonical descent
  datum relative to a morphism `X ⟶ S`.
* `AlgebraicGeometry.DescentData.IsEffective` says that a descent datum is isomorphic to a
  canonical one.

## Implementation notes

A descent datum for a single morphism is a `Unit`-indexed `AlgebraicGeometry.DescentData`. For
the identity morphism the gluing map is the symmetry between `U ×_S S` and `S ×_S U`; after the
canonical identifications with `U` this is the identity morphism in the source. The canonical
datum functor is the composite of the trivial-datum functor with the pullback functor of a
commutative square. Effectivity is membership in its essential image, retaining both the
descended scheme and the isomorphism of descent data. Both functors are `implicit_reducible` so
their inherited object and morphism APIs remain available to clients.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

/-- The functor sending a scheme over `S` to its trivial descent datum relative to the
singleton family consisting of `𝟙 S`. -/
@[stacks 023Z "part (1)", implicit_reducible]
def trivialFunctor (S : Scheme.{u}) :
    Over S ⥤ DescentData (S := S) (X := fun _ : Unit ↦ S) (fun _ ↦ 𝟙 S) where
  obj U :=
    { obj := fun _ ↦ U
      gluing := fun _ _ ↦ Over.isoMk (prod.braiding _ _) (by
        apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext)
      cocycle := by
        intros
        apply prod.hom_ext
        · apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext
        · simp [prodMapLastTwo, prodMapFirstThird] }
  map g :=
    { hom := fun _ ↦ g
      comm := by intros; simp }
  map_id U := by ext; simp
  map_comp g h := by ext; simp

/-- The functor sending a scheme over `S` to its canonical descent datum relative to
`f : X ⟶ S`, obtained by pulling back its trivial descent datum. -/
@[stacks 023Z "part (2)", implicit_reducible]
def canonicalFunctor {S X : Scheme.{u}} (f : X ⟶ S) :
    Over S ⥤ DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f) :=
  trivialFunctor S ⋙ (pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).functor

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- A descent datum relative to `f : X ⟶ S` is effective if it is isomorphic to the
canonical descent datum of a scheme over `S`. -/
@[stacks 023Z "part (3)", sga "3 IV 3.5.1"]
abbrev IsEffective
    (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)) : Prop :=
  (canonicalFunctor f).essImage D

end AlgebraicGeometry.DescentData
