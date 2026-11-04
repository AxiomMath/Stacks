module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# The universal flattening of a quasi-coherent module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be a quasi-coherent `𝒪_X`-module.  The situation of Stacks 0CWX asks, at each scheme `T`
over `Y`, whether the base change `F_T` is flat over `T`, and collects the test schemes where it
is into a functor `F_flat`.  Stacks 0CWR says that the *universal flattening of `F` exists* when
`F_flat` is an algebraic space, and that the *universal flattening of `X` exists* when the
universal flattening of `𝒪_X` does.

## Main definitions

* `AlgebraicGeometry.Space.pointSchemeOver`: the test scheme over an algebraic space determined
  by one of its points over a scheme of the big fppf site.
* `AlgebraicGeometry.Space.FlatnessSituation.IsFlatStableUnderBaseChange`: stability of the
  flatness condition of Stacks 0CWX under morphisms of test schemes.
* `AlgebraicGeometry.Space.FlatnessSituation.flatSubfunctor`: the functor `F_flat` of
  Stacks 0CWX, as the subfunctor of `Y` cut out by flatness of the base-changed module.
* `AlgebraicGeometry.Space.FlatnessSituation.HasUniversalFlattening`: **Stacks 0CWR**, existence
  of the universal flattening of a quasi-coherent module.
* `AlgebraicGeometry.Space.structureSheafFlatnessSituation`: the flatness situation of the
  structure sheaf of the source of a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.HasUniversalFlattening`: **Stacks 0CWR**, existence of the universal
  flattening of an algebraic space over another.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.isFlatStableUnderBaseChange`: the stability
  hypothesis of the subfunctor holds, by Stacks 05VW.

`AlgebraicGeometry.Space.FlatnessSituation.mem_flatSubfunctor_iff` unfolds the sections of the
flatness locus, which the elaborator does not do on its own.

## Implementation notes

"Is an algebraic space" is `AlgebraicGeometry.IsAlgebraicSpace`, a predicate on the presheaves
on the big fppf site of `S`, whereas `F_flat` is displayed on the schemes over `Y`.  The two are
matched in the usual way: a sheaf on the schemes over `Y` is a sheaf on the big fppf site of `S`
together with a map to `Y`, and for a subfunctor of the final object such as `F_flat` that sheaf
is the subfunctor of `Y` whose `T`-points are the maps `T ⟶ Y` along which the base change of
`F` is flat.  `AlgebraicGeometry.Space.pointSchemeOver` turns such a point into the test scheme
at which the flatness condition is stated, by Yoneda.

Flatness of the base change is
`AlgebraicGeometry.Space.FlatnessSituation.IsFlatAfterBaseChange`.  That it is inherited by a
test scheme mapping to another is Stacks 05VW for algebraic spaces, and it is exactly the data
making the flatness condition a subfunctor, so the subfunctor takes it as the hypothesis
`AlgebraicGeometry.Space.FlatnessSituation.IsFlatStableUnderBaseChange` and existence of the
universal flattening quantifies over it existentially.  That hypothesis is *not* an assumption
of the development: it is discharged by
`AlgebraicGeometry.Space.FlatnessSituation.isFlatStableUnderBaseChange`, which is the final
assertion of Stacks 05VW through
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_hom` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctor.lean`, so the existential quantifier
above is satisfiable and the definition says what the source says: that the flatness condition
cuts out a subfunctor of `Y` and that this subfunctor is an algebraic space.  Neither the
hypothesis nor the subfunctor carries a tag, each being a universe-specialised,
hypothesis-carrying form of its statement; the functor `F_flat` itself is
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor` of the same file and is unconditional.

The universal flattening of an algebraic space is *defined* as that of its structure sheaf, so
the second definition is the first at `F = 𝒪_X` rather than a second statement.  The structure
sheaf as an `𝒪_X`-module is the unit object of the modules on the small étale ringed site, over
`AlgebraicGeometry.Space.structureRingSheaf`, and is quasi-coherent by
`SheafOfModules.isQuasicoherentOnSite_unit`.

The scheme-level counterpart is `AlgebraicGeometry.FlatnessSituation.HasUniversalFlattening` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningStratification/Basic.lean`, which is
Stacks 05P6; the names here follow it.

## References

* [Stacks Project, Tag 0CWR](https://stacks.math.columbia.edu/tag/0CWR)
* [Stacks Project, Tag 0CWX](https://stacks.math.columbia.edu/tag/0CWX)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 05P6](https://stacks.math.columbia.edu/tag/05P6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The test scheme over an algebraic space `Y` determined by a point of `Y` over a scheme `T`
of the big fppf site of `S`: the scheme `T`, mapping to `Y` by the morphism of algebraic spaces
to which the point corresponds under Yoneda. -/
def pointSchemeOver (Y : AlgebraicSpaces B S hS) {T : (BigFppfOver B S hS)ᵒᵖ}
    (a : Y.obj.obj T) : SchemesOver Y :=
  CostructuredArrow.mk (ObjectProperty.homMk (yonedaEquiv.symm a))

/-- The morphism of test schemes over `Y` induced by a morphism of schemes of the big fppf site
of `S`, from the restricted point of `Y` to the given one. -/
def pointSchemeOverMap (Y : AlgebraicSpaces B S hS) {T T' : (BigFppfOver B S hS)ᵒᵖ}
    (i : T ⟶ T') (a : Y.obj.obj T) :
    pointSchemeOver Y (Y.obj.map i a) ⟶ pointSchemeOver Y a :=
  CostructuredArrow.homMk i.unop
    (ObjectProperty.hom_ext _ (yonedaEquiv_symm_naturality_left i.unop Y.obj a))

namespace FlatnessSituation

/-- Stability of the flatness condition of Stacks 0CWX under morphisms of test schemes: if the
base change of `F` to a test scheme is flat over it, so is the base change to any test scheme
mapping to it.  This is Stacks 05VW for algebraic spaces, and it holds:
`AlgebraicGeometry.Space.FlatnessSituation.isFlatStableUnderBaseChange`. -/
def IsFlatStableUnderBaseChange (D : FlatnessSituation.{u} B S hS) : Prop :=
  ∀ {T T' : SchemesOver D.Y}, (T' ⟶ T) → D.IsFlatAfterBaseChange T → D.IsFlatAfterBaseChange T'

/-- The flatness condition of Stacks 0CWX is stable under morphisms of test schemes: this is
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_hom`, the final assertion of
Stacks 05VW applied to the cartesian square of a morphism of test schemes. -/
theorem isFlatStableUnderBaseChange (D : FlatnessSituation.{u} B S hS) :
    D.IsFlatStableUnderBaseChange :=
  fun g h => D.isFlatAfterBaseChange_of_hom g h

/-- The functor `F_flat` of Stacks 0CWX, on the big fppf site of `S`: the subfunctor of `Y`
whose points are the maps to `Y` along which the base change of `F` is flat. -/
def flatSubfunctor (D : FlatnessSituation.{u} B S hS) (h : D.IsFlatStableUnderBaseChange) :
    Subfunctor D.Y.obj where
  obj _ := {a | D.IsFlatAfterBaseChange (pointSchemeOver D.Y a)}
  map i a ha := h (pointSchemeOverMap D.Y i a) ha

/-- A point of `Y` is a section of the flatness locus exactly when the base change of `F` to the
test scheme it determines is flat, stated as an equivalence; the elaborator does not unfold the
definition on its own. -/
theorem mem_flatSubfunctor_iff (D : FlatnessSituation.{u} B S hS)
    (h : D.IsFlatStableUnderBaseChange) {T : (BigFppfOver B S hS)ᵒᵖ} (a : D.Y.obj.obj T) :
    a ∈ (D.flatSubfunctor h).obj T ↔ D.IsFlatAfterBaseChange (pointSchemeOver D.Y a) :=
  Iff.rfl

/-- **Stacks 0CWR.** The universal flattening of `F` exists when the flatness condition of
Stacks 0CWX is stable under base change and the functor `F_flat` it cuts out of `Y` is an
algebraic space. -/
@[stacks 0CWR "the universal flattening of a module"]
def HasUniversalFlattening (D : FlatnessSituation.{u} B S hS) : Prop :=
  ∃ h : D.IsFlatStableUnderBaseChange,
    IsAlgebraicSpace B S hS (D.flatSubfunctor h).toFunctor

end FlatnessSituation

/-- The flatness situation of the structure sheaf: a morphism `f : X ⟶ Y` of algebraic spaces
together with the `𝒪_X`-module `𝒪_X`, which is quasi-coherent. -/
def structureSheafFlatnessSituation {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    FlatnessSituation.{u} B S hS where
  X := X
  Y := Y
  f := f
  F := SheafOfModules.unit (structureRingSheaf B S hS X)
  quasicoherent := SheafOfModules.isQuasicoherentOnSite_unit _

/-- **Stacks 0CWR.** The universal flattening of an algebraic space `X` over `Y` exists when the
universal flattening of its structure sheaf `𝒪_X` does. -/
@[stacks 0CWR "the universal flattening of the space"]
def HasUniversalFlattening {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  (structureSheafFlatnessSituation f).HasUniversalFlattening

end AlgebraicGeometry.Space

end
