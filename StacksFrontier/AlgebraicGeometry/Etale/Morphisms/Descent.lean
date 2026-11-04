module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Descending étale morphisms

A descent datum relative to a universal homeomorphism `S' ⟶ S` has an underlying scheme over
`S'`. Restricting to descent data whose underlying scheme is étale gives a forgetful functor to
schemes étale over `S'`. In the other direction, pulling an étale `S`-scheme back along a
morphism `X ⟶ S` gives a descent datum relative to that morphism whose underlying `X`-scheme is
again étale, so the canonical descent functor restricts to étale objects.

## Main definitions

* `AlgebraicGeometry.EtaleOver` is the category of schemes étale over a fixed scheme.
* `AlgebraicGeometry.EtaleDescentData` is the category of descent data relative to a morphism
  whose underlying scheme is étale.
* `AlgebraicGeometry.etaleDescentDataForget` is the forgetful functor between these categories.
* `AlgebraicGeometry.etaleDescentFunctor` is the canonical functor from schemes étale over `S`
  to étale descent data relative to a morphism `X ⟶ S`.

## Main results

* `AlgebraicGeometry.canonicalDescentData_etale` states that the canonical descent datum of an
  étale scheme has an étale underlying scheme.

## Implementation notes

Descent data for the single morphism `S' ⟶ S` are represented by descent data for the
corresponding `Unit`-indexed family. Both the source and the target of the forgetful functor are
full subcategories, so their morphisms are the underlying morphisms of descent data and of
schemes over `S'` respectively.

For the canonical functor the source is Mathlib's category `Scheme.Etale S`, and the functor is
obtained by lifting the composite of the étale forgetful functor with
`AlgebraicGeometry.DescentData.canonicalFunctor`; its underlying object and morphism maps are
therefore canonically the pullback maps, not merely isomorphic choices.

## References

* [Stacks Project, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI)
* [Stacks Project, Tag 0BTZ](https://stacks.math.columbia.edu/tag/0BTZ)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- The property of a scheme over `S` that its structure morphism is étale. -/
abbrev IsEtaleOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ Etale X.hom

/-- The category of schemes étale over `S`. -/
abbrev EtaleOver (S : Scheme.{u}) := (IsEtaleOver S).FullSubcategory

/-- The property that the scheme underlying a descent datum relative to
`S' ⟶ S` is étale over `S'`. -/
abbrev IsEtaleDescentData {S S' : Scheme.{u}} (g : S' ⟶ S) :
    ObjectProperty (DescentData (fun _ : Unit ↦ g)) :=
  fun D ↦ Etale (D.obj ()).hom

/-- The category of descent data relative to `S' ⟶ S` whose underlying scheme
is étale over `S'`. -/
abbrev EtaleDescentData {S S' : Scheme.{u}} (g : S' ⟶ S) :=
  (IsEtaleDescentData g).FullSubcategory

/-- The functor forgetting the descent isomorphism of an étale descent datum relative to
`S' ⟶ S`, retaining its underlying étale scheme over `S'`. -/
@[stacks 0BTZ]
def etaleDescentDataForget {S S' : Scheme.{u}} (g : S' ⟶ S)
    [UniversalHomeomorphism g] : EtaleDescentData g ⥤ EtaleOver S' where
  obj D := ⟨D.obj.obj (), D.property⟩
  map f := ObjectProperty.homMk (f.hom.hom ())
  map_id D := ObjectProperty.hom_ext _ (DescentData.id_hom D.obj ())
  map_comp f h := ObjectProperty.hom_ext _ (DescentData.comp_hom f.hom h.hom ())

variable {S X : Scheme.{u}}

/-- The canonical descent datum of an étale scheme over `S` has an étale underlying scheme
over `X`. -/
@[stacks 0BTI "étale objects"]
theorem canonicalDescentData_etale (f : X ⟶ S) (U : S.Etale) :
    IsEtaleDescentData f
      ((DescentData.canonicalFunctor f).obj ((Scheme.Etale.forget S).obj U)) := by
  let P := DescentData.pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)
  let D := (DescentData.trivialFunctor S).obj ((Scheme.Etale.forget S).obj U)
  show Etale ((P.functor.obj D).obj ()).hom
  have : Etale ((Scheme.Etale.forget S).obj U).hom := U.prop
  have : Etale ((Over.pullback f).obj ((Scheme.Etale.forget S).obj U)).hom := by
    show Etale (pullback.snd ((Scheme.Etale.forget S).obj U).hom f)
    infer_instance
  have : IsIso (P.objIso D).hom.left := by
    show IsIso ((Over.forget X).map (P.objIso D).hom)
    infer_instance
  have hcomm : (P.objIso D).hom.left ≫
      ((Over.pullback f).obj ((Scheme.Etale.forget S).obj U)).hom =
        ((P.functor.obj D).obj ()).hom := (P.objIso D).hom.w
  rw [← hcomm]
  infer_instance

/-- The canonical functor, given by pullback along `f`, from étale `S`-schemes to descent data
relative to `f` with étale underlying `X`-scheme. -/
@[stacks 0BTI "the functor"]
def etaleDescentFunctor (f : X ⟶ S) :
    S.Etale ⥤ EtaleDescentData f :=
  (IsEtaleDescentData f).lift
    ((Scheme.Etale.forget S) ⋙ DescentData.canonicalFunctor f)
    (canonicalDescentData_etale f)

end AlgebraicGeometry

end
