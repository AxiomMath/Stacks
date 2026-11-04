module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-coherent module as the filtered colimit of its coherent submodules

On a Noetherian scheme the coherent submodules of a quasi-coherent module `F` form a filtered
diagram over `F`, and the cocone whose legs are their inclusions is a colimit cocone. This is
the Noetherian form of the statement that a quasi-coherent module is the directed union of its
finite type quasi-coherent submodules: on a locally Noetherian scheme a submodule is coherent
exactly when it is quasi-coherent and of finite type, so the two diagrams are equivalent.

## Main definitions

* `AlgebraicGeometry.coherentSubobjectProperty` is the property of a subobject of `F` that its
  underlying module is coherent, and `AlgebraicGeometry.CoherentSubobject` the category of such
  subobjects.
* `AlgebraicGeometry.coherentSubobjectFunctor` is the diagram they form, and
  `AlgebraicGeometry.coherentSubobjectCocone` its canonical cocone with point `F`.
* `AlgebraicGeometry.coherentSubobjectEquiv` is the equivalence between the coherent submodules
  of `F` and its finite type quasi-coherent submodules.

## Main results

* `AlgebraicGeometry.isCoherent_subobject_iff`: on a locally Noetherian scheme a submodule is
  coherent exactly when it is quasi-coherent and of finite type.
* `AlgebraicGeometry.coherentSubobject_isFiltered`: the diagram of coherent submodules is
  filtered.
* `AlgebraicGeometry.isColimit_coherentSubobjectCocone`: the canonical cocone is a colimit
  cocone, so `F` is the filtered colimit of its coherent submodules.

## Implementation notes

A submodule is a categorical `Subobject` in `X.Modules`, and the submodules satisfying a
property form the corresponding `ObjectProperty.FullSubcategory`, whose morphisms are the
inclusions. The comparison with the finite type quasi-coherent submodules is an equivalence
rather than an equality of categories, because the two defining properties are pointwise
equivalent but not definitionally equal; the two functors are `ObjectProperty.ιOfLE`, whose
composites with the inclusions into `Subobject F` are the identity, so the colimit statement
transports along the equivalence with no further comparison.

Noetherianness is used twice and in two different ways: locally Noetherian for the equivalence
of the two properties, and quasi-compactness and quasi-separatedness for the colimit statement
about finite type quasi-coherent submodules. Both follow from `IsNoetherian X`, which extends
`CompactSpace` and whose underlying space is Noetherian, hence quasi-separated.

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0GN6](https://stacks.math.columbia.edu/tag/0GN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The property of a subobject of `F` that its underlying module is coherent. -/
def coherentSubobjectProperty {X : Scheme.{u}} (F : X.Modules) :
    ObjectProperty (Subobject F) :=
  fun G => SheafOfModules.IsCoherent (G : X.Modules)

/-- The category of coherent submodules of an `𝒪_X`-module `F`. -/
abbrev CoherentSubobject {X : Scheme.{u}} (F : X.Modules) :=
  (coherentSubobjectProperty F).FullSubcategory

/-- The diagram of all coherent submodules of `F`. -/
noncomputable def coherentSubobjectFunctor {X : Scheme.{u}} (F : X.Modules) :
    CoherentSubobject F ⥤ X.Modules :=
  (coherentSubobjectProperty F).ι ⋙ Subobject.underlying

/-- The canonical cocone from the coherent submodules of `F` to `F`, whose legs are their
inclusions. -/
noncomputable def coherentSubobjectCocone {X : Scheme.{u}} (F : X.Modules) :
    Cocone (coherentSubobjectFunctor F) :=
  Cocone.mk F
    { app := fun G => G.obj.arrow
      naturality := fun {G H} f => by
        exact Subobject.underlying_arrow f.hom }

/-- On a locally Noetherian scheme a submodule of an `𝒪_X`-module is coherent exactly when it
is quasi-coherent and of finite type. -/
lemma isCoherent_subobject_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (G : Subobject F) :
    SheafOfModules.IsCoherent (G : X.Modules) ↔
      SheafOfModules.IsQuasicoherent (G : X.Modules) ∧
        SheafOfModules.IsFiniteType (G : X.Modules) :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X (G : X.Modules)).out 1 2

/-- On a locally Noetherian scheme the coherent submodules of `F` and its finite type
quasi-coherent submodules are the same submodules, hence equivalent categories. -/
noncomputable def coherentSubobjectEquiv {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) :
    CoherentSubobject F ≌ FiniteTypeQuasicoherentSubobject F := by
  have hPQ : coherentSubobjectProperty F ≤ finiteTypeQuasicoherentSubobjectProperty F :=
    fun G hG => (isCoherent_subobject_iff F G).mp hG
  have hQP : finiteTypeQuasicoherentSubobjectProperty F ≤ coherentSubobjectProperty F :=
    fun G hG => (isCoherent_subobject_iff F G).mpr hG
  exact
    { functor := (coherentSubobjectProperty F).ιOfLE hPQ
      inverse := (finiteTypeQuasicoherentSubobjectProperty F).ιOfLE hQP
      unitIso := NatIso.ofComponents
        (fun G => (coherentSubobjectProperty F).isoMk (Iso.refl G.obj)) (by cat_disch)
      counitIso := NatIso.ofComponents
        (fun G => (finiteTypeQuasicoherentSubobjectProperty F).isoMk (Iso.refl G.obj))
        (by cat_disch)
      functor_unitIso_comp := by cat_disch }

/-- **Stacks Project, Tag 0GN6 (directedness).** The coherent submodules of a quasi-coherent
module on a Noetherian scheme form a filtered category. -/
@[stacks 0GN6 "directedness", ega "I 1.5.4" "filtered system"]
instance coherentSubobject_isFiltered {X : Scheme.{u}} (F : X.Modules)
    [IsNoetherian X] [F.IsQuasicoherent] : IsFiltered (CoherentSubobject F) :=
  IsFiltered.of_equivalence (coherentSubobjectEquiv F).symm

/-- **Stacks Project, Tag 0GN6 (colimit).** A quasi-coherent module on a Noetherian scheme is
the filtered colimit of its coherent submodules. -/
@[stacks 0GN6 "colimit", ega "I 1.5.4" "colimit", ega "I 9.4.9" "Noetherian scheme"]
noncomputable def isColimit_coherentSubobjectCocone {X : Scheme.{u}} (F : X.Modules)
    [IsNoetherian X] [F.IsQuasicoherent] :
    IsColimit (coherentSubobjectCocone F) :=
  (isColimit_finiteTypeQuasicoherentSubobjectCocone F).whiskerEquivalence
    (coherentSubobjectEquiv F)

end AlgebraicGeometry

end
