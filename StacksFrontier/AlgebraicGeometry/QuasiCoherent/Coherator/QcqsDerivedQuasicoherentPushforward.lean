module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel

/-!
# The restriction of `Rf_*` to the complexes with quasi-coherent cohomology, for `f` qcqs

`AlgebraicGeometry.derivedQuasicoherentPushforward` is the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of the unbounded derived direct image, and it is built from
part (1) of [Stacks, Tag 08D5] for an *affine* morphism. The same construction runs on the
quasi-compact quasi-separated case of that result, which is
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`, and that
is what this file records: the right edge of the square of [Stacks, Tag 0CRX] for a
quasi-compact quasi-separated morphism with quasi-compact target.

## Main definitions

* `AlgebraicGeometry.qcqsDerivedQuasicoherentPushforward` — `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
  for `f` quasi-compact and quasi-separated with quasi-compact target.

## Main results

* `AlgebraicGeometry.qcqsDerivedQuasicoherentPushforward_eq_derivedQuasicoherentPushforward` — for
  an affine morphism it is `AlgebraicGeometry.derivedQuasicoherentPushforward`.
* `AlgebraicGeometry.qcqsDerivedQuasicoherentPushforwardCompιIso` — composed with the inclusion of
  `D_QCoh(𝒪_Y)` it is the inclusion of `D_QCoh(𝒪_X)` followed by `Rf_*`; this is the defining
  property of the restriction.

## Implementation notes

**No `@[stacks 08D5]` attribute is placed**, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardAnyModel.lean`: the tag has
three parts and the integer `N` of [Stacks, Tag 01XJ], and part (3) is not available, so the
covering set of the tag is incomplete. The functor here is the object the square of
[Stacks, Tag 0CRX] is *about*, not an assertion of that tag either.

The two definitions agree *definitionally* in the affine case: `ObjectProperty.lift` takes the
membership witness as a `Prop`-valued argument, so the two witnesses — the affine case and the
quasi-compact quasi-separated case of part (1) of [Stacks, Tag 08D5] — give the same term.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0CRX](https://stacks.math.columbia.edu/tag/0CRX)
* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived
open AlgebraicGeometry.AnyModel (derivedPushforward derivedPushforwardUnit)

namespace AlgebraicGeometry

universe u

/-- **The restriction of `Rf_*` to the complexes with quasi-coherent cohomology**, for
`f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes with `Y` quasi-compact: the
functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` that the right edge of the square of
[Stacks, Tag 0CRX] is about.

It exists because `Rf_*` carries quasi-coherent cohomology to quasi-coherent cohomology, which is
part (1) of [Stacks, Tag 08D5],
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`. -/
public def qcqsDerivedQuasicoherentPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).lift
    ((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
      derivedPushforward.{u} f)
    (fun E n =>
      AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs f E.1 E.2 n)

/-- **The defining property of the restriction**: forgetting quasi-coherence after
`AlgebraicGeometry.qcqsDerivedQuasicoherentPushforward` gives the inclusion followed by the
unbounded derived direct image. -/
public def qcqsDerivedQuasicoherentPushforwardCompιIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    qcqsDerivedQuasicoherentPushforward f ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ≅
      (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ derivedPushforward.{u} f :=
  ObjectProperty.liftCompιIso _ _ _

/-- **The right edge of the square of [Stacks, Tag 0CRX] under that tag's own hypotheses.** For
`X` and `Y` quasi-compact schemes with affine diagonal and `f : X ⟶ Y` arbitrary, `Rf_*`
restricts to `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

A scheme with affine diagonal is quasi-separated, a morphism out of a quasi-separated scheme is
quasi-separated, and a morphism from a quasi-compact scheme to a quasi-separated one is
quasi-compact; so `f` is quasi-compact and quasi-separated and
`AlgebraicGeometry.qcqsDerivedQuasicoherentPushforward` applies. It is the right edge of the
square of [Stacks, Tag 0CRX],
`AlgebraicGeometry.derivedQuasicoherentComparisonSquareOfAffineDiagonal`. -/
public def affineDiagonalDerivedQuasicoherentPushforward {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (f : X ⟶ Y) :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).FullSubcategory :=
  haveI := quasiSeparatedSpace_of_isAffineHom_diagonal X
  haveI := quasiSeparatedSpace_of_isAffineHom_diagonal Y
  qcqsDerivedQuasicoherentPushforward f

/-- **For an affine morphism the two restrictions of `Rf_*` are the same functor.** Both are the
factorisation of the unbounded derived direct image through the complexes with quasi-coherent
cohomology; they differ only in the witness of part (1) of [Stacks, Tag 08D5] used to build it,
and that witness is a `Prop`. -/
public theorem qcqsDerivedQuasicoherentPushforward_eq_derivedQuasicoherentPushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [CompactSpace Y] :
    qcqsDerivedQuasicoherentPushforward f = derivedQuasicoherentPushforward f :=
  rfl

end AlgebraicGeometry

end
