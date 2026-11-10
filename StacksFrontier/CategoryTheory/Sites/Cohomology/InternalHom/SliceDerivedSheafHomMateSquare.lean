module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTranspose
import StacksCore.Tactic.StacksAttribute

/-!
# The mate statement for Stacks 08DL is a square of morphisms

Let `(C, O)` be a ringed site, `U` an object of `C` and `L`, `M` objects of `D(O)`. The *mate
statement* is the assertion that the comparison

`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`

which Stacks 08DL asserts to be an isomorphism is the mate
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose` of the slice tensor
comparison.
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTranspose` reduces
it, by the bijectivity of the tensor–internal-hom bijection of Stacks 08J8 over `C/U`, to the
equation

```
derivedSheafHomRestrictionDatum X U L M =
  sliceCurryEquiv X U L M ((derivedHomRestriction X U).iso L M).hom,
```

in which the bijection still stands. This file removes it. The bijection is `g ↦ (g ⊗ 1) ≫ e`
for `e` the evaluation morphism (`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`), so
the mate statement becomes the commutativity of

```
R𝓗om_O(L, M)|_U ⊗^𝐋_{O|_U} L|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U) ⊗^𝐋_{O|_U} L|_U ⟶ M|_U
            ‖                                                             ‖
    (R𝓗om_O(L, M) ⊗^𝐋_O L)|_U -------------------------------------→   M|_U
```

— bottom row the restriction to `C/U` of the evaluation morphism formed over `C`, top row the
comparison of Stacks 08DL tensored with `L|_U` followed by the evaluation morphism formed over
`C/U`, left edge the slice tensor comparison
`Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso`. That is the 2-cell
identity the mate statement amounts to, with no bijection and no transpose left in it.

**The square is not proved here, and nothing below assumes it.** What is proved is that it *is*
the mate statement.

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum_eq_iff`: the transpose
  datum is the transpose of a morphism `g` exactly when that square commutes with `g` along its
  top row.
* `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose_eq_iso_iff_square`:
  **the mate statement is that square**, with `g` the comparison of Stacks 08DL.

## Implementation notes

The formula for the bijection is used at the slice site `C/U` and at the restrictions of three
objects of `D(O)`. It is not provable at those arguments; the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedCurryingCounitFormula.lean`
record which steps fail and why, and that file states it over a variable ringed site for exactly
this consumer. Here it is only instantiated, and the instantiation is reached by `rw`, which
matches through the reducible abbreviation
`Stacks.Cohomology.SliceDerivedSheafHom.sliceCurryEquiv`.

**Why the slice instances are assumed at two spellings.** Each variable block below assumes the
sheafification, local-bijectivity, additivity and bifunctor-map hypotheses over the slice site
twice, once as `X.J.over U` and `X.O.over U` and once as `(X.over U).J` and `(X.over U).O`. The
fields of `AlgebraicGeometry.RingedSite.over` *are* those terms, so the two spellings are equal
by `rfl` and the duplicates assume nothing new; but `over` is only `implicit_reducible`, so
instance search does not unfold its projections, and the statements below demand both spellings.
The results imported from
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTranspose` —
`restrictD`, `sliceTensorRestrictionObjIso`, `derivedSheafHomRestrictionDatum`,
`sliceCurryEquiv` — carry their slice instances at `X.J.over U`, while the applications of
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`,
`Stacks.SheafOfModules.derivedTensorProductFunctor` and
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit` to the ringed site `X.over U` demand them at
`(X.over U).J`. With either spelling alone the demand at the other one is met by no local
hypothesis, and the search for it exhausts the synthesis budget.

**Why the mate statement is still open, and what it is not open for.** It is not the
naturality of Stacks 08JA, nor with it that of Stacks 08DI: both are proved, as
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality` and
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality`, and this file is a consumer of
them. Nor is it the identification of Stacks 08JA **over an object of the site**, which is needed
because the comparison of Stacks 08DL is pinned down only on K-injective representatives, by
`AlgebraicGeometry.RingedSite.derivedHomRestriction_model`, and the square has to be checked
there — which means reading both rows on sections over `U` rather than on global sections.
Stacks 08JA over an object is
natural in both variables,
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_naturality`, and does agree on a
K-flat and a K-injective complex with the identification built from them,
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_eq_ofKFlat`; both are in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOverAnObjectNaturality`.

What is absent is the square itself. With the identification over `U` in hand the remaining work
is to read `derivedHomRestriction_model` against it and against the restriction of the evaluation
morphism of Stacks 08J8, at the chosen K-injective representatives, and to check that the two
agree; nothing below does that, and nothing below assumes it.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard

section Slice

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor X.O).Additive]
  [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive]
  [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]
  [(X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor (X.over U).O).Additive]
  [∀ M, ((sheafTensor (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.over U).O) (ComplexShape.up ℤ)]
  (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The transpose datum, as a square.** A morphism

`g : R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`

has `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum` for its transpose
under the tensor–internal-hom bijection of Stacks 08J8 over `C/U` exactly when the restriction to
`C/U` of the evaluation morphism `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` formed over `C` factors as the slice
tensor comparison, then `g` tensored with `L|_U`, then the evaluation morphism formed over
`C/U`. -/
theorem derivedSheafHomRestrictionDatum_eq_iff
    (g : (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
        (op ((restrictD X U).obj L))).obj ((restrictD X U).obj M)) :
    derivedSheafHomRestrictionDatum X U L M = sliceCurryEquiv X U L M g ↔
      (restrictD X U).map (RingedSite.derivedSheafHomCounit X L M) =
        (sliceTensorRestrictionObjIso X U
              (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) L).hom ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map g).app
              ((restrictD X U).obj L) ≫
            RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
              ((restrictD X U).obj M) := by
  rw [RingedSite.derivedCurryHomEquiv_apply, map_derivedSheafHomCounit_eq]
  exact (Iso.cancel_iso_hom_left _ _ _).symm

end Slice

section MateStatement

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor X.O).Additive]
  [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive]
  [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]
  [(X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor (X.over U).O).Additive]
  [∀ M, ((sheafTensor (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.over U).O) (ComplexShape.up ℤ)]
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The mate statement for Stacks 08DL is a square of morphisms.** The comparison

`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`

of Stacks 08DL is the mate
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose` of the slice tensor
comparison if and only if the restriction to `C/U` of the evaluation morphism
`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` of Stacks 08J8 factors as the slice tensor comparison, followed by
that comparison tensored with `L|_U`, followed by the evaluation morphism formed over `C/U`.

This is
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose_eq_iso_iff` with the
tensor–internal-hom bijection of Stacks 08J8 eliminated from the right-hand side: the same
assertion, with nothing in it but constructed morphisms of `D(O|_U)` and composition. Neither side
is
proved — the square is exactly the 2-cell identity missing from this development, and nothing
here asserts it. -/
theorem derivedSheafHomRestrictionTranspose_eq_iso_iff_square :
    ((RingedSite.derivedHomRestriction X U).iso L M).hom =
        derivedSheafHomRestrictionTranspose X U L M ↔
      (restrictD X U).map (RingedSite.derivedSheafHomCounit X L M) =
        (sliceTensorRestrictionObjIso X U
              (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) L).hom ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
                ((RingedSite.derivedHomRestriction X U).iso L M).hom).app
              ((restrictD X U).obj L) ≫
            RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
              ((restrictD X U).obj M) :=
  (derivedSheafHomRestrictionTranspose_eq_iso_iff X U L M).trans
    (derivedSheafHomRestrictionDatum_eq_iff X U L M _)

end MateStatement

end Stacks.Cohomology.SliceDerivedSheafHom

end
