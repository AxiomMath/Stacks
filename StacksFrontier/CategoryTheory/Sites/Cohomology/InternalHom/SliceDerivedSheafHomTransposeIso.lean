module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTranspose
import StacksCore.Tactic.StacksAttribute

/-!
# The mate removed from the localization step: an isomorphism suffices, the 2-cell identity is
not needed

Let `(C, O)` be a ringed site, `U` an object of `C`, and `L`, `M` objects of `D(O)`. The
localization step that the globalization of [Stacks, Tag 0ATP] runs on needs the restriction of
the evaluation morphism

`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M`

to the slice site `C/U` to be an isomorphism, from the affine-local hypothesis that the
evaluation morphism *formed over* `C/U`,

`R𝓗om_{O|_U}(L|_U, M|_U) ⊗^𝐋_{O|_U} L|_U ⟶ M|_U`,

is one. `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit` reduces the
first to invertibility of
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum`, and the module
documentation of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SliceDerivedSheafHomTranspose.lean`
records that getting from the second to that is where the **mate statement** was wanted: that
the comparison [Stacks, Tag 08DL] asserts to be an isomorphism *is* the canonical transpose
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`. That statement is
an identity of 2-cells and is not proved in this development.

**It is not what the step needs.** What the step needs is only that the transpose be *an
isomorphism* — not that it be equal to the comparison of 08DL. This file proves that, and the
input it consumes is available: [Stacks, Tag 08J8] in the form
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`, that the tensor–internal-hom bijection
is tensoring with the identity followed by the evaluation morphism. Read at the transpose, whose
image under the bijection is the datum by definition, that formula says

`datum = (transpose ⊗^𝐋 1) ≫ (evaluation over C/U)`.

Both factors are then isomorphisms under the two hypotheses, and the datum is one.

So the residue of the localization step is strictly smaller than the mate statement: an
invertibility, with no 2-cell identity in it. Whether the transpose is invertible is of course
*implied* by the mate statement, 08DL's comparison being an isomorphism by definition — this
file does not prove either, it separates them.

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.sliceCurryEquiv_eq` — the named bijection is the
  bijection of [Stacks, Tag 08J8] over `C/U` at those three objects, on the nose. This is what
  lets a general fact about the bijection be used in a statement spelled with the named one.
* `SliceDerivedSheafHom.derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose` —
  the image of the transpose under the tensor–internal-hom bijection of [Stacks, Tag 08J8] on the
  slice is the transpose datum. This is the defining equation read forwards.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionDatum_of_isIso_transpose`
  — the transpose datum is invertible when the mate and the evaluation morphism over `C/U` are,
  the bijection eliminated by [Stacks, Tag 08J8].
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit_of_isIso_transpose` —
  **the localization step with the mate statement replaced by an invertibility**: if the
  transpose is an isomorphism and the evaluation morphism over `C/U` is an isomorphism, then the
  restriction to `C/U` of the evaluation morphism over `C` is an isomorphism.

## Implementation notes

No `@[stacks]` attribute is attached. [Stacks, Tag 08DL] is registered on
`Stacks.SheafOfModules.derivedSheafHomRestrictionIso` and its functoriality clauses, and nothing
here adds to that tag: what is proved is a reduction of a *consumer* of the mate statement, not
any part of 08DL. The one tag whose content is used is 08J8, registered where it is proved.

The three objects of the bijection are kept at the names
`Stacks.Cohomology.SliceDerivedSheafHom.sliceCurryEquiv`,
`derivedSheafHomRestrictionTranspose` and `derivedSheafHomRestrictionDatum` rather than written
out, for the elaboration reason recorded in the implementation notes of
`SliceDerivedSheafHomTranspose.lean`: a statement that spells the bijection out and applies it to
the mate exhausts the elaborator's recursion budget, and raising it is not permitted here.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- `Stacks.Cohomology.SliceDerivedSheafHom.sliceCurryEquiv` is the tensor–internal-hom bijection
of [Stacks, Tag 08J8] over `C/U` at the three objects the mate lives between, on the nose.

Stating it is what lets a general fact about `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`
be rewritten into a statement spelled with `sliceCurryEquiv`: the two sides are the same term, but
only the equation between the two *functions* is cheap to check — asking the elaborator to unify
an *application* of one against an application of the other, with the image a metavariable,
exhausts its recursion budget. -/
theorem sliceCurryEquiv_eq :
    sliceCurryEquiv X U L M = @RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ module, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj module).Additive)
      (inferInstance : ∀ first second : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor first second
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
      ((restrictD X U).obj L) ((restrictD X U).obj M) :=
  rfl

/-- **The defining equation of the mate, read forwards.** The tensor–internal-hom bijection of
[Stacks, Tag 08J8] on the slice site carries the mate to the transpose datum: the mate is by
definition the inverse image of the datum, and the bijection is a bijection. -/
theorem derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose :
    derivedSheafHomRestrictionDatum X U L M =
      sliceCurryEquiv X U L M (derivedSheafHomRestrictionTranspose X U L M) :=
  (eq_derivedSheafHomRestrictionTranspose_iff X U L M _).1 rfl

/-- **The transpose datum is invertible as soon as the mate and the slice evaluation are**, with
no 2-cell identity used.

By `derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose` the datum is the image of the
mate under the tensor–internal-hom bijection of [Stacks, Tag 08J8], and by
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply` that image is the mate tensored with the
identity of `L|_U` followed by the evaluation morphism formed over `C/U`. The first factor is
invertible because tensoring is a functor and the mate is, the second by hypothesis.

The intermediate equation — the datum as that composite, with the bijection eliminated — is not
stated as a declaration of its own: writing the composite out in a *statement* at these objects
exhausts the elaborator's recursion budget, exactly as the implementation notes of
`SliceDerivedSheafHomTranspose.lean` record for the bijection itself, and raising the budget is
not permitted here. Inside the proof the composite is never written: it arrives as the
right-hand side of the rewrite. -/
theorem isIso_derivedSheafHomRestrictionDatum_of_isIso_transpose
    (htr : IsIso (derivedSheafHomRestrictionTranspose X U L M))
    (hev : IsIso (@RingedSite.derivedSheafHomCounit (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ module, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj module).Additive)
      (inferInstance : ∀ first second : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor first second
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      ((restrictD X U).obj L)
      ((restrictD X U).obj M))) :
    IsIso (derivedSheafHomRestrictionDatum X U L M) := by
  have := htr
  have := hev
  have computation := @RingedSite.derivedCurryHomEquiv_apply (X.over U)
    (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
    (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
    (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
    (inferInstance : ∀ module, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj module).Additive)
    (inferInstance : ∀ first second : CochainComplex (Modules (X.O.over U)) ℤ,
      HomologicalComplex.HasMapBifunctor first second
        (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
    ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
    ((restrictD X U).obj L) ((restrictD X U).obj M)
    (derivedSheafHomRestrictionTranspose X U L M)
  have curryEquation := DFunLike.congr_fun (sliceCurryEquiv_eq X U L M)
    (derivedSheafHomRestrictionTranspose X U L M)
  refine (congrArg IsIso
    ((derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose X U L M).trans
      (curryEquation.trans computation))).mpr ?_
  infer_instance

/-- **The localization step, with the mate statement replaced by an invertibility.** If the mate
`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)` is an isomorphism and the evaluation morphism formed
over `C/U` is an isomorphism, then the restriction to `C/U` of the evaluation morphism
`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` formed over `C` is an isomorphism.

This is the statement the globalization of [Stacks, Tag 0ATP] consumes, and it does **not** need
the mate statement — that the comparison of [Stacks, Tag 08DL] equals the mate — which is the
2-cell identity missing from this development. Only invertibility of the mate is used, and the
reduction that makes the difference is [Stacks, Tag 08J8]. -/
theorem isIso_map_derivedSheafHomCounit_of_isIso_transpose
    (htr : IsIso (derivedSheafHomRestrictionTranspose X U L M))
    (hev : IsIso (@RingedSite.derivedSheafHomCounit (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ module, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj module).Additive)
      (inferInstance : ∀ first second : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor first second
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      ((restrictD X U).obj L)
      ((restrictD X U).obj M))) :
    IsIso ((restrictD X U).map (RingedSite.derivedSheafHomCounit X L M)) :=
  isIso_map_derivedSheafHomCounit X U L M
    (isIso_derivedSheafHomRestrictionDatum_of_isIso_transpose X U L M htr hev)

end Stacks.Cohomology.SliceDerivedSheafHom

end
