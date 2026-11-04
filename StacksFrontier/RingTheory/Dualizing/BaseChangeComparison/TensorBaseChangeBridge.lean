module
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIsoGeneral
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateUnit

/-!
# Stacks 068I as a candidate for the lax monoidal structure map of derived base change

`Dualizing.derivedTensorBaseChange` is the lax monoidal structure map
`μ_{X,Y} : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` of a model `F` of derived extension of scalars along
`f : R → A`.  It is built as a double adjoint transpose through the derived-Hom base-change
morphism of [stacks 0E1X].  `…BaseChangeComparison.TensorBaseChangeStrong` proves `μ` invertible
unconditionally, and what the tags of Chapter 47 listed in
`…BaseChangeComparison.AlgebraActionKFlat` are conditional on is
`Dualizing.TensorComparisonCompatibility`, which invertibility of `μ` does not discharge: by
`Dualizing.tensorComparisonCompatibility_iff_eq_inv` that obligation is a determinate *value* for
`μ`, and `Dualizing.isIso_derivedTensorBaseChange` gives no value.

`…BaseChangeComparison.TensorMateUnit` reduced that obligation to a single equation, with the
morphism of [stacks 0E1X] eliminated: a morphism satisfying
`Dualizing.unit_comp_homEquiv_symm_derivedTensorBaseChange` *is* `μ`
(`Dualizing.eq_derivedTensorBaseChange_of_unit`).  What was missing was a *second*, manifestly
invertible candidate to test against that equation.  This file supplies it.

The monoidality isomorphism of [stacks 068I],
`CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`, is unconditional, but it is
stated for `CochainComplex.DerivedTensor.DerivedTensorProductGeneral` data, not for the
tensor--Hom bundle of [stacks 0A63] that `μ` lives in.
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` of
`…BaseChangeComparison.TensorBifunctorIsoGeneral` bridges exactly that gap, bifunctorially, so
[stacks 068I] can be composed with it on both sides.

## Main results

* `Dualizing.canonicalTensorBaseChangeNatIso` — [stacks 068I] in the vocabulary of
  [stacks 0A63], for a total left derived model `D` of extension of scalars.
* `Dualizing.extensionModelIso` — any model `F` with the total-left-derived universal property
  is isomorphic to `D.functor`, by uniqueness of left derived functors.
* `Dualizing.tensorBaseChangeNatIso` — the same isomorphism of bifunctors at `F`, and
  `Dualizing.tensorBaseChangeMor` its component, invertible by
  `Dualizing.isIso_tensorBaseChangeMor`.
* `Dualizing.isIso_derivedTensorBaseChange_of_unit` — if that component satisfies the unit
  characterization, then `μ` is invertible.  Its conclusion is now unconditional
  (`Dualizing.isIso_derivedTensorBaseChange`); what the hypothesis is worth proving for is the
  identification of the [stacks 068I] morphism with `μ`, as the section "What is not done here"
  below explains.

## What is not done here

The equation is not proved.  Nothing in this file discharges
`Dualizing.KFlatAlgebraActionEq`, `Dualizing.ProjectionFormulaCompatibility` or
`Dualizing.UnitBridgeCompatibility`, and no tag loses its conditional caveat.

The obstruction is not a missing computation of the
**unit** of the adjunction of [stacks 0GMT],
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`, at a localized
complex, complementing the counit lemmas
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app` and
`…_counit_app_eq`.  The unit is pinned, in exactly
the shape of those two counit lemmas, by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app`,
`…_unit_app_eq` and `…_unit_app_eq_of_kFlat` of
`StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction`, and
`…_unit_app_eq_of_model` of `StacksFrontier.Homology.Tor.DerivedChangeOfRingsResolution` drops the
presentation altogether: the unit is pinned at any object admitting a K-flat model.  The
[stacks 0A63] tensor product of two localizations of K-flat complexes has one —
`Dualizing.kFlatDerivedTensorIsoGeneral` presents it as the class of `tensorComplex K L`, which
is K-flat by `CochainComplex.KFlat.tensor`.  So both occurrences
of the unit in `hg` are now computable at exactly the complexes where
`CochainComplex.DerivedTensor.DerivedExtensionScalarsTensorIso.comparison` pins [stacks 068I]
down.  What still separates the two sides of `hg` at such a pair is the isomorphism of
[stacks 0E1W], whose chain-level value asks for a K-flat/K-injective join, and the component of
`Dualizing.extensionModelIso`, for which
`…BaseChangeComparison.ExtensionModelIsoComponent` supplies the defining identity
`Dualizing.extensionModelIso_hom_app_comp_comparison`.

Two things about this file's *conclusion* have to be read before it is worked on again.

Invertibility of `μ` is no longer in question and is no longer what `hg` is worth proving for.
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong` proves `μ`
invertible outright, unconditionally and with `Dualizing.derivedTensorBaseChangeSection` as an
explicit two-sided inverse, so `Dualizing.isIso_derivedTensorBaseChange` is an instance and the
conclusion of `Dualizing.isIso_derivedTensorBaseChange_of_unit` is closed by `inferInstance` with
`hg` discarded.  What `hg` is still worth proving for is the *identification* of the [stacks 068I]
morphism with `μ` — `Dualizing.unit_comp_homEquiv_symm_iff` and
`Dualizing.tensorBaseChangeMor_eq_iff` of
`…BaseChangeComparison.TensorBaseChangeIdentification` — because it would give `μ` a value built
from the chain-level tensor base-change isomorphism
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso` of [stacks 068I].  `μ` is not without
chain-level descriptions: `Dualizing.derivedTensorBaseChange_eq_model` of
`…BaseChangeComparison.TensorBaseChangeModelValue` presents it as a localized chain map, and
`Dualizing.derivedTensorBaseChange_eq_evaluation` of
`…BaseChangeComparison.TensorBaseChangeEvaluation` as a tensoring followed by an evaluation with
no existential at all.  But the first does not say *which* chain map, and the second still carries
the derived-Hom base-change morphism of [stacks 0E1X]; the identification is what would remove
both.

And that identification is not by itself the chapter's keystone.
`Dualizing.KFlatAlgebraActionEq` has a single producer,
`Dualizing.kFlatAlgebraActionEq_of_tensorComparisonCompatibility`, whose only input is
`Dualizing.TensorComparisonCompatibility`; that obligation is phrased with
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` rather than with the [stacks 068I]
morphism, and neither `hg` nor the identification implies it on its own.

What the identification *does* do is reduce the obligation to a single equation in which no
component of [stacks 0E1W] occurs.  It does more than
contribute a chain-level value for the one factor of the obligation that
`…BaseChangeComparison.TensorComparisonFactors` does not treat.  By
`Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` of
`…BaseChangeComparison.TensorComparisonBaseChangeMor`, granted the identification at `(X, A[0])`
the obligation at `X` *is*

`μ' ≫ tensorComparisonOfIso X = 𝟙 ⊗ derivedBaseChangeAlgebraIso`,

and by `Dualizing.tensorBaseChangeMor_eq_iff_tensorComparisonCompatibility`, granted that
equation the obligation *is* the identification.  The two are therefore jointly equivalent to the
obligation, and `Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` assembles them at
the classes of K-flat complexes.

## Implementation notes

The three universe arguments of each declaration here are passed explicitly at every internal
use site.  `D`'s module universe enters the statements only inside `max`, and the level
unifier leaves constraints such as `max (max (uA+1) (uR+1)) (?u+1) =?= max (max (uA+1) (uM+1))
(uR+1)` unsolved rather than taking `?u := uM`; naming the universes avoids the metavariable.
For the same reason `D` is a parameter and not
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, whose two
derived-morphism universes cannot be pinned from inside a definition that mentions `D` twice.
This costs nothing: the chapter's statements quantify over models anyway, and
`Dualizing.extensionModelIso` shows the choice is immaterial.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped MonoidalCategory
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
  (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
    max uR uA uM + 1} f)

/-- **[Stacks 068I] read in the vocabulary of [stacks 0A63], for a total left derived model `D`
of extension of scalars.** -/
noncomputable def canonicalTensorBaseChangeNatIso :
    (D.functor.prod D.functor ⋙
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
          max uR uA uM + 1} A).tensor) ≅
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor ⋙ D.functor) :=
  Functor.isoWhiskerLeft (D.functor.prod D.functor)
      (derivedHomAdjunctionTensorNatIsoGeneral.{uA, max uR uA uM} A).symm ≪≫
    (derivedExtensionScalarsTensorIso.{uR, uA, max uR uA uM} f
      (canonicalDerivedTensorProductGeneral.{uR, max uR uA uM} R)
      (canonicalDerivedTensorProductGeneral.{uA, max uR uA uM} A) D).iso ≪≫
    Functor.isoWhiskerRight
      (derivedHomAdjunctionTensorNatIsoGeneral.{uR, max uR uA uM} R) D.functor

/-- **Any left derived model of extension of scalars is the canonical one.** -/
noncomputable def extensionModelIso : D.functor ≅ F :=
  @Functor.leftDerivedUnique _ _ _ _ _ _ F D.functor _ _
    D.comparison comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))
    inferInstance D.isLeftDerived hF

/-- **[Stacks 068I] read in the vocabulary of [stacks 0A63], at an arbitrary left derived model
`F` of extension of scalars.** -/
noncomputable def tensorBaseChangeNatIso :
    (F.prod F ⋙ (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).tensor) ≅
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor ⋙ F) :=
  Functor.isoWhiskerRight
      (NatIso.prod (extensionModelIso.{uR, uA, uM} f F comparison D)
        (extensionModelIso.{uR, uA, uM} f F comparison D)).symm
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).tensor ≪≫
    canonicalTensorBaseChangeNatIso.{uR, uA, uM} f D ≪≫
    Functor.isoWhiskerLeft
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
        max uR uA uM + 1} R).tensor (extensionModelIso.{uR, uA, uM} f F comparison D)

/-- The candidate lax monoidal structure map supplied by [stacks 068I]. -/
noncomputable abbrev tensorBaseChangeMor
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
          max uR uA uM + 1} A).tensor.obj (F.obj X, F.obj Y) ⟶
      F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
        max uR uA uM + 1} R).tensor.obj (X, Y)) :=
  (tensorBaseChangeNatIso.{uR, uA, uM} f F comparison D).hom.app (X, Y)

/-- The [stacks 068I] candidate is invertible, being a component of an isomorphism. -/
instance isIso_tensorBaseChangeMor
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    IsIso (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) :=
  inferInstanceAs (IsIso ((tensorBaseChangeNatIso.{uR, uA, uM} f F comparison D).hom.app (X, Y)))

/-- **The keystone, reduced to one equation about the [stacks 068I] morphism.** -/
theorem isIso_derivedTensorBaseChange_of_unit
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (hg : (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          (((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
              max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y)
              (F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (X, Y)))).symm
            (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y)) =
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj
                ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app
          (Opposite.op Y, F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR,
            max uR uA uM, max uR uA uM + 1} R).tensor.obj (X, Y)))) :
    IsIso (derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y) := by
  rw [← eq_derivedTensorBaseChange_of_unit.{uR, uA, uM} f F comparison X Y
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) hg]
  infer_instance

end Dualizing

end
