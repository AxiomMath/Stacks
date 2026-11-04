module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonSquare
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.FiniteTorDimension

/-!
# Stacks 0BZM and Stacks 0BZP, conditional only on the projection-formula compatibility

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonSquare` transposes both sides of
the comparison square of Stacks 0E2A and computes each transpose, leaving one equation: a
compatibility between the two projection formulas — one at `R → A`, one at `R' → A ⊗_R R'` — the
lax monoidal structure map of derived base change, the base change of the algebra, and the
restriction/base-change identification of Stacks 0661. That equation mentions neither the
base-change morphism of Stacks 0E29, nor the one of Stacks 0E1X, nor either bridge of
Stacks 0E2A.

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.MateSquare` and
`…BaseChangeComparison.FiniteTorDimension`, on the other hand, state the three cases of
Stacks 0A6A that Stacks 0BZM and Stacks 0BZP need with the *mate square* as their hypothesis —
the square written in terms of the two bridges.

This file joins the two halves, so that the three cases become conditional on the
projection-formula compatibility alone. The join needs no instantiation at a canonical model:
`Dualizing.isIso_derivedHomBaseChange_app_of_comparison` takes the source and target
identifications as arguments, so the two bridges at the *arbitrary* models `Ff` and `Fi` of
derived extension of scalars are admissible identifications, and the equation produced by
`Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility` is already
in the shape that reduction consumes.

The two obligations are equivalent, not merely related: the transposes are taken under the
tensor--Hom adjunction of Stacks 0A63 over `R'`, whose `homEquiv` is a bijection, so the square
holds if and only if the compatibility does. Replacing one by the other therefore weakens
nothing.

## Main definitions

* `Dualizing.ProjectionFormulaCompatibility` — the one remaining obligation, named: the equality
  of the two transposes of the comparison square of Stacks 0E2A.

## Main results

* `Dualizing.projectionFormulaCompatibility_of_algebraActionSquare` — a *sufficient* condition
  for the obligation in which the derived restriction/Hom adjunction of Stacks 0A70 does not
  appear at all: that `Dualizing.restrictionBaseChangeIso` is linear over the algebra.
* `Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_projectionFormulaCompatibility` —
  **Stacks 0BZP**, conditional only on the compatibility.
* `Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_projectionFormulaCompatibility` — the
  **flat case of Stacks 0BZM**, conditional only on the compatibility.
* `isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_projectionFormulaCompatibility` — the
  **finite-Tor-dimension case of Stacks 0BZM**, conditional only on the compatibility.

## Implementation notes

The hypotheses on `A`, on `R'` and on `K` are those of the three source statements, unchanged;
the finite-Tor-dimension case reads Tor amplitude at the module universe that the three rings
force, as `Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_mateSquare` does and
for the reason recorded there.

`Dualizing.projectionFormulaCompatibility_of_algebraActionSquare` is deliberately a one-way
implication and is kept separate from the obligation itself, so that nothing here presents a
strictly stronger hypothesis as if it were the obligation.

No `@[stacks]` attribute is placed here: none of the three statements is yet unconditional, so
none of them covers its tag.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS uT v w

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

/-- **The one remaining obligation of Stacks 0E2A, named.** The equality of the two transposes,
under the tensor--Hom adjunction of Stacks 0A63 over `R'`, of the two sides of the comparison
square of Stacks 0E2A: computed by
`Dualizing.homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso` and by
`Dualizing.homEquiv_sourceIso_comp_derivedHomBaseChange`.

It is a compatibility between the two projection formulas — at `R → A` and at
`R' → A ⊗_R R'` — the lax monoidal structure map `Dualizing.derivedTensorBaseChange` of derived
base change, the base-change identification `Dualizing.derivedBaseChangeAlgebraIso` of the
algebra, the counits of derived extension of scalars, and the restriction/base-change
identification `Dualizing.restrictionBaseChangeIso` of Stacks 0661. Neither the base-change
morphism of Stacks 0E29, nor the one of Stacks 0E1X, nor either bridge of Stacks 0E2A occurs
in it.

The definition is a plain equation, so a proof of it may be given either at this name or at the
equation itself; the two are interchangeable by `rfl`. -/
def ProjectionFormulaCompatibility
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) : Prop :=
  (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).hom) :
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
          baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv.app
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uRp,
              max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
            (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
        ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
              comparisonA isLeftDerivedA).hom.app K ≫
          baseChangeR.map
            ((derivedHomAdjunction.{uR, uA, max v uRp}
              (algebraMap R A)).counit.app K)) =
  (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      (((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
            comparisonA isLeftDerivedA).hom.app K,
          𝟙 (baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
          baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.obj
                ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
            baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
    derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj
          ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
      baseChangeR.map
        ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff
              alphaf).inv.app
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapDerivedCategory.map
            ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR,
                uA, max v uRp} (algebraMap R A) Ff alphaf).counit.app
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
          (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)

/-- **The projection-formula compatibility follows from one square: that the comparison of
Stacks 0661 is linear over the algebra.** Each of the two projection formulas, followed by the
counit of derived extension of scalars, is an action of the algebra: at `R' → A ⊗_R R'` it makes
the restriction of a derived base change a module over `A ⊗_R R'`, and at `R → A` it makes the
restriction of `RHom_R(A, K)` a module over `A`. The hypothesis `hAct` says that
`Dualizing.restrictionBaseChangeIso` carries the first action to the derived base change of the
second, the two being compared through `Dualizing.derivedBaseChangeAlgebraIso` on one side and
the lax monoidal structure map `Dualizing.derivedTensorBaseChange` of derived base change on the
other.

This is *sufficient* for `Dualizing.ProjectionFormulaCompatibility` and not equivalent to it:
the two differ by post-composition with the derived base change of the evaluation counit of
Stacks 0A70, which is not injective. What it buys is that neither the derived
restriction/Hom adjunction of Stacks 0A70 nor its counit occurs in `hAct` — only the two
projection formulas, the two counits of derived extension of scalars, the lax monoidal structure
map, and the two base-change identifications. -/
theorem projectionFormulaCompatibility_of_algebraActionSquare
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hAct :
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                baseChangeA comparisonA isLeftDerivedA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uRp,
                  max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
            (restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
              comparisonA isLeftDerivedA).hom.app K =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
                comparisonA isLeftDerivedA).hom.app K,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj
                    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR,
                    uA, max v uRp} (algebraMap R A) Ff alphaf).counit.app
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K := by
  have reassoc : ∀ {W X Y Z T U : DerivedCategory (ModuleCat.{max v uR uA uRp} R')}
      (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) (e : T ⟶ U),
      a ≫ b ≫ c ≫ (d ≫ e) = (a ≫ b ≫ c ≫ d) ≫ e := by
    intros
    simp only [Category.assoc]
  refine Eq.trans (reassoc _ _ _ _ _) ?_
  refine Eq.trans (congrArg (fun z => z ≫ baseChangeR.map
    ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)) hAct) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)) ?_
  exact congrArg (fun z => _ ≫ _ ≫ z)
    ((baseChangeR.map_comp _ _).symm.trans
      (congrArg baseChangeR.map (Category.assoc _ _ _)))

/-- The morphism of Stacks 0E29 is invertible once the projection-formula compatibility holds and
the base-change morphism at the algebra `A` is invertible. -/
private theorem isIso_app_of_projectionFormulaCompatibility
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K)
    (hβ : IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K)) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_comparison hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA K _ _ _
    (restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility hTor baseChangeR
      comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K
      hProj) hβ

/-- **Stacks 0BZP, conditional only on the projection-formula compatibility.** The morphism of
Stacks 0E29 is invertible when `A` is perfect as an `R`-module, given
`Dualizing.ProjectionFormulaCompatibility`. Compared with
`Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_mateSquare` the hypothesis is the
equality of the two transposes rather than the square itself; the two are equivalent, since the
transposes are taken under a bijection. -/
theorem isIso_derivedHomBaseChange_app_of_isPerfect_of_projectionFormulaCompatibility
    (hA : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_app_of_projectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K hProj
    (isIso_derivedHomBaseChangeAtAlgebra_of_isPerfect baseChangeR comparisonR isLeftDerivedR
      hA K)

/-- **The flat case of Stacks 0BZM, conditional only on the projection-formula compatibility.**
The morphism of Stacks 0E29 is invertible when `R → R'` is flat, `A` is pseudo-coherent as an
`R`-module and `K` is bounded below, given `Dualizing.ProjectionFormulaCompatibility`. -/
theorem isIso_derivedHomBaseChange_app_of_flat_of_projectionFormulaCompatibility
    (hFlat : (algebraMap R R').Flat)
    (hA : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b)
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_app_of_projectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K hProj
    (isIso_derivedHomBaseChangeAtAlgebra_of_flat baseChangeR comparisonR isLeftDerivedR
      hFlat hA K b hK)

/-- **The finite-Tor-dimension case of Stacks 0BZM, conditional only on the projection-formula
compatibility.** The hypotheses on `A`, on `R'` and on `K` are those of Stacks 0BZM: `A`
pseudo-coherent as an `R`-module, `R'` of finite Tor dimension over `R` read off a certified
derived tensor product as in Stacks 0652, the square Tor-independent, and `K` bounded below.
Together with the two statements above this puts all three cases of Stacks 0A6A that Stacks 0BZM
and Stacks 0BZP need on the single obligation
`Dualizing.ProjectionFormulaCompatibility`.

Finite Tor dimension is read at the module universe the three rings force, exactly as in
`Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_mateSquare`, and for the
reason recorded there: Tor amplitude at a smaller module universe is a different, weaker
proposition. -/
theorem isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_projectionFormulaCompatibility
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring.{uR, max v uR uA uRp} R)
    (hFinite : StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension D.tensor D.comparison
      D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR uA, uRp} R'))))
    (hA : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) A)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{max v uR uA uRp} R)).plus K)
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_app_of_projectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K hProj
    (isIso_derivedHomBaseChangeAtAlgebra_of_finiteTorDimension baseChangeR comparisonR
      isLeftDerivedR D hFinite hA K hK.choose hK.choose_spec)

end Dualizing

end
