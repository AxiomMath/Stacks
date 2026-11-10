module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.SquareCounitConjugate

/-!
# Assembling the left-hand side of the tensor-comparison obligation

`Dualizing.tensorComparisonCompatibility_of_homEquiv_square` reduces
`Dualizing.TensorComparisonCompatibility` at `X` to an equation whose left-hand side is

`pf.inv X ≫ homEquiv_{R → R'} (homEquiv_{R' → A ⊗_R R'} (conj) ≫ pf'.hom (baseChangeR X))`,

with `conj = γ.inv ((Ff X)|_R) ≫ baseChangeA (ε_{Ff X}) ≫ γ.hom X` the square isomorphism
conjugating the counit of derived extension of scalars along `R → A`.  At `X = Q K` with `K`
K-flat over `R`, `Dualizing.squareIso_counit_conjugate_comp_comparison_app_q_obj` pins `conj`
*composed with* the composite comparison along `R → R' → A ⊗_R R'` at `K`, and that comparison is
invertible at a K-flat `K` by `Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat`.  This file
divides by it and carries the result through the two transposes.

What comes out is the left-hand side with **neither the square isomorphism nor the counit of
[stacks 0GMT] along `R → A` occurring at all**.  Its factors are: the inverse projection formula
over `R` followed by the explicit isomorphism `(Ff (Q K))|_R ≅ Q ((A ⊗_R K)|_R)`; the transpose
over [stacks 0GMT] along `R' → A ⊗_R R'` of a composite of two composite comparisons, the
composition isomorphism `Dualizing.compTailLeft` of the top-and-right edge and the class of a
chain map; the projection formula over `R'` at `baseChangeR (Q K)`; and the transpose over
[stacks 0GMT] along `R → R'`.

## Main results

* `Dualizing.squareIso_counit_conjugate_app_q_obj_eq` — **the conjugate itself**, no longer
  composed with the comparison: the right-hand side of
  `Dualizing.squareIso_counit_conjugate_comp_comparison_app_q_obj` divided by the composite
  comparison along `R → R' → A ⊗_R R'` at `K`.
* `Dualizing.homEquiv_squareIso_counit_conjugate_app_q_obj` — its transpose over [stacks 0GMT]
  along `R' → A ⊗_R R'`, with the leading factor `Fi (baseChangeR u)` taken out of the transpose
  by `CategoryTheory.Adjunction.homEquiv_naturality_left`.
* `Dualizing.tensorComparisonCompatibility_lhs_app_q_obj` — **the left-hand side of the
  obligation's hypothesis at `X = Q K`**, with both outer factors taken out of the two transposes
  and the square isomorphism gone.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj` — the projection
  formula over `R'` read at `baseChangeR (Q K)`, transported onto the class of the degreewise
  extension of scalars `R' ⊗_R K`, where
  `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates it: that complex is
  K-flat over `R'` by `Dualizing.kFlat_extendScalars_algebraMapR`.

## Implementation notes

The invertibility of the composite comparison along `R → R' → A ⊗_R R'` at `K` is an instance
binder rather than a K-flatness hypothesis, as in
`Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj`: a consumer at a K-flat `K` supplies it from
`Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat`, and the statements here are then free of
any hypothesis on `K`.

Every step is a forward `Eq.trans`/`congrArg` chain with its first argument known, for the reason
recorded in `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.SquareCounitConjugate`: the
two
spellings of the target of the composite comparison are definitionally but not syntactically
equal, so keyed matching does not cross them and `rfl` across them diverges.

No `@[stacks]` attribute is placed here: `Dualizing.TensorComparisonCompatibility` is still open,
so nothing in this file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
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
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The square isomorphism conjugating the counit, at the class of a K-flat complex and with no
comparison composed on.**  `Dualizing.squareIso_counit_conjugate_comp_comparison_app_q_obj` pins
the conjugate composed with the composite comparison along `R → R' → A ⊗_R R'` at `K`; that
comparison is invertible at a K-flat `K` by
`Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat`, so the equation determines the conjugate
itself.

This is the only invertibility the route uses, and it is at `K`, which K-flatness of `K` supplies:
the composite comparison is *not* inverted at `(A ⊗_R K)|_R`, which is not K-flat over `R` unless
`A` is flat over `R`. -/
theorem squareIso_counit_conjugate_app_q_obj_eq
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
      (algebraMap R R')
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom
      baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R'))
      algebraMap_tensorProduct_comp_right).app K)] :
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).inv.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj (Ff.obj (DerivedCategory.Q.obj K))) ≫
        baseChangeA.map
            ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
              alphaf).counit.app (Ff.obj (DerivedCategory.Q.obj K))) ≫
          (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).hom.app (DerivedCategory.Q.obj K) =
      (Fi.map (baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map (alphaf.app K) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
              max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
              max v uR uA uRp + 1}
              (algebraMap R R')
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom
              baseChangeR comparisonR Fi alphai
              (algebraMap R (TensorProduct R A R'))
              algebraMap_tensorProduct_comp_right).app
            (((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).inv.app
              (((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            DerivedCategory.Q.map
                (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                      (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                  (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
                    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
              (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).hom.app K) ≫
        CategoryTheory.inv
          ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
            max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
            max v uR uA uRp + 1}
            (algebraMap R R')
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom
            baseChangeR comparisonR Fi alphai
            (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_right).app K) :=
  (IsIso.eq_comp_inv _).mpr
    (squareIso_counit_conjugate_comp_comparison_app_q_obj baseChangeR comparisonR baseChangeA
      comparisonA Ff alphaf Fi alphai K)

include hf hA hR hi in
/-- **The conjugate's transpose over [stacks 0GMT] along `R' → A ⊗_R R'`, with the leading factor
taken out of the transpose.**  `Dualizing.squareIso_counit_conjugate_app_q_obj_eq` presents the
conjugate as `Fi (baseChangeR u)` — for `u` the explicit isomorphism
`(Ff (Q K))|_R ≅ Q ((A ⊗_R K)|_R)` — followed by data in which the square isomorphism does not
occur, so `CategoryTheory.Adjunction.homEquiv_naturality_left` moves `baseChangeR u` out of the
transpose.

What is left inside the transpose is the composite comparison along `R → R' → A ⊗_R R'` at
`(A ⊗_R K)|_R`, the composition isomorphism `Dualizing.compTailLeft` of the top-and-right edge
twice, the class of the degreewise counit extended along `A → A ⊗_R R'`, and the inverse of the
composite comparison at `K`.  Neither `Dualizing.derivedBaseChangeSquareIso` nor the counit of
[stacks 0GMT] along `R → A` appears. -/
theorem homEquiv_squareIso_counit_conjugate_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
      (algebraMap R R')
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom
      baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R'))
      algebraMap_tensorProduct_comp_right).app K)] :
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).homEquiv _ _
        ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
                Fi alphai).inv.app
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj (Ff.obj (DerivedCategory.Q.obj K))) ≫
            baseChangeA.map
                ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).counit.app (Ff.obj (DerivedCategory.Q.obj K))) ≫
              (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                comparisonR Fi alphai).hom.app (DerivedCategory.Q.obj K)) =
      baseChangeR.map
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.map (alphaf.app K) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).homEquiv _ _
          ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
                max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
                max v uR uA uRp + 1}
                (algebraMap R R')
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom
                baseChangeR comparisonR Fi alphai
                (algebraMap R (TensorProduct R A R'))
                algebraMap_tensorProduct_comp_right).app
              (((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).inv.app
                (((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
              DerivedCategory.Q.map
                  (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                      (ComplexShape.up ℤ)).map
                    (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
                        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
                      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
                (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).hom.app K ≫
                  CategoryTheory.inv
                    ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
                      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
                      max v uR uA uRp + 1}
                      (algebraMap R R')
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom
                      baseChangeR comparisonR Fi alphai
                      (algebraMap R (TensorProduct R A R'))
                      algebraMap_tensorProduct_comp_right).app K)) := by
  rw [squareIso_counit_conjugate_app_q_obj_eq baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai K, Category.assoc, Adjunction.homEquiv_naturality_left]
  congr 2
  exact Eq.trans (Category.assoc _ _ _) (congrArg (_ ≫ ·)
    (Eq.trans (Category.assoc _ _ _) (congrArg (_ ≫ ·) (Category.assoc _ _ _))))

include hf hA hR hi in
/-- **The left-hand side of the tensor-comparison obligation's hypothesis at the class of a K-flat
complex, with the square isomorphism eliminated.**  The left-hand side of the hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_homEquiv_square`, read at `X = Q K`, is

`pf.inv (Q K) ≫ u ≫`
`  homEquiv_{R → R'} (homEquiv_{R' → A ⊗_R R'} (W) ≫ pf'.hom (baseChangeR (Q K)))`,

where `u` is the explicit isomorphism `(Ff (Q K))|_R ≅ Q ((A ⊗_R K)|_R)` — the model comparison
`alphaf` at `K` followed by a `CategoryTheory.Functor.mapDerivedCategoryFactors` — and `W` is the
composite comparison along `R → R' → A ⊗_R R'` at `(A ⊗_R K)|_R`, the composition isomorphism
`Dualizing.compTailLeft` of the top-and-right edge, the class of the degreewise counit extended
along `A → A ⊗_R R'`, that composition isomorphism again, and the inverse of the composite
comparison at `K`.

Neither `Dualizing.derivedBaseChangeSquareIso` nor the counit of [stacks 0GMT] along `R → A`
occurs on the right-hand side; what is left of the left-hand side of the obligation is the two
projection formulas, the two transposes of [stacks 0GMT], chain-level data, and one inverse of
the composite comparison at `K`, which K-flatness of `K` supplies through
`Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat`.

This settles the left-hand side of the hypothesis.  Its right-hand side — the transpose of
`𝟙 ⊗ derivedBaseChangeAlgebraIso` read backwards through the change-of-rings isomorphism of
[stacks 0E1W] — is untouched, and `Dualizing.TensorComparisonCompatibility` remains open. -/
theorem tensorComparisonCompatibility_lhs_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
      (algebraMap R R')
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom
      baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R'))
      algebraMap_tensorProduct_comp_right).app K)] :
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
            (algebraMap R A) Ff alphaf).inv.app (DerivedCategory.Q.obj K) ≫
        (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
            comparisonR).homEquiv _ _
          ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).homEquiv _ _
              ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                      comparisonR Fi alphai).inv.app
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                    (Ff.obj (DerivedCategory.Q.obj K))) ≫
                baseChangeA.map
                    ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A)
                      Ff alphaf).counit.app (Ff.obj (DerivedCategory.Q.obj K))) ≫
                  (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                    comparisonR Fi alphai).hom.app (DerivedCategory.Q.obj K)) ≫
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
              (baseChangeR.obj (DerivedCategory.Q.obj K))) =
      (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
            (algebraMap R A) Ff alphaf).inv.app (DerivedCategory.Q.obj K) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.map (alphaf.app K) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
              comparisonR).homEquiv _ _
            ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).homEquiv _ _
                ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
                      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
                      max v uR uA uRp + 1}
                      (algebraMap R R')
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom
                      baseChangeR comparisonR Fi alphai
                      (algebraMap R (TensorProduct R A R'))
                      algebraMap_tensorProduct_comp_right).app
                    (((ModuleCat.restrictScalars.{max v uR uA uRp}
                        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
                  (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).inv.app
                      (((ModuleCat.restrictScalars.{max v uR uA uRp}
                          (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                          (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
                    DerivedCategory.Q.map
                        (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                              (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                            (ComplexShape.up ℤ)).map
                          (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
                              (algebraMap R A)).mapHomologicalComplex
                            (ComplexShape.up ℤ)).counit.app
                            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                              (algebraMap R A)).mapHomologicalComplex
                              (ComplexShape.up ℤ)).obj K))) ≫
                      (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).hom.app K ≫
                        CategoryTheory.inv
                          ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR,
                            uRp, max uA uRp, max v uA, max v uR uA uRp + 1,
                            max v uR uA uRp + 1, max v uR uA uRp + 1}
                            (algebraMap R R')
                            (Algebra.TensorProduct.includeRight :
                              R' →ₐ[R] TensorProduct R A R').toRingHom
                            baseChangeR comparisonR Fi alphai
                            (algebraMap R (TensorProduct R A R'))
                            algebraMap_tensorProduct_comp_right).app K)) ≫
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
                (baseChangeR.obj (DerivedCategory.Q.obj K))) := by
  refine congrArg (_ ≫ ·) ?_
  erw [homEquiv_squareIso_counit_conjugate_app_q_obj baseChangeR comparisonR baseChangeA
    comparisonA Ff alphaf Fi alphai K, Category.assoc, Adjunction.homEquiv_naturality_left]

include hA hR in
/-- **The right-hand side of the obligation's hypothesis, with [stacks 0E1W] eliminated.**  The
right-hand side of the hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_homEquiv_square` — the transpose over [stacks 0A63]
of the transpose over [stacks 0GMT] of the inverse transpose of
`𝟙 ⊗ derivedBaseChangeAlgebraIso`, composed with the inverse of the change-of-rings isomorphism of
[stacks 0E1W] — is the transpose over [stacks 0GMT] of

`ν_{X, A[0]} ≫ (𝟙 ⊗ derivedBaseChangeAlgebraIso)`,

where `ν` is `Dualizing.derivedTensorBaseChangeSection`, the two-sided inverse of the lax monoidal
structure map `μ` of derived base change along `R → R'`.

The isomorphism of [stacks 0E1W] does not occur on the right-hand side.  This is
`Dualizing.homEquiv_derivedTensorBaseChangeSection_tensorHomUnit` after the inverse transpose of
[stacks 0A63] is written as a coevaluation followed by an internal Hom
(`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_hom_map`).  Nothing is assumed
of `X`: no K-flat representative is involved.

So the remaining content of `Dualizing.TensorComparisonCompatibility` is a determinate value for
`ν`, equivalently for `μ`, equivalently for the component of [stacks 0E1W]: the three are
interdefinable — `Dualizing.derivedTensorBaseChangeSection` is a transpose of that component by
definition, and `Dualizing.homEquiv_derivedTensorBaseChangeSection` reads the component back off
it — and this is that interdefinability in the direction the obligation needs. -/
theorem tensorComparisonCompatibility_rhs_eq_section
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R).homEquiv X
          (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) _
        ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
              comparisonR).homEquiv X _
            (((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                  max v uR uA uRp + 1} R').homEquiv _ _ _).symm
              ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                  max v uR uA uRp + 1} R').tensor.map
                (Prod.mkHom (𝟙 (baseChangeR.obj X))
                  (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                    comparisonA hA).hom))) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR).inv.app
              (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), _)) =
      (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
          comparisonR).homEquiv _ _
        (derivedTensorBaseChangeSection.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
              comparisonR X (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
              max v uR uA uRp + 1} R').tensor.map
            (Prod.mkHom (𝟙 (baseChangeR.obj X))
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom)) := by
  have key := homEquiv_derivedTensorBaseChangeSection_tensorHomUnit.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR X
    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) _
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      (Prod.mkHom (𝟙 (baseChangeR.obj X))
        (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
          comparisonA hA).hom))
  rwa [DerivedHomAdjunction.tensorHomUnit_comp_hom_map
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R')
    (baseChangeR.obj X)
    (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) _ _] at key

omit hR in
include hi in
/-- **The projection formula over `R'` at the object the comparison reads it at.**
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_of_iso` transports the component of the
projection formula over `R'` along any isomorphism onto a class; at
`baseChangeR (Q K)` the isomorphism is the model comparison `comparisonR` at `K`, which is
invertible for a K-flat `K` by `Dualizing.isIso_comparisonR_app_of_kFlat`, and the class it lands
on is that of the degreewise extension of scalars `R' ⊗_R K`, which is K-flat over `R'` by
`Dualizing.kFlat_extendScalars_algebraMapR` — so
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates the transported
component there.

This puts the third factor of
`Dualizing.tensorComparisonCompatibility_lhs_app_q_obj` at a class of a K-flat complex, where it
is chain-level data. -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso (comparisonR.app K)] :
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
        (baseChangeR.obj (DerivedCategory.Q.obj K)) =
      (Fi ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory).map
          (comparisonR.app K) ≫
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          (derivedExtendRestrictScalarsTensorFunctor.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).map
            (CategoryTheory.inv (comparisonR.app K)) :=
  derivedExtendRestrictScalarsTensorIso_hom_app_of_iso.{uR, uA, uRp, v} Fi alphai _ _
    (asIso (comparisonR.app K))

end Dualizing

end
