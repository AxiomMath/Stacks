module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoreLHS

/-!
# The left-hand side of step 3's equation, second reduction

`CochainComplex.coreLHS_step1` reduced the left-hand side of step 3's elementwise equation for
[Stacks, Tag 09LK] to five factors: the descent `CochainComplex.homEvaluationDerivedIso`, the
transport `CochainComplex.homDerivedLiftForgetIsoMid`, the two factorizations of cohomology
through the homotopy category, and the explicit cohomology of the complex of a right differential
graded module. This file removes three of the five, at the homotopy class of a complex.

* The transport is the identity. `CochainComplex.homDerivedLiftForgetIsoMid` is `eqToIso` of the
  equality of functors `DGCategory.homDGFunctor_onK`, and that equality is
  `CategoryTheory.Functor.hext` of `rfl` on objects, so its component at any object is an
  `eqToHom` between two spellings of one object.
* The two factorizations of cohomology through the homotopy category compose to the
  factorization through the derived category, preceded by Mathlib's comparison of the two
  localizations: that is `DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj` with its
  trailing inverse cancelled.
* That comparison then annihilates the innermost factor of the descent, which
  `CochainComplex.homEvaluationDerivedIso_inv_app` shows is its inverse at the same complex.

What is left is the left-hand side as three factors, none of which is a localization comparison:
the forgetful square of the Hom representation, the unlocalized comparison of the two readings of
`Hom^•(K, Y)`, and the factorization of cohomology over the category of complexes followed by the
explicit cohomology.

## Main results

* `CochainComplex.homDerivedLiftForgetIsoMid_inv_app`: the transport is the identity.
* `CochainComplex.homologyFunctorFactorsh_hom_app_comp`: the two factorizations of cohomology
  through the homotopy category, composed.
* `CochainComplex.homologyMap_homEvaluationDerivedIso_inv_app`: `H^n` of the inverse of the
  descent at a complex, as three applications of `H^n`.
* `CochainComplex.coreLHS_step2`: **the second reduction.**

## Implementation notes

Everything here is a term proof or a `rw` on a goal in which the objects do not have to be
unfolded, for the reason recorded in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCoreLHS.lean`: the objects in sight are
`DGCategory.K` and `DGCategory.Obj` of the right-module category, and Mathlib's
`HomologicalComplexUpToQuasiIso.Qh` is not exposed, so `rw` either fails to find its own pattern
or leaves a goal that is not type-correct. In particular `rw [CategoryTheory.Functor.map_id]`
cannot match `H^n (𝟙 X)` here, and the two cancellations are performed by
`CategoryTheory.comp_id_mid` and `CategoryTheory.comp_cancel_mid'` — lemmas in which every object
is a variable, applied by `exact`, so that the matching happens at default transparency and
nothing is unfolded. No option is set and nothing is made reducible.

The one place where a definitional equality has to be *seen* rather than avoided is
`CochainComplex.homDerivedLiftForgetIsoMid_inv_app`, where `rfl` fails but
`CategoryTheory.eqToHom_refl` applied by `exact` succeeds: `rfl` elaborates at a transparency that
stops at `Qh`, while unifying the two endpoints of `eqToHom_refl` does not need `Qh` unfolded.

## What is still owed

This file does not finish goal 2's piece (B). What remains, and it is one lemma, is the
intertwining of the two explicit cohomologies by the degreewise comparison. Expanding
`DGCategory.HomRepresentation.forgetSquareIso` by `CochainComplex.forgetSquareIso_hom_app` and
identifying its first factor by `CochainComplex.complexesQuotientSquareIso_inv_app_onComp`, and
expanding `CochainComplex.homologyGradedCohomologyIso` by
`CochainComplex.homologyGradedCohomologyIso_hom_app` and
`DifferentialGradedModule.derivedForgetHomologyIso_hom_app`, the two sides share their first three
factors — the derived forgetful image of the quotient comparison, the forgetful factorization and
the passage from the homotopy category to the derived category. Moving
`H^n(Q(homEvaluationComparisonIso))` across `DerivedCategory.homologyFunctorFactors_hom_naturality`
then leaves exactly

```
HomologicalComplex.homologyMap ((homEvaluationComparisonIso A K).hom.app Y) n ≫
    (DGCategory.RightModule.gradedCohomologyIso
      (DGCategory.yonedaRightModule (dgCategory A) Y) K n).hom =
  (DifferentialGradedModule.gradedCohomologyIso
      (DGCategory.representableModule (dgCategory A) K Y) n).hom ≫
    ModuleCat.ofHom (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap
```

which typechecks as written — the two indexings agree because
`DGCategory.RightModule.gradedCohomology_evaluation` is `rfl`. It mentions no derived category and
no comparison `ν`: both sides are maps out of a `homology n`, `HomologicalComplex.homologyπ` is
epi, and the two characterisations
`DifferentialGradedModule.homologyπ_gradedCohomologyIso_hom` and
`DGCategory.RightModule.homologyπ_gradedCohomologyIso_hom` reduce it to the agreement of
`CochainComplex.homEvaluationComparisonIso_hom_app_f_apply` with
`CochainComplex.homYonedaCocyclesEquiv_coe` — both of which are `CochainComplex.homGradingEquiv`.
The bookkeeping that is left is the two `HomologicalComplex.cyclesIsoSc'`, which the
`DifferentialGradedModule` side folds away and the `DGCategory.RightModule` side does not.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 the
  equation belongs to.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

/-- `(a ≫ b ≫ g) ≫ g' ≫ r = a ≫ b ≫ r` for a `g` with a retraction `g'`. -/
private alias CategoryTheory.comp_cancel_mid' := CategoryTheory.comp_cancel_mid

/-- `a ≫ u ≫ r = a ≫ r` for a `u` that is the identity. Every object is a variable, so
`exact`ing this at a composite whose middle object is a large semireducible term matches it at
default transparency and unfolds nothing. -/
private theorem CategoryTheory.comp_id_mid {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y)
    {u : Y ⟶ Y} (r : Y ⟶ Z) (h : u = 𝟙 Y) : a ≫ u ≫ r = a ≫ r := by
  rw [h, Category.id_comp]

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- The middle transport of `ν` is the identity on components. -/
theorem homDerivedLiftForgetIsoMid_inv_app (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (homDerivedLiftForgetIsoMid A K).inv.app Y = 𝟙 _ := by
  rw [homDerivedLiftForgetIsoMid, eqToIso.inv, eqToHom_app]
  exact eqToHom_refl _ _

/-- The two factorizations of cohomology through the homotopy category, composed. -/
theorem homologyFunctorFactorsh_hom_app_comp (X : CochainComplex (ModuleCat.{0} ℤ) ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{0} ℤ) n).hom.app
          ((HomotopyCategory.quotient (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).obj X) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} ℤ)
          (ComplexShape.up ℤ) n).hom.app X =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)).hom.app X) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℤ) n).hom.app X := by
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj, Category.assoc,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- `H^n` of the inverse of the descent at a complex, as three applications of `H^n`. -/
theorem homologyMap_homEvaluationDerivedIso_inv_app (n : ℤ) (Y : CochainComplex A ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((homEvaluationDerivedIso A K).inv.app ((DGCategory.compToK (dgCategory A)).obj Y)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          (((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).hom.app Y) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            (DerivedCategory.Q.map ((homEvaluationComparisonIso A K).hom.app Y)) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)).inv.app
              ((homEvaluationComplexFunctor A K).obj Y)) :=
  (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
      (homEvaluationDerivedIso_inv_app A K Y)).trans
    (((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _).trans
      (congrArg (fun t => (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map _ ≫ t)
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _)))

/-- **The left-hand side of step 3's equation, at the homotopy class of a complex.** -/
theorem coreLHS_step2 (n : ℤ) (Y : CochainComplex A ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homDerivedLiftForgetIso A K).inv.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≫
        (DGCategory.RightModule.endDerivedForgetGradedCohomologyIso (dgCategory A) K
          ((yonedaHomotopyFunctor A).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) PUnit.unit n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          (((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).hom.app Y) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            (DerivedCategory.Q.map ((homEvaluationComparisonIso A K).hom.app Y)) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℤ) n).hom.app
              ((homEvaluationComplexFunctor A K).obj Y) ≫
            (DGCategory.RightModule.gradedCohomologyIso
              ((DGCategory.evaluationOnK (dgCategory A) K).obj
                ((yonedaHomotopyFunctor A).obj
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))) PUnit.unit
              n).hom := by
  have h4 := ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).mapIso
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)).app
      ((homEvaluationComplexFunctor A K).obj Y))).inv_hom_id
  have hid : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((homDerivedLiftForgetIsoMid A K).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) = 𝟙 _ :=
    (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        (homDerivedLiftForgetIsoMid_inv_app A K _)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_id _)
  refine (coreLHS_step1 A K n _).trans ?_
  refine Eq.trans (comp_id_mid _ _ hid) ?_
  refine Eq.trans (congrArg (fun t => t ≫ _)
    (homologyMap_homEvaluationDerivedIso_inv_app A K n Y)) ?_
  refine Eq.trans (congrArg (fun t => _ ≫ t)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫
          (DGCategory.RightModule.gradedCohomologyIso
            ((DGCategory.evaluationOnK (dgCategory A) K).obj
              ((yonedaHomotopyFunctor A).obj
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))) PUnit.unit n).hom)
        (homologyFunctorFactorsh_hom_app_comp
          ((homEvaluationComplexFunctor A K).obj Y) n))).trans
      (Category.assoc _ _ _))) ?_
  exact comp_cancel_mid' _ _ _ h4

end CochainComplex

end
