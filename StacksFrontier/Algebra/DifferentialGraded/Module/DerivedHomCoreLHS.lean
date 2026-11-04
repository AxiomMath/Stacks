module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomEvaluationDerivedIsoApp
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedForgetGradedCohomology

/-!
# The left-hand side of step 3's elementwise equation, first reduction

Step 3 of the replacement proof of [Stacks, Tag 09LK] has to compare two maps out of the
degree-`n` cohomology of `Hom^•(K, Y)`. One of them — the *left-hand side* — is the comparison
`ν` of step 3 followed by the identification of the cohomology of the forgetful image of a
derived right differential graded module with the explicit cohomology of its complex:

`H^n(Hom(K, Y)) --H^n(ν⁻¹)--> H^n(U(Q_E(ev_K(h_Y)))) --≅--> H^n(ev_K(h_Y))`.

The second map is `DGCategory.RightModule.endDerivedForgetGradedCohomologyIso`, and `ν⁻¹` is the
three-factor composite of `CochainComplex.homDerivedLiftForgetIso_inv`. This file performs the
cancellation that those two share: the outermost factor of `ν⁻¹` is the *inverse* of
`DGCategory.RightModule.derivedEvaluationForgetCompIso`, and the innermost factor of the
identification is its *hom*, so the two annihilate and the left-hand side is a composite of four
maps in which that comparison no longer occurs.

## Main results

* `DGCategory.RightModule.derivedForgetGradedCohomologyIso_hom_factors`: the identification of the
  cohomology of the forgetful image with the explicit cohomology, as the four factors it is built
  from, with the two associators discharged.
* `DGCategory.RightModule.endDerivedForgetGradedCohomologyIso_hom`: the same at the endomorphism
  differential graded category, which is where step 3 uses it.
* `CochainComplex.homologyMap_homDerivedLiftForgetIso_inv_app`: `H^n(ν⁻¹)` at an object, as the
  three applications of `H^n` to the three factors of `ν⁻¹`.
* `CochainComplex.coreLHS_step1`: **the cancellation.** The left-hand side of step 3's equation
  is the descent `CochainComplex.homEvaluationDerivedIso`, the transport
  `CochainComplex.homDerivedLiftForgetIsoMid`, and the three comparisons of cohomology with the
  explicit cohomology — no evaluation-forget comparison.

## Implementation notes

*Why none of this is proved by `rw` or `simp` on the composite.* The objects in sight are
`DGCategory.K` and `DGCategory.Obj` of the category of right differential graded modules, and
those two are distinct semireducible definitions that `rw` has to unfold to see the composite's
middle object. Attempting `rw [Functor.map_comp]` on `H^n(f ≫ g)` here reports that it "did not
find an occurrence" of its own pattern, and a `rw` chain that does get started leaves a goal that
is no longer type-correct at `implicit` transparency.

Both places where that happens are avoided by the same device, and neither needs an option to be
set or a definition to be made reducible:

* `CochainComplex.homologyMap_homDerivedLiftForgetIso_inv_app` is an explicit `Eq.trans` of
  `congrArg` and `CategoryTheory.Functor.map_comp`. A term never has to *find* an occurrence, so
  the transparency question does not arise.
* the cancellation itself is `CategoryTheory.comp_cancel_mid`, in which every object is a
  variable and the invertibility is a hypothesis `g ≫ g' = 𝟙`. Applying it with `exact` matches
  the objects at default transparency and never unfolds them.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 the
  equation belongs to.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u r

/-- `(a ≫ b ≫ g) ≫ g' ≫ r = a ≫ b ≫ r` for a `g` with a retraction `g'`.

Every object of the composite is a variable and the invertibility is the hypothesis `h`, so
`exact`ing this lemma at a composite whose objects are large semireducible terms matches them at
default transparency and unfolds none of them. That is the whole reason it is stated separately
rather than performed by a `rw` chain on the composite in question. -/
theorem CategoryTheory.comp_cancel_mid {D : Type*} [Category D] {X Y Z W V : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) {g : Z ⟶ W} {g' : W ⟶ Z} (r : Z ⟶ V) (h : g ≫ g' = 𝟙 Z) :
    (a ≫ b ≫ g) ≫ g' ≫ r = a ≫ b ≫ r := by
  rw [Category.assoc, Category.assoc, ← Category.assoc g g' r, h, Category.id_comp]

namespace DGCategory.RightModule

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **The identification of the cohomology of the forgetful image with the explicit cohomology,
decomposed.** `DGCategory.RightModule.derivedForgetGradedCohomologyIso` is the comparison of the
derived evaluation with evaluation on homotopy categories, followed by the two factorizations of
cohomology through the homotopy category and by the explicit cohomology of a complex.

The two associators that
`DGCategory.RightModule.derivedEvaluationForgetHomologyIso` carries are the identity on
components, so they contribute only the two `CategoryTheory.Category.id_comp` of the proof; the
definitional content is the `rfl` cast, and the three category axioms are what the `rw` does. -/
theorem derivedForgetGradedCohomologyIso_hom_factors (M : (rightModuleCategory.{v} C).K) (X : C.Obj)
    (n : ℤ) :
    (derivedForgetGradedCohomologyIso C M X n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((derivedEvaluationForgetCompIso C X).hom.app M) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{v} R) n).hom.app
            ((cochainComplexOnK.{v} X).obj M) ≫
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
              (ComplexShape.up ℤ) n).hom.app (cochainComplex (C := C) M X) ≫
            (gradedCohomologyIso M X n).hom := by
  rw [show (derivedForgetGradedCohomologyIso C M X n).hom =
      (𝟙 _ ≫ ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
            ((derivedEvaluationForgetCompIso C X).hom.app M) ≫ 𝟙 _ ≫
          (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{v} R) n).hom.app
            ((cochainComplexOnK.{v} X).obj M))) ≫
      ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
          (ComplexShape.up ℤ) n).hom.app (cochainComplex (C := C) M X) ≫
        (gradedCohomologyIso M X n).hom) from rfl,
    Category.id_comp, Category.id_comp, Category.assoc]

/-- **The same decomposition at the endomorphism differential graded category.** This is the form
step 3 of [Stacks, Tag 09LK] uses: the module is the evaluation at `K` of a right differential
graded module over `C`, and the object of `E = C(K, K)` is its single one. -/
theorem endDerivedForgetGradedCohomologyIso_hom (M : (rightModuleCategory.{v} C).K) (K : C.Obj)
    (e : (endDGCategory C K).Obj) (n : ℤ) :
    (endDerivedForgetGradedCohomologyIso C K M e n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((derivedEvaluationForgetCompIso (endDGCategory C K) e).hom.app
            ((evaluationOnK.{v} C K).obj M)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{v} R) n).hom.app
            ((cochainComplexOnK.{v} e).obj ((evaluationOnK.{v} C K).obj M)) ≫
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
                (ComplexShape.up ℤ) n).hom.app
              (cochainComplex (C := endDGCategory C K) ((evaluationOnK.{v} C K).obj M) e) ≫
            (gradedCohomologyIso ((evaluationOnK.{v} C K).obj M) e n).hom :=
  derivedForgetGradedCohomologyIso_hom_factors (endDGCategory C K)
    ((evaluationOnK.{v} C K).obj M) e n

end DGCategory.RightModule

namespace CochainComplex

universe u'

variable (A : Type u') [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **`H^n(ν⁻¹)` at an object, as three applications of `H^n`.** The comparison `ν` of step 3 of
[Stacks, Tag 09LK] has the three factors recorded by
`CochainComplex.homDerivedLiftForgetIso_inv`, and `H^n` of a composite is the composite of the
`H^n`s.

The proof is an explicit `Eq.trans` of `congrArg` and `CategoryTheory.Functor.map_comp` rather
than a `rw` chain: the middle objects of the composite are `DGCategory.K` and `DGCategory.Obj` of
the category of right differential graded modules, and `rw [Functor.map_comp]` cannot match its
own pattern against them without unfolding those two semireducible definitions. A term proof has
no occurrence to find. -/
theorem homologyMap_homDerivedLiftForgetIso_inv_app (n : ℤ)
    (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((homDerivedLiftForgetIso A K).inv.app Y) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homEvaluationDerivedIso A K).inv.app
            ((homotopyCategoryEquivalence A).functor.obj Y)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((homDerivedLiftForgetIsoMid A K).inv.app Y) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((DGCategory.RightModule.derivedEvaluationForgetCompIso
              (DGCategory.endDGCategory (dgCategory A) K) PUnit.unit).inv.app
              ((DGCategory.evaluationOnK (dgCategory A) K).obj
                ((yonedaHomotopyFunctor A).obj Y))) :=
  (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
      (NatTrans.congr_app (homDerivedLiftForgetIso_inv A K) Y)).trans
    ((((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _).trans
        (congrArg (· ≫ _)
          (((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n)).map_comp _ _))).trans
      (Category.assoc _ _ _))

/-- **The left-hand side of step 3's equation, with the evaluation-forget comparison cancelled.**
The composite of `H^n(ν⁻¹)` with
`DGCategory.RightModule.endDerivedForgetGradedCohomologyIso` is

`H^n(descent⁻¹) ≫ H^n(transport⁻¹) ≫ (the two factorizations of cohomology) ≫ (explicit
cohomology)`,

because the outermost factor of `ν⁻¹` is the inverse of
`DGCategory.RightModule.derivedEvaluationForgetCompIso` and the innermost factor of the
identification is its hom.

What remains on the right is therefore a composite in which the only factors not already computed
elementwise are the descent `CochainComplex.homEvaluationDerivedIso` — computed by
`CochainComplex.homEvaluationDerivedIso_inv_app` — and the transport
`CochainComplex.homDerivedLiftForgetIsoMid`. -/
theorem coreLHS_step1 (n : ℤ) (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homDerivedLiftForgetIso A K).inv.app Y) ≫
        (DGCategory.RightModule.endDerivedForgetGradedCohomologyIso (dgCategory A) K
          ((yonedaHomotopyFunctor A).obj Y) PUnit.unit n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homEvaluationDerivedIso A K).inv.app
            ((homotopyCategoryEquivalence A).functor.obj Y)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((homDerivedLiftForgetIsoMid A K).inv.app Y) ≫
          (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{0} ℤ) n).hom.app
              ((DGCategory.RightModule.cochainComplexOnK PUnit.unit).obj
                ((DGCategory.evaluationOnK (dgCategory A) K).obj
                  ((yonedaHomotopyFunctor A).obj Y))) ≫
            (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} ℤ)
                  (ComplexShape.up ℤ) n).hom.app
                (DGCategory.RightModule.cochainComplex
                  ((DGCategory.evaluationOnK (dgCategory A) K).obj
                    ((yonedaHomotopyFunctor A).obj Y)) PUnit.unit) ≫
              (DGCategory.RightModule.gradedCohomologyIso
                ((DGCategory.evaluationOnK (dgCategory A) K).obj
                  ((yonedaHomotopyFunctor A).obj Y)) PUnit.unit n).hom := by
  rw [homologyMap_homDerivedLiftForgetIso_inv_app,
    DGCategory.RightModule.endDerivedForgetGradedCohomologyIso_hom]
  exact comp_cancel_mid _ _ _
    (((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _).symm.trans
      ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((DGCategory.RightModule.derivedEvaluationForgetCompIso
            (DGCategory.endDGCategory (dgCategory A) K) PUnit.unit).inv_hom_id_app _)).trans
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_id _)))

end CochainComplex

end
