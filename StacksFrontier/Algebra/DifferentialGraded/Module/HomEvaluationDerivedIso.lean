module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLiftComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomEvaluationComplexIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexCompShift
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentationForget
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedCochainComplex

/-!
# The comparison `β` of Tag 09LK: the lift of `Hom(K, -)` through the forgetful functor

Let `A` be a preadditive category with morphisms in `Type 0` and let `K` be a cochain complex in
`A`. Steps 1 and 2 of the replacement proof of [Stacks, Tag 09LK]
(`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomReflectorExists.lean`)
produce, for the differential graded category of complexes `C = Comp^dg(A)` and the one-object
differential graded category `E = C(K, K)`, an exact functor `R̃ : D(A) ⥤ D(E)` together with a
unit

`η : Φ ⋙ ev_K ⋙ Q_E ⟶ q ⋙ R̃`

whose source is the differential graded Yoneda functor followed by evaluation at `K` and the
quotient functor of `D(E)`. Step 3 of that proof
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean`) consumes instead
a comparison

`β : Hom(K, -) ⟶ Q ⋙ R̃ ⋙ U`

out of the abelian-group-valued `Hom(K, -) : K(A) ⥤ D(Ab)`, where `U : D(E) ⥤ D(Ab)` is the
forgetful functor `DGCategory.endDerivedForget`. The two are joined by the identification of the
source of `η`, read through `U`, with `Hom(K, -)`; this file produces that identification and
hence `β`.

## How the identification is assembled

Composing with `U` is, by `DGCategory.RightModule.derivedEvaluationForgetCompIso`, evaluation at
the unique object of `E` followed by the localization of complexes of `ℤ`-modules. So both
functors are a functor on the homotopy category of `Comp^dg(A)` followed by
`DerivedCategory.Qh`, and the whole comparison descends from the category of complexes
`Comp(Comp^dg(A))`, along `DGCategory.compToK`, by the fully faithfulness of precomposition with
it (`DGCategory.whiskeringLeft_compToK_full`). Down there the three compatibilities are:

* evaluation at an object commutes with the passage to homotopy classes, which is
  `DGCategory.RightModule.compToK_comp_cochainComplexOnK` and an equality of functors;
* the differential-graded-module side is the underlying complex of `Hom(K, -)`, which is
  `DGCategory.HomRepresentation.forgetSquareIso`;
* the two complexes of `ℤ`-modules named `Hom^•(K, Y)` agree, which is the unlocalized
  mathematical content and is `CochainComplex.homEvaluationComparisonIso`.

## Main definitions

* `CochainComplex.yonedaHomotopyFunctor`: the differential graded Yoneda functor `X ↦ h_X` as a
  functor `K(A) ⥤ K(Mod^dg(Comp^dg(A)))`, which is the `Φ` of steps 1 and 2.
* `CochainComplex.homDerivedLift`: **the lift `V : K(A) ⥤ D(E)`**, that `Φ` followed by
  evaluation at `K` and the quotient functor of `D(E)`.
* `CochainComplex.homDerivedLiftForgetIso`: **the identification `ι : V ⋙ U ≅ Hom(K, -)`.**
* `CochainComplex.homDerivedForgetUnit`: **the comparison `β`**, obtained from `ι` and a unit
  `η : V ⟶ Q ⋙ R̃`.

## Main results

* `CochainComplex.homEvaluationDerivedIso`: the identification before the Yoneda functor is
  prefixed, as an isomorphism of functors on the homotopy category of `Comp^dg(A)`.

## Implementation notes

Nothing here assumes `A` abelian or a derived category of `A` to exist, except
`CochainComplex.homDerivedForgetUnit`, which mentions `DerivedCategory.Qh`. The universe of `A`
is unconstrained: `DGCategory.endDerivedForget` and
`DGCategory.HomRepresentation.forgetSquareIso` both ask only that the morphism modules of the
differential graded category live in the universe of the base ring, which for `Comp^dg(A)` over
`ℤ` with `A` having morphisms in `Type 0` holds.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor `Hom(K, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v w u

namespace CochainComplex

section Preadditive

variable (A : Type u) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)

/-- **The differential graded Yoneda functor on the homotopy category**, `X ↦ h_X`: the
comparison of the homotopy category of complexes with that of the differential graded category of
complexes, followed by the functor induced on homotopy classes by `X ↦ C(-, X)`. This is the
functor `Φ` that steps 1 and 2 of the replacement proof of [Stacks, Tag 09LK] take as their
source. -/
def yonedaHomotopyFunctor :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤
      (DGCategory.rightModuleCategory (dgCategory A)).K :=
  (homotopyCategoryEquivalence A).functor ⋙ (DGCategory.yonedaDGFunctor (dgCategory A)).onK

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The lift `V : K(A) ⥤ D(E)` of `Hom(K, -)`.** The differential graded Yoneda functor
followed by evaluation at `K` and by the quotient functor of the derived category of right
differential graded modules over `E = C(K, K)`. This is the source of the unit that steps 1 and 2
of the replacement proof of [Stacks, Tag 09LK] produce. -/
def homDerivedLift :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤
      DGCategory.RightModule.derivedCategory (DGCategory.endDGCategory (dgCategory A) K) :=
  yonedaHomotopyFunctor A ⋙ DGCategory.evaluationOnK (dgCategory A) K ⋙
    DGCategory.RightModule.derivedQ (DGCategory.endDGCategory (dgCategory A) K)

/-- **`ev_K(h_-)` and `Hom^•(K, -)` agree in `D(Ab)`.** On the homotopy category of the
differential graded category of complexes, evaluating the differential graded Yoneda module at
`K` and reading the result in the derived category of complexes of `ℤ`-modules is the functor
`Hom(K, -)` of [Stacks, Tag 09LE] into the derived category of differential graded `End(K)`-
modules, read in `D(Ab)` by the forgetful functor.

The isomorphism is obtained by descent along `DGCategory.compToK`, where it is
`CochainComplex.homEvaluationComparisonIso`. -/
def homEvaluationDerivedIso :
    (DGCategory.homDGFunctor (dgCategory A) K).onK ⋙
        DGCategory.RightModule.cochainComplexOnK PUnit.unit ⋙ DerivedCategory.Qh ≅
      (DGCategory.homRepresentation (dgCategory A) K).homotopyFunctor ⋙
        (DifferentialGradedModule.quasiIsomorphisms' (endAlgebra A K)).Q ⋙
          DifferentialGradedModule.derivedForget (endAlgebra A K) := by
  refine Functor.preimageIso
    ((Functor.whiskeringLeft (dgCategory A).Comp (dgCategory A).K
      (DerivedCategory (ModuleCat.{0} ℤ))).obj (DGCategory.compToK (dgCategory A)))
    (?_ ≪≫ ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).symm)
  exact Functor.isoWhiskerLeft (homEvaluationComplexFunctor A K)
      (DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)) ≪≫
    Functor.isoWhiskerRight (homEvaluationComparisonIso A K).symm DerivedCategory.Q

/-- **The identification `ι : V ⋙ U ≅ Hom(K, -)` that step 3 of [Stacks, Tag 09LK] consumes.**
The lift `CochainComplex.homDerivedLift`, read in the derived category of complexes of
`ℤ`-modules through the forgetful functor `DGCategory.endDerivedForget`, is the
abelian-group-valued `Hom(K, -) : K(A) ⥤ D(Ab)` that the tag right derives. -/
def homDerivedLiftForgetIso :
    homDerivedLift A K ⋙ DGCategory.endDerivedForget (dgCategory A) K ≅
      homToDerivedCategoryForget A K :=
  Functor.isoWhiskerLeft
      (yonedaHomotopyFunctor A ⋙ DGCategory.evaluationOnK (dgCategory A) K)
      (DGCategory.RightModule.derivedEvaluationForgetCompIso
        (DGCategory.endDGCategory (dgCategory A) K) PUnit.unit) ≪≫
    eqToIso (by rw [DGCategory.homDGFunctor_onK]; rfl) ≪≫
    Functor.isoWhiskerLeft (homotopyCategoryEquivalence A).functor
      (homEvaluationDerivedIso A K)

end Preadditive

section Beta

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (Rt : DerivedCategory A ⥤
    DGCategory.RightModule.derivedCategory (DGCategory.endDGCategory (dgCategory A) K))

/-- **The comparison `β` of [Stacks, Tag 09LK].** Given the unit
`η : V ⟶ Q ⋙ R̃` that steps 1 and 2 of the replacement proof produce, forgetting it along
`DGCategory.endDerivedForget` and composing with
`CochainComplex.homDerivedLiftForgetIso` gives the comparison out of the abelian-group-valued
`Hom(K, -)` that step 3 consumes. -/
def homDerivedForgetUnit (η : homDerivedLift A K ⟶ DerivedCategory.Qh ⋙ Rt) :
    homToDerivedCategoryForget A K ⟶
      DerivedCategory.Qh ⋙ Rt ⋙ DGCategory.endDerivedForget (dgCategory A) K :=
  derivedHomForgetUnitOfLift A K (DGCategory.endDerivedForget (dgCategory A) K) Rt
    (homDerivedLift A K) (homDerivedLiftForgetIso A K) η

end Beta

end CochainComplex

end
