module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLiftComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomVariant

/-!
# Step 3 of Tag 09LK at the lift Tag 09LK itself registers

`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean` proves step 3 of
the replacement proof of [Stacks, Tag 09LK] for an *abstract* lift: a category `E`, a functor
`U : E ⥤ D(Ab)`, a functor `R̃ : D(A) ⥤ E` and a comparison
`β : Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)`, together with the identification `(*)`
`CochainComplex.DerivedHomLiftIdentification` of the cohomology of the values of the lift with the
morphism groups of `D(A)`. Its conclusions are that the canonical comparison
`θ : R Hom(K, -) ⟶ R̃ ⋙ U` out of the abelian-group-valued derived Hom is invertible, and
equivalently that `R̃ ⋙ U` with `β` is a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`.

The declarations Tag 09LK registers in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` are not about an abstract
`E`: they are about `DifferentialGradedModule.derivedCategory' (endAlgebra A K)` and the
forgetful functor `DifferentialGradedModule.derivedForget` out of it. This file carries out that
instantiation — it writes down which `E`, `U`, `R̃` and `β` the registered side presents, and
proves that at those values the hypothesis `(*)` of step 3 *holds*, from the hypothesis the
registered declarations already take.

So the two sides meet: step 3's interface is aimed at exactly the target Tag 09LK is registered
on, and the strengthened hypothesis in force there is at least as strong as everything step 3
consumes. The instantiation is

* `E := DifferentialGradedModule.derivedCategory' (CochainComplex.endAlgebra A K)`, the derived
  category of differential graded `E = End(K)`-modules;
* `U := DifferentialGradedModule.derivedForget (CochainComplex.endAlgebra A K)`, the forgetful
  functor to `D(Ab)` of
  `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedForgetful.lean`;
* `R̃ := CochainComplex.derivedHomFunctor A K h`, Tag 09LK's functor;
* `β := CochainComplex.derivedHomForgetUnitOfDerivable A K h`, the `U`-image of
  `CochainComplex.derivedHomFunctorUnit`.

## What this does and does not settle

It does not discharge the deviation recorded on `CochainComplex.derivedHomFunctor`. The lift
instantiated here is built from the `D(E, d)`-valued derivability hypothesis, so `(*)` is proved
*from* that hypothesis and not from the source's. What the file adds is the junction: a
construction of a lift by other means — the differential graded localization argument of
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomReflectorExists.lean`, which
takes the source's hypothesis — would enter step 3 through exactly this interface, at exactly
these four values, and the registered conclusions are what it would have to reproduce.

It also records, as the named isomorphism
`CochainComplex.derivedHomForgetFunctorIso`, that the abelian-group-valued derived Hom assembled
from the source's hypothesis in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomValueCohomology.lean` *is* the reduction
of Tag 09LK's functor on taking associated complexes. The two sides of Tag 09LK's reduction
clause are rfl-equal to nothing: they are two separately assembled functors, and the clause
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor` compares them only
through a universal property. The isomorphism whose declared type mentions both is the usable
form, and it is obtained from step 3, not from the universal property directly.

## Main definitions

* `CochainComplex.derivedHomForgetUnitOfDerivable`: the comparison `β` of the instantiation, the
  forgetful image of Tag 09LK's canonical comparison.
* `CochainComplex.derivedHomLiftIdentificationOfIsRightDerivable`: the hypothesis `(*)` of step
  3, at the instantiation above.
* `CochainComplex.derivedHomForgetFunctorIso`: the isomorphism
  `R Hom(K, -) : D(A) ⥤ D(Ab) ≅ R Hom(K, -) : D(A) ⥤ D(E, d)` followed by the forgetful functor.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w w' u

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (h : (homToDerivedCategory A K).IsRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

/-- **The comparison `β` of the instantiation.** Tag 09LK's canonical comparison
`Hom(K, -) ⟶ Qh ⋙ R Hom(K, -)` of `CochainComplex.derivedHomFunctorUnit`, read in `D(Ab)` by
applying the forgetful functor `D(E, d) ⥤ D(Ab)` and reassociating. This is the datum step 3 of
the replacement proof consumes, and the unit with respect to which
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor` is stated. -/
def derivedHomForgetUnitOfDerivable :
    homToDerivedCategoryForget A K ⟶ DerivedCategory.Qh ⋙
      derivedHomFunctor A K h ⋙ DifferentialGradedModule.derivedForget (endAlgebra A K) :=
  Functor.whiskerRight (derivedHomFunctorUnit A K h)
      (DifferentialGradedModule.derivedForget (endAlgebra A K)) ≫
    (Functor.associator _ _ _).hom

/-- **The hypothesis `(*)` of step 3 holds at Tag 09LK's own lift.** For `E = D(E, d)`,
`U` the forgetful functor, `R̃ = R Hom(K, -)` of `CochainComplex.derivedHomFunctor` and `β` its
forgetful image, the identification
`CochainComplex.DerivedHomLiftIdentification` of the cohomology of the values of the lift with the
morphism groups `Hom_{D(A)}(Q K, (Q X)⟦n⟧)` is available.

It is obtained from `CochainComplex.derivedHomLiftIdentificationOfIsRightDerivedFunctor`, the
converse half of step 3, applied to Tag 09LK's reduction clause
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor`. So it is proved from
the `D(E, d)`-valued derivability hypothesis, which is strictly what the registered declarations
assume; it is *not* a route from the source's hypothesis to the registered conclusions. -/
def derivedHomLiftIdentificationOfIsRightDerivable :
    DerivedHomLiftIdentification A K
      (DifferentialGradedModule.derivedForget (endAlgebra A K)) (derivedHomFunctor A K h)
      (derivedHomForgetUnitOfDerivable A K h) :=
  derivedHomLiftIdentificationOfIsRightDerivedFunctor A K
    (DifferentialGradedModule.derivedForget (endAlgebra A K)) (derivedHomFunctor A K h)
    (isRightDerivable_homToDerivedCategoryForget_quasiIso A K h)
    (derivedHomForgetUnitOfDerivable A K h)
    (derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor A K h)

/-- **The reduction clause of Tag 09LK as an isomorphism.** The abelian-group-valued derived Hom
`R Hom(K, -) : D(A) ⥤ D(Ab)` assembled from the source's own hypothesis is isomorphic to Tag
09LK's functor `R Hom(K, -) : D(A) ⥤ D(E, d)` followed by the forgetful functor taking associated
complexes.

Both sides are separately assembled left Kan extensions, so this is not an identity of
definitions and no reassociation produces it; it is the comparison `θ` of step 3,
`CochainComplex.derivedHomForgetComparisonIso`, at the instantiation of this file. -/
def derivedHomForgetFunctorIso :
    derivedHomForgetFunctor A K (isRightDerivable_homToDerivedCategoryForget_quasiIso A K h) ≅
      derivedHomFunctor A K h ⋙ DifferentialGradedModule.derivedForget (endAlgebra A K) :=
  derivedHomForgetComparisonIso A K
    (DifferentialGradedModule.derivedForget (endAlgebra A K)) (derivedHomFunctor A K h)
    (isRightDerivable_homToDerivedCategoryForget_quasiIso A K h)
    (derivedHomForgetUnitOfDerivable A K h)
    (derivedHomLiftIdentificationOfIsRightDerivable A K h)

end CochainComplex

end
