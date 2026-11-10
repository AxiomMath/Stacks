module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomVariant

/-!
# `Hom(K, -)` commutes with the translation on homotopy, on derived and on derived-functor level

Let `K` be a cochain complex in a preadditive category `B` and let `E = End(K)`. The
`CategoryTheory.Functor.CommShift ℤ` carried by
`Hom(K, -) : CochainComplex B ℤ ⥤ Mod_{(E, d)}` descends to the homotopy category, is carried
along the localization at the quasi-isomorphisms, and — for `B` abelian with a chosen derived
category — is inherited by the right derived functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of Tag 09LK,
whose canonical comparison is compatible with it.

The descent is the only step with content. `CochainComplex.homHomotopyFunctor` is *not* defined
as a descent: it is the comparison of `K(B)` with the homotopy category of the differential graded
category of complexes, followed by the functor of Tag 09LE on homotopy classes and the comparison
of the homotopy category of the differential graded category of differential graded modules with
`K(E, d)`. So the descent of `Hom(K, -)` along the quotient by homotopy has to be *identified*
with it, and that identification is `CochainComplex.homHomotopyFunctorLiftIso`.

## Main definitions

* `CochainComplex.homHomotopyFunctorQuotientIso`: the comparison
  `K(B)` ← complexes → `K(E, d)`, i.e. `Hom(K, -)` on homotopy classes restricted to complexes is
  `Hom(K, -)` followed by the quotient.
* `CochainComplex.homHomotopyFunctorLift`: the descent of `Hom(K, -)` along the quotient by
  homotopy, which `CategoryTheory.Quotient.liftCommShift` equips with a `CommShift`.
* `CochainComplex.homHomotopyFunctorLiftIso`: that descent is the functor of Tag 09LE on homotopy
  categories.
* `CochainComplex.derivedHomFunctorCommShift`: the `CommShift ℤ` of Tag 09LK's functor
  `R Hom(K, -)`.

## Main results

* `CochainComplex.homHomotopyFunctorCommShift` and
  `CochainComplex.homToDerivedCategoryCommShift`: the functor being derived commutes with the
  translation, before and after the localization.
* `CochainComplex.natTrans_commShift_derivedHomFunctorUnit`: the canonical comparison
  `Hom(K, -) ⟶ Qh ⋙ R Hom(K, -)` is compatible with the translation.

## What is not included

`CategoryTheory.Functor.IsTriangulated`, at either level. Both are proved elsewhere, and the
`CategoryTheory.Functor.CommShift` of `CochainComplex.homHomotopyFunctorLift` built here is the
input that makes the first of them reachable.

`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomExactness.lean` proves
`CategoryTheory.Functor.IsTriangulated` for the functor being derived, which is unconditional.
Preservation of distinguished triangles is
`CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`, stated for a presentation of
the triangle by a degreewise split short exact sequence; turning it into `map_distinguished` means
identifying the third arrow of `mapTriangle`, which is formed with the degree-one component of
the `CommShift` *of the homotopy-level functor* — that is, with the comparison above transported
along `CochainComplex.homHomotopyFunctorLiftIso`, which is not the identity. That is why the
statement is proved for `CochainComplex.homHomotopyFunctorLift` and transported: the descent
carries `CategoryTheory.Quotient.liftCommShift`, whose components
`CategoryTheory.Quotient.LiftCommShift.iso_hom_app` pins down.

`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomDerivedTriangulated.lean` proves it for
`CochainComplex.derivedHomFunctor`, under Tag 09LK's own hypothesis that the right derived
functor is defined everywhere and no other. It does not go through
`CategoryTheory.Functor.isTriangulated_of_leftExtension`, whose hypothesis — for every morphism
of `D(A)` a distinguished triangle of `K(A)` lifting it *at whose three vertices the unit
`CochainComplex.derivedHomFunctorUnit` is invertible* — everywhere-definedness does not supply;
it goes through `CategoryTheory.Functor.isTriangulated_of_isRightDerivable`, where the triangle
used is the triangle of values of Tag 05SC.

## Implementation notes

The identification of the descent with `CochainComplex.homHomotopyFunctor` is obtained by
cancelling the fully faithful comparison
`DifferentialGradedModule.homotopyCategoryEquivalence` on the right: after that cancellation the
two routes from complexes to the homotopy category of the differential graded category of
differential graded modules are *equal*, which is
`CochainComplex.homotopyFunctor_quotient_eq`, proved by `rfl`.

Two instances are stated by `inferInstanceAs` only to change the spelling of the endomorphism
algebra: `CochainComplex.endAlgebra` is the algebra of
`DGCategory.homRepresentation`, which is definitionally but not reducibly
`DGCategory.endAlgebra`, and instance search sees only the latter in the type of
`CochainComplex.homComplexesFunctor`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK); [Tag
  09LE](https://stacks.math.columbia.edu/tag/09LE) for the shift comparison; [Tag
  09L9](https://stacks.math.columbia.edu/tag/09L9) and [Tag
  09LC](https://stacks.math.columbia.edu/tag/09LC) for the two comparisons of homotopy
  categories.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CochainComplex

open CochainComplex.HomComplex DifferentialGradedModule

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)

/-- **The two routes from complexes to the homotopy category of the differential graded category
of differential graded `E`-modules agree.** On the one side a complex is sent to its homotopy
class and then by the functor of Tag 09LE on homotopy classes; on the other it is sent to
`Hom(K, X)`, then to its homotopy class, and then along the comparison of Tag 09LC. Both are the
homotopy class of `Hom(K, -)` applied to a cochain map, so the two functors are equal. -/
theorem homotopyFunctor_quotient_eq :
    HomotopyCategory.quotient B (.up ℤ) ⋙ (homotopyCategoryEquivalence B).functor ⋙
        (DGCategory.representableDGFunctor (dgCategory B) K).onK =
      homComplexesFunctor B K ⋙ DifferentialGradedModule.toHomotopyCategory (endAlgebra B K) ⋙
        (DifferentialGradedModule.homotopyCategoryEquivalence (endAlgebra B K)).functor :=
  rfl

/-- The route through the differential graded category, restricted to complexes: a complex is
sent to its homotopy class and then to the homotopy class of `Hom(K, -)` in the homotopy category
of the differential graded category of differential graded `E`-modules. -/
noncomputable abbrev homComplexesViaDG :
    CochainComplex B ℤ ⥤ (DifferentialGradedModule.dgCategory (endAlgebra B K)).K :=
  HomotopyCategory.quotient B (.up ℤ) ⋙ (homotopyCategoryEquivalence B).functor ⋙
    (DGCategory.representableDGFunctor (dgCategory B) K).onK

/-- **The functor of Tag 09LE on homotopy categories, restricted to complexes, is `Hom(K, -)`
followed by the quotient by homotopy.** This is the previous equality with the comparison
`DifferentialGradedModule.homotopyCategoryEquivalence` cancelled on the right. -/
noncomputable def homHomotopyFunctorQuotientIso :
    HomotopyCategory.quotient B (.up ℤ) ⋙ homHomotopyFunctor B K ≅
      homComplexesFunctor B K ⋙ DifferentialGradedModule.toHomotopyCategory (endAlgebra B K) :=
  Functor.fullyFaithfulCancelRight
    (DifferentialGradedModule.homotopyCategoryEquivalence (endAlgebra B K)).functor
    (Functor.isoWhiskerLeft (homComplexesViaDG B K)
        (DifferentialGradedModule.homotopyCategoryEquivalence (endAlgebra B K)).counitIso ≪≫
      (homComplexesViaDG B K).rightUnitor ≪≫ eqToIso (homotopyFunctor_quotient_eq B K))

/-- `Hom(K, -)` carries homotopic chain maps to homotopic homomorphisms of differential graded
modules: this is read off the comparison, since the two maps already have the same homotopy class
in `K(B)`. -/
theorem homComplexesFunctor_toHomotopyCategory_map_eq_of_homotopic
    (X Y : CochainComplex B ℤ) (f₁ f₂ : X ⟶ Y) (h : homotopic B (.up ℤ) f₁ f₂) :
    (homComplexesFunctor B K ⋙
          DifferentialGradedModule.toHomotopyCategory (endAlgebra B K)).map f₁ =
      (homComplexesFunctor B K ⋙
        DifferentialGradedModule.toHomotopyCategory (endAlgebra B K)).map f₂ := by
  have hq : (HomotopyCategory.quotient B (.up ℤ) ⋙ homHomotopyFunctor B K).map f₁ =
      (HomotopyCategory.quotient B (.up ℤ) ⋙ homHomotopyFunctor B K).map f₂ :=
    congrArg (homHomotopyFunctor B K).map (CategoryTheory.Quotient.sound _ h)
  have key : (homHomotopyFunctorQuotientIso B K).hom.app X ≫
        (homComplexesFunctor B K ⋙
          DifferentialGradedModule.toHomotopyCategory (endAlgebra B K)).map f₁ =
      (homHomotopyFunctorQuotientIso B K).hom.app X ≫
        (homComplexesFunctor B K ⋙
          DifferentialGradedModule.toHomotopyCategory (endAlgebra B K)).map f₂ := by
    rw [← (homHomotopyFunctorQuotientIso B K).hom.naturality f₁,
      ← (homHomotopyFunctorQuotientIso B K).hom.naturality f₂, hq]
  exact (Iso.cancel_iso_hom_left ((homHomotopyFunctorQuotientIso B K).app X) _ _).mp key

/-- `Hom(K, -)` followed by the quotient to the homotopy category commutes with the translation.
The statement is the one the descent along the quotient needs, with the endomorphism algebra
spelled as in `CochainComplex.homHomotopyFunctor`. -/
noncomputable instance homComplexesToHomotopyCommShift :
    (homComplexesFunctor B K ⋙
      DifferentialGradedModule.toHomotopyCategory (endAlgebra B K)).CommShift ℤ :=
  inferInstanceAs ((homComplexesFunctor B K ⋙
    DifferentialGradedModule.toHomotopyCategory
      (DGCategory.endAlgebra (dgCategory B) K)).CommShift ℤ)

/-- `Hom(K, -) : K(B) ⥤ K(E, d)` as the descent of `Hom(K, -)` along the quotient by homotopy. -/
noncomputable abbrev homHomotopyFunctorLift :
    HomotopyCategory B (.up ℤ) ⥤
      DifferentialGradedModule.HomotopyCategory (endAlgebra B K) :=
  CategoryTheory.Quotient.lift (homotopic B (.up ℤ))
    (homComplexesFunctor B K ⋙ DifferentialGradedModule.toHomotopyCategory (endAlgebra B K))
    (homComplexesFunctor_toHomotopyCategory_map_eq_of_homotopic B K)

/-- The descent commutes with the translation, by `CategoryTheory.Quotient.liftCommShift`. -/
noncomputable instance homHomotopyFunctorLiftCommShift :
    (homHomotopyFunctorLift B K).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift _ (homotopic B (.up ℤ)) ℤ
    (homComplexesFunctor_toHomotopyCategory_map_eq_of_homotopic B K)

/-- The descent agrees with the functor of Tag 09LE on homotopy categories. -/
noncomputable def homHomotopyFunctorLiftIso :
    homHomotopyFunctorLift B K ≅ homHomotopyFunctor B K :=
  CategoryTheory.Quotient.natIsoLift _
    (CategoryTheory.Quotient.lift.isLift _ _ _ ≪≫ (homHomotopyFunctorQuotientIso B K).symm)

/-- **`Hom(K, -) : K(B) ⥤ K(E, d)` commutes with the translation.** -/
@[stacks 09LK "the differential graded Hom functor Hom(K, -) : K(B) ⥤ K(E, d) commutes with the \
translation, the shift comparisons of 09LE descending along the quotient by homotopy"]
noncomputable instance homHomotopyFunctorCommShift :
    (homHomotopyFunctor B K).CommShift ℤ :=
  Functor.CommShift.ofIso (homHomotopyFunctorLiftIso B K) ℤ

/-- **The functor being right derived in Tag 09LK commutes with the translation.** -/
@[stacks 09LK "the functor Hom(K, -) : K(B) ⥤ D(E, d) being right derived commutes with the \
translation"]
noncomputable instance homToDerivedCategoryCommShift :
    (homToDerivedCategory B K).CommShift ℤ :=
  inferInstanceAs ((homHomotopyFunctor B K ⋙
    (DifferentialGradedModule.quasiIsomorphisms' (endAlgebra B K)).Q).CommShift ℤ)

end CochainComplex

namespace CochainComplex

universe w'

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ)

/-- **Tag 09LK's functor commutes with the translation, under a hypothesis stronger than the
source's.** The right derived functor
The right derived functor `R Hom(K, -) : D(A) ⥤ D(E, d)` inherits the commutation with the
translation from the functor being derived, by Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`, and the canonical comparison `Hom(K, -)
⟶ Qh ⋙ R Hom(K, -)` is compatible with it.

This is NOT tagged, deliberately. Tag 09LK assumes that the right derived functor of the
`D(Ab)`-valued `Hom(K, -) : K(A) ⤥ D(Ab)` is everywhere defined; this declaration assumes it of
the `D(E, d)`-valued functor. The latter implies the former,
`CochainComplex.isRightDerivable_homToDerivedCategoryForget`; the converse is
`CochainComplex.ReflectsHomDerivability`, which this development neither proves nor refutes, so
the hypothesis used here is not known to be the source's. That converse asks for reflection of
essential constancy of an ind-object along the forgetful functor `D(E, d) ⤥ D(Ab)`. It holds
along a functor that is full and faithful with idempotent-complete source,
`CategoryTheory.Functor.IsRightDerivable.of_comp`, and the forgetful functor is neither full nor
faithful; it fails for some conservative functors,
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero`, but that
functor is not the forgetful functor of a differential graded algebra and is neither additive nor
exact, so it refutes the general lemma and not this instance. Deriving the `D(E, d)`-valued
functor is also the step the Stacks Project's own proof of 09LK takes. A registration may sit
only on a declaration that proves its tag under the source's own hypotheses, so this one carries
no attribute.
-/
@[instance_reducible]
noncomputable def derivedHomFunctorCommShift
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomFunctor A K h).CommShift ℤ :=
  haveI := hasRightDerivedFunctor_homToDerivedCategory A K h
  haveI := derivedHomFunctor_isRightDerivedFunctor A K h
  Functor.IsRightDerivedFunctor.commShift (derivedHomFunctor A K h)
    (derivedHomFunctorUnit A K h) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ

/-- The canonical comparison of Tag 09LK is compatible with the translation. -/
theorem natTrans_commShift_derivedHomFunctorUnit
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    letI := derivedHomFunctorCommShift A K h
    NatTrans.CommShift (derivedHomFunctorUnit A K h) ℤ :=
  haveI := hasRightDerivedFunctor_homToDerivedCategory A K h
  haveI := derivedHomFunctor_isRightDerivedFunctor A K h
  Functor.IsRightDerivedFunctor.natTrans_commShift (derivedHomFunctor A K h)
    (derivedHomFunctorUnit A K h) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ

end CochainComplex
