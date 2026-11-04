module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# `R Hom(K, -)` is exact as a functor of triangulated categories

Let `K` be a cochain complex in an abelian category `A` with a chosen derived category and let
`E = End(K)`. Tag 09LK's functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of
`CochainComplex.derivedHomFunctor` commutes with the translation,
`CochainComplex.derivedHomFunctorCommShift`, and the functor being derived is exact,
`CochainComplex.homToDerivedCategory_isTriangulated`. Exactness of the derived functor itself is
reached here, under the hypothesis that the right derived functor of the `D(E, d)`-valued
`Hom(K, -)` is defined everywhere, which is stronger than the source's (see the docstring of
`CochainComplex.derivedHomFunctor_isTriangulated`).

## Main results

* `CochainComplex.derivedHomFunctor_isTriangulated`:
  **`R Hom(K, -) : D(A) ⥤ D(E, d)` is exact** as a functor of triangulated categories, whenever
  the right derived functor of `Hom(K, -)` is defined at every object of `K(A)`.
* `CochainComplex.exists_isKInjective_qh_iso`: every object of `D(A)` is isomorphic to the image
  of a K-injective complex, when K-injective resolutions exist.

## Implementation notes

*Where exactness comes from.* Mathlib's
`CategoryTheory.Functor.isTriangulated_of_leftExtension` would make a left extension exact given
that the functor being extended is exact, which is
`CochainComplex.homToDerivedCategory_isTriangulated`, together with one more thing: for every
morphism `φ` of `D(A)` a distinguished triangle of `K(A)` whose first arrow becomes `φ` and at
whose three vertices the canonical comparison `CochainComplex.derivedHomFunctorUnit` is
invertible. Everywhere-definedness supplies no such triangle: being defined at an object says
that an ind-object is essentially constant, which says nothing about where the comparison is
invertible. So that route is not the one taken.

What is used instead is `CategoryTheory.Functor.isTriangulated_of_isRightDerivable`, the
everywhere-defined case of Tag 05SE: there the triangle of *values* of Tag 05SC is distinguished
for every distinguished triangle of `K(A)`, the three morphisms of values are the images of the
morphisms of the triangle because the characterisation of Tag 05SA determines them, and exactness
descends from `K(A)` to `D(A)` because the localization functor is exact and essentially
surjective on arrows. It needs of the class of quasi-isomorphisms that it be a saturated
multiplicative system compatible with the triangulation, which is Tag 05RT,
`HomotopyCategory.isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq`, together with
`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`.

*The K-injective statement.* `CochainComplex.exists_isKInjective_qh_iso` records, for a category
in which K-injective resolutions exist, that every object of `D(A)` is the image of a K-injective
complex; the localization is essentially surjective and the homotopy quotient is surjective on
objects, and the complex so obtained maps quasi-isomorphically to a K-injective one. It is not
needed for the exactness above.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose exactness clause
  this completes; [Tag 05SE](https://stacks.math.columbia.edu/tag/05SE) for the exactness of a
  right derived functor and [Tag 05RT](https://stacks.math.columbia.edu/tag/05RT) for the
  quasi-isomorphisms of `K(A)` being a saturated multiplicative system.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w' u

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]

/-- **Every object of `D(A)` is isomorphic to the image of a K-injective complex**, when every
complex admits a quasi-isomorphism towards a K-injective one. The object is the image of a
complex, because the localization is essentially surjective and the homotopy quotient is
surjective on objects, and that complex maps quasi-isomorphically to a K-injective one. -/
theorem exists_isKInjective_qh_iso
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧
      Nonempty (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≅ X) := by
  obtain ⟨L, hL⟩ := _root_.HomotopyCategory.quotient_obj_surjective
    (DerivedCategory.Qh.objPreimage X)
  obtain ⟨I, q, hI, hq⟩ := hres L
  exact ⟨I, hI, ⟨(Localization.isoOfHom DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq)).symm ≪≫
    eqToIso (congrArg DerivedCategory.Qh.obj hL) ≪≫ DerivedCategory.Qh.objObjPreimageIso X⟩⟩

variable (K : CochainComplex A ℤ)

/-- **The exactness of the functor of Stacks 09LK, under a hypothesis stronger than the
source's.** Tag 09LK's functor `R Hom(K, -) : D(A) ⥤ D(E, d)` is exact as a functor of
triangulated categories, under the hypothesis that the right derived functor of the
`D(E, d)`-valued `Hom(K, -)` is defined at every object of `K(A)`.

Both halves of exactness of the functor being derived are available unconditionally — the
commutation with the translation is `CochainComplex.homToDerivedCategoryCommShift` and the
preservation of distinguished triangles is `CochainComplex.homToDerivedCategory_isTriangulated` —
and the derived functor inherits the commutation with the translation by
`CochainComplex.derivedHomFunctorCommShift`. Exactness of the derived functor is then the
everywhere-defined case of Tag 05SE, `CategoryTheory.Functor.isTriangulated_of_isRightDerivable`,
applied to the class of quasi-isomorphisms of `K(A)`, which is a saturated multiplicative system
compatible with the triangulation by Tag 05RT.

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
@[sga "4 XVII 1.2.2" "(ii), special case"]
theorem derivedHomFunctor_isTriangulated
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    letI := derivedHomFunctorCommShift A K h
    (derivedHomFunctor A K h).IsTriangulated := by
  have : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsCompatibleWithTriangulation := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  have := hasRightDerivedFunctor_homToDerivedCategory A K h
  let _ := derivedHomFunctorCommShift A K h
  have := derivedHomFunctor_isRightDerivedFunctor A K h
  have := natTrans_commShift_derivedHomFunctorUnit A K h
  exact Functor.isTriangulated_of_isRightDerivable (homToDerivedCategory A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomFunctor A K h) (derivedHomFunctorUnit A K h)
    (HomotopyCategory.isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq
      (DerivedCategory.Qh (C := A))).2.1.1 h

end CochainComplex

end
