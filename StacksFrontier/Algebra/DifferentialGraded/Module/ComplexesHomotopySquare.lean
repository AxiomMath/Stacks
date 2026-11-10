module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryHomotopyCategory

/-!
# The quotient square of differential graded modules and their differential graded category

Let `A` be a differential graded algebra over a commutative ring `R`. There are two routes from
the category of complexes of the differential graded category `Mod^dg(A)` to the homotopy
category `K(Mod^dg(A))`:

* through the ordinary categories: read a closed degree-zero homogeneous map as a homomorphism of
  differential graded modules (`DifferentialGradedModule.dgCategoryCompEquivalence`), pass to the
  ordinary homotopy category of differential graded modules
  (`DifferentialGradedModule.toHomotopyCategory`), and compare that with `K(Mod^dg(A))` by
  `DifferentialGradedModule.homotopyCategoryEquivalence`;
* directly, by `DGCategory.compToK`.

This file proves that the two agree. The comparison is an *equality* of functors in the direction
in which the comparison of homotopy categories appears covariantly, since both composites are the
identity on objects and send a closed degree-zero morphism to its own homotopy class; the two
isomorphisms obtained from it by moving the comparison to the other side across its unit and
counit are recorded as well.

The second of those, `DifferentialGradedModule.complexesQuotientSquareIso`, is the only usable
description of `(homotopyCategoryEquivalence A).inverse` on the image of `DGCategory.compToK`:
that inverse is the one manufactured by `CategoryTheory.Functor.asEquivalence`, whose action on
objects goes through `Exists.choose` and therefore computes on nothing.

## Main results

* `DifferentialGradedModule.complexesHomotopySquare`: **the square commutes**, as an equality of
  functors `Comp(Mod^dg(A)) ⥤ K(Mod^dg(A))`.
* `DifferentialGradedModule.modulesHomotopySquareIso` and
  `DifferentialGradedModule.complexesQuotientSquareIso`: the two isomorphisms obtained from it by
  transposing one of the two comparison equivalences.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]

/-- Homotopy classes of closed degree-zero morphisms between equal objects, with equal underlying
maps, are equal. The statement is heterogeneous because the two classes live in the morphism types
of possibly distinct pairs of objects, which is the shape `CategoryTheory.Functor.hext` leaves
behind. -/
private theorem cocycleClass_heq {A : DifferentialGradedAlgebra.{u, u} R}
    {L M L' M' : DifferentialGradedModule.{u, u, u} A} (hL : L = L') (hM : M = M')
    (f : (dgCategory.{u, u, u} A).Cocycle L M) (g : (dgCategory.{u, u, u} A).Cocycle L' M')
    (h : HEq f.1.1 g.1.1) :
    HEq (Quotient.mk _ f : (dgCategory.{u, u, u} A).HomotopyClass L M)
      (Quotient.mk _ g : (dgCategory.{u, u, u} A).HomotopyClass L' M') := by
  subst L'
  subst M'
  exact heq_of_eq (congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext (eq_of_heq h))))

/-- **The quotient square commutes.** Reading a closed degree-zero homogeneous morphism as a
homomorphism of differential graded modules, passing to the ordinary homotopy category and
comparing with the homotopy category of the differential graded category is the canonical functor
`Comp(Mod^dg(A)) ⥤ K(Mod^dg(A))`. Both composites are the identity on objects and send a morphism
to its own homotopy class, so this is an equality of functors and not merely an isomorphism. -/
theorem complexesHomotopySquare (A : DifferentialGradedAlgebra.{u, u} R) :
    (dgCategoryCompEquivalence A).1.functor ⋙ toHomotopyCategory A ⋙
        (homotopyCategoryEquivalence A).functor =
      DGCategory.compToK (dgCategory.{u, u, u} A) := by
  apply Functor.hext
  · intro X
    change (homotopyCategoryEquivalence A).functor.obj
      ((toHomotopyCategory A).obj ((dgCategoryCompEquivalence A).1.functor.obj X)) = X
    rw [homotopyCategoryEquivalence_obj, (dgCategoryCompEquivalence A).2.1]
  · intro X Y f
    let E := (dgCategoryCompEquivalence A).1
    obtain ⟨c, hc, hq⟩ := homotopyCategoryHomEquiv_map A
      (E.functor.obj X) (E.functor.obj Y) (E.functor.map f)
    have hmap := homotopyCategoryEquivalence_map A (E.functor.obj X) (E.functor.obj Y)
      ((toHomotopyCategory A).map (E.functor.map f))
    exact hmap.trans ((heq_of_eq hq).trans
      (cocycleClass_heq ((dgCategoryCompEquivalence A).2.1 X)
        ((dgCategoryCompEquivalence A).2.1 Y) c f
        ((heq_of_eq hc).trans ((dgCategoryCompEquivalence A).2.2 X Y f))))

/-- **The square with the comparison of categories of complexes transposed.** Passing from
differential graded modules to the homotopy category of the differential graded category is
reading a homomorphism as a closed degree-zero morphism and taking its homotopy class. -/
def modulesHomotopySquareIso (A : DifferentialGradedAlgebra.{u, u} R) :
    toHomotopyCategory A ⋙ (homotopyCategoryEquivalence A).functor ≅
      (dgCategoryCompEquivalence A).1.inverse ⋙ DGCategory.compToK (dgCategory.{u, u, u} A) :=
  let E := (dgCategoryCompEquivalence A).1
  let Q := toHomotopyCategory A ⋙ (homotopyCategoryEquivalence A).functor
  (Functor.leftUnitor Q).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm Q ≪≫
    Functor.associator E.inverse E.functor Q ≪≫
    Functor.isoWhiskerLeft E.inverse (eqToIso (complexesHomotopySquare A))

/-- **The square with the comparison of homotopy categories transposed.** This is the description
of `(DifferentialGradedModule.homotopyCategoryEquivalence A).inverse` restricted along
`DGCategory.compToK`: on a closed degree-zero morphism it is the homotopy class of the
corresponding homomorphism of differential graded modules. Since that inverse is the one
`CategoryTheory.Functor.asEquivalence` manufactures from essential surjectivity, nothing else
describes it. -/
def complexesQuotientSquareIso (A : DifferentialGradedAlgebra.{u, u} R) :
    (dgCategoryCompEquivalence A).1.functor ⋙ toHomotopyCategory A ≅
      DGCategory.compToK (dgCategory.{u, u, u} A) ⋙ (homotopyCategoryEquivalence A).inverse :=
  let E := homotopyCategoryEquivalence A
  let F := (dgCategoryCompEquivalence A).1.functor ⋙ toHomotopyCategory A
  (Functor.rightUnitor F).symm ≪≫ Functor.isoWhiskerLeft F E.unitIso ≪≫
    (Functor.associator F E.functor E.inverse).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (complexesHomotopySquare A)) E.inverse

end DifferentialGradedModule

end
