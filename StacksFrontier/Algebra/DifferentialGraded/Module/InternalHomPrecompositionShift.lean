module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionDescent
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomShiftFunctor
public import StacksCore.Tactic.StacksAttribute

/-! # Tag 0FQR is natural in the bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`. Tag 0FQR
gives, for a differential graded `(A, B)`-bimodule `N` and each `k`, a sign-free isomorphism
`Hom^•_B(N, P)[k] ≅ Hom^•_B(N, P[k])`, and
`DifferentialGradedModule.homHomotopyCategoryFunctorShiftIso` is that isomorphism as an
isomorphism of functors on `K(B, d)`. This file proves that it is also natural in `N`:
precomposition with a homomorphism `f : M ⟶ N` of bimodules
(`DifferentialGraded.Bimodule.precompHomotopyNatTrans`, the underived half of Tag 0BYV) commutes
with it.

That naturality is one of the two inputs to the assertion of Tag 0CS5 that the identification of
the cohomology of derived Hom with Ext is compatible with the contravariant functoriality of
Tag 0BYV.

## Main results

* `DifferentialGraded.Bimodule.homHomotopyCategoryFunctorShiftIso_precompHomotopyNatTrans`:
  **Tag 0FQR is natural in the bimodule.**
* `DifferentialGraded.Bimodule.homPresentationShiftIso_precompModuleNatTrans`: the computation it
  rests on, at the level of presentations of the internal hom.

## Implementation notes

The shape of the argument mirrors
`DifferentialGradedModule.homPresentationShiftIso_naturality`, which proves the same isomorphism
natural in the target: the shift comparison is characterized rather than given by a formula
(`DifferentialGradedModule.HomModuleData.IsShiftComparison`), so both composites are evaluated on
a homogeneous element, read through
`DifferentialGradedModule.HomModuleData.homogeneousEquiv`, and compared value by value. Both come
out as the homogeneous map of the element precomposed with `f`, which is what makes the square
commute. Uniqueness of the comparison cannot be used, there as here, because the two sides compare
different pairs of presentations.

The passage to `K(B, d)` is `CategoryTheory.Quotient.natTrans_ext`: the objects of a quotient
category are those of the original one, so it is enough to check the restricted square at a
differential graded module. The restricted square is a composite of five squares, of which three
need nothing specific — the naturality of the two
`CategoryTheory.Functor.commShiftIso`s and of precomposition itself — while the remaining two are
the computation above and the descent identification of precomposition
(`DifferentialGraded.Bimodule.homHomotopyDescent_precompHomotopyNatTrans`, needed in both
directions, since the descent isomorphism occurs once each way in
`DifferentialGradedModule.homHomotopyCategoryFunctorShiftRestrictedIso`).

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV)
* [Stacks Project, Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ)
* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} {M N : Bimodule A B}

/-- **Tag 0FQR is natural in the bimodule, at the level of presentations.** The shift comparison
of Tag 0FQR commutes with precomposition by a homomorphism of differential graded
`(A, B)`-bimodules. -/
theorem homPresentationShiftIso_precompModuleNatTrans (f : M ⟶ N)
    (P : DifferentialGradedModule B) (k : ℤ) :
    (shiftFunctor A k).map ((precompModuleNatTrans f).app P) ≫
        (homPresentationShiftIso A B M.rightModule M.leftAction P k).hom =
      (homPresentationShiftIso A B N.rightModule N.leftAction P k).hom ≫
        (precompModuleNatTrans f).app (shift P k) := by
  refine DifferentialGradedModule.Hom.ext_of_grading fun n g => ?_
  set g' : ((homModuleFunctor A B N.rightModule N.leftAction).obj P).grading (n + k) :=
    ⟨g.1, g.property⟩ with hg'
  set u := (precompModuleNatTrans f).app P with hu
  set v := (precompModuleNatTrans f).app (shift P k) with hv
  set φM := (homPresentationShiftIso A B M.rightModule M.leftAction P k).hom with hφM
  set φN := (homPresentationShiftIso A B N.rightModule N.leftAction P k).hom with hφN
  have hmemL : φM.toFun (u.toFun g.1) ∈
      (homPresentation M (shift P k)).module.grading n :=
    φM.map_grading n _ (u.map_grading (n + k) g.1 g'.property)
  have hmemR : v.toFun (φN.toFun g.1) ∈
      (homPresentation M (shift P k)).module.grading n :=
    v.map_grading n _ (φN.map_grading n g.1 g.property)
  have key : (⟨φM.toFun (u.toFun g.1), hmemL⟩ :
        (homPresentation M (shift P k)).module.grading n) =
      ⟨v.toFun (φN.toFun g.1), hmemR⟩ := by
    apply ((homPresentation M (shift P k)).homogeneousEquiv n).injective
    refine homogeneousMap_ext fun p x => ?_
    have hL : (((homPresentation M (shift P k)).homogeneousEquiv n
          ⟨φM.toFun (u.toFun g.1), hmemL⟩).1 x : P.M) =
        ((homPresentation N P).homogeneousEquiv (n + k) g').1 (f.rightHom.toFun (x : _)) := by
      refine (homPresentationShiftIso_apply A B M.rightModule M.leftAction P k n p
        (u.gradedMap (n + k) g') x).trans ?_
      exact precompModuleNatTrans_homogeneousEquiv_apply f P (n + k) g' (x : _)
    have hR : (((homPresentation M (shift P k)).homogeneousEquiv n
          ⟨v.toFun (φN.toFun g.1), hmemR⟩).1 x : P.M) =
        ((homPresentation N P).homogeneousEquiv (n + k) g').1 (f.rightHom.toFun (x : _)) := by
      refine (precompModuleNatTrans_homogeneousEquiv_apply f (shift P k) n
        ⟨φN.toFun g.1, φN.map_grading n g.1 g.property⟩ (x : _)).trans ?_
      exact homPresentationShiftIso_apply A B N.rightModule N.leftAction P k n p g'
        (f.rightHom.gradedMap p x)
    exact hL.trans hR.symm
  exact congrArg Subtype.val key

/-- **Tag 0FQR is natural in the bimodule, on differential graded modules.** -/
theorem homModuleFunctorShiftIso_precompModuleNatTrans (f : M ⟶ N) (k : ℤ) :
    Functor.whiskerRight (precompModuleNatTrans f)
          (CategoryTheory.shiftFunctor (DifferentialGradedModule A) k) ≫
        (homModuleFunctorShiftIso A B M.rightModule M.leftAction k).hom =
      (homModuleFunctorShiftIso A B N.rightModule N.leftAction k).hom ≫
        Functor.whiskerLeft (CategoryTheory.shiftFunctor (DifferentialGradedModule B) k)
          (precompModuleNatTrans f) := by
  ext P : 2
  exact homPresentationShiftIso_precompModuleNatTrans f P k

/-- **Tag 0FQR is natural in the bimodule, restricted to differential graded modules.** The five
squares composed here are: the descent identification of precomposition in both directions, the
naturality of the two comparison isomorphisms of the quotient functors with the shift, and the
identification on differential graded modules. -/
theorem homHomotopyCategoryFunctorShiftRestrictedIso_precompHomotopyNatTrans (f : M ⟶ N)
    (P : DifferentialGradedModule B) (k : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) k).map
          ((precompHomotopyNatTrans f).app ((toHomotopyCategory B).obj P)) ≫
        (homHomotopyCategoryFunctorShiftRestrictedIso A B M.rightModule M.leftAction
          k).hom.app P =
      (homHomotopyCategoryFunctorShiftRestrictedIso A B N.rightModule N.leftAction
          k).hom.app P ≫
        (precompHomotopyNatTrans f).app
          ((CategoryTheory.shiftFunctor (HomotopyCategory B) k).obj
            ((toHomotopyCategory B).obj P)) := by
  have h1 : (CategoryTheory.shiftFunctor (HomotopyCategory A) k).map
        ((precompHomotopyNatTrans f).app ((toHomotopyCategory B).obj P)) ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory A) k).map
        ((homHomotopyDescent M.rightModule M.leftAction).hom.app P) =
      (CategoryTheory.shiftFunctor (HomotopyCategory A) k).map
        ((homHomotopyDescent N.rightModule N.leftAction).hom.app P) ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory A) k).map
        ((toHomotopyCategory A).map ((precompModuleNatTrans f).app P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, homHomotopyDescent_precompHomotopyNatTrans]
  have h2 : (CategoryTheory.shiftFunctor (HomotopyCategory A) k).map
        ((toHomotopyCategory A).map ((precompModuleNatTrans f).app P)) ≫
      ((toHomotopyCategory A).commShiftIso k).inv.app
        ((homModuleFunctor A B M.rightModule M.leftAction).obj P) =
      ((toHomotopyCategory A).commShiftIso k).inv.app
        ((homModuleFunctor A B N.rightModule N.leftAction).obj P) ≫
      (toHomotopyCategory A).map
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) k).map
          ((precompModuleNatTrans f).app P)) :=
    ((toHomotopyCategory A).commShiftIso k).inv.naturality ((precompModuleNatTrans f).app P)
  have h3 : (toHomotopyCategory A).map
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) k).map
          ((precompModuleNatTrans f).app P)) ≫
      (toHomotopyCategory A).map
        ((homModuleFunctorShiftIso A B M.rightModule M.leftAction k).hom.app P) =
      (toHomotopyCategory A).map
        ((homModuleFunctorShiftIso A B N.rightModule N.leftAction k).hom.app P) ≫
      (toHomotopyCategory A).map ((precompModuleNatTrans f).app
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule B) k).obj P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun t => (toHomotopyCategory A).map t)
      (homPresentationShiftIso_precompModuleNatTrans f P k)
  have h4 := homHomotopyDescent_inv_precompHomotopyNatTrans f
    ((CategoryTheory.shiftFunctor (DifferentialGradedModule B) k).obj P)
  have h5 : (precompHomotopyNatTrans f).app
        ((toHomotopyCategory B).obj
          ((CategoryTheory.shiftFunctor (DifferentialGradedModule B) k).obj P)) ≫
      (homHomotopyCategoryFunctor A B M.rightModule M.leftAction).map
        (((toHomotopyCategory B).commShiftIso k).hom.app P) =
      (homHomotopyCategoryFunctor A B N.rightModule N.leftAction).map
        (((toHomotopyCategory B).commShiftIso k).hom.app P) ≫
      (precompHomotopyNatTrans f).app
        ((CategoryTheory.shiftFunctor (HomotopyCategory B) k).obj
          ((toHomotopyCategory B).obj P)) :=
    ((precompHomotopyNatTrans f).naturality
      (((toHomotopyCategory B).commShiftIso k).hom.app P)).symm
  simp only [homHomotopyCategoryFunctorShiftRestrictedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4, h5]

/-- **Tag 0FQR is natural in the bimodule.** The identification of the shift of the internal hom
with the internal hom of the shift commutes with precomposition by a homomorphism of differential
graded `(A, B)`-bimodules, the underived half of Tag 0BYV.

This is one of the two naturality statements behind the compatibility of Tag 0CS5 with Tag 0BYV. -/
theorem homHomotopyCategoryFunctorShiftIso_precompHomotopyNatTrans (f : M ⟶ N) (k : ℤ) :
    Functor.whiskerRight (precompHomotopyNatTrans f)
          (CategoryTheory.shiftFunctor (HomotopyCategory A) k) ≫
        (homHomotopyCategoryFunctorShiftIso A B M.rightModule M.leftAction k).hom =
      (homHomotopyCategoryFunctorShiftIso A B N.rightModule N.leftAction k).hom ≫
        Functor.whiskerLeft (CategoryTheory.shiftFunctor (HomotopyCategory B) k)
          (precompHomotopyNatTrans f) := by
  refine CategoryTheory.Quotient.natTrans_ext _ _ ?_
  ext P : 2
  exact homHomotopyCategoryFunctorShiftRestrictedIso_precompHomotopyNatTrans f P k

end DifferentialGraded.Bimodule

end
