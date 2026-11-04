module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionDescent
public import StacksCore.Tactic.StacksAttribute

/-! # Tag 09LC is natural in the bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`. Tag 09LC
identifies, for a differential graded `(A, B)`-bimodule `N`, the degree-zero cohomology of the
internal hom out of `N` with the morphism module of the homotopy category,

`H^0(Hom^•_B(N, P)) = Hom_{K(B, d)}(N, P)`,

and `DifferentialGradedModule.homCohomologyZeroNatIso` is that identification as an isomorphism
of functors of `P`. This file proves that it is also natural in `N`: precomposition with a
homomorphism `f : M ⟶ N` of bimodules (`DifferentialGraded.Bimodule.precompHomotopyNatTrans`,
the underived half of Tag 0BYV) corresponds to precomposition with `f` on the morphism modules of
`K(B, d)`.

That naturality is one of the two inputs to the assertion of Tag 0CS5 that the identification of
the cohomology of derived Hom with Ext is compatible with the contravariant functoriality of
Tag 0BYV.

## Main definitions

* `DifferentialGraded.Bimodule.coyonedaPrecompHomotopyCategory`: precomposition with `f` on the
  co-Yoneda functors of `K(B, d)`.

## Main results

* `DifferentialGraded.Bimodule.homCohomologyZeroNatIso_precompHomotopyNatTrans`: **Tag 09LC is
  natural in the bimodule.**
* `DifferentialGraded.Bimodule.homOfCocycle_cocyclesEquiv_gradedCocyclesMap_precomp`: the
  computation it rests on — the homomorphism `M ⟶ P` attached to the image of a degree-zero
  cocycle of `Hom^•_B(N, P)` under precomposition is `f` followed by the homomorphism attached to
  the cocycle.

## Implementation notes

The shape of the argument mirrors
`StacksFrontier/Algebra/DifferentialGraded/Module/InternalHomCohomology.lean`, where the same
identification is proved natural in the target: the whole map is computed on a representative
cocycle, so that the square to be checked becomes an identity between two homomorphisms of
differential graded modules, and the statement on `K(B, d)` is then obtained from the statement on
differential graded modules by `CategoryTheory.Quotient.natTrans_ext` — the objects of a quotient
category are those of the original one, so a natural transformation on `K(B, d)` is determined by
its components at differential graded modules.

Between the two there is one step the naturality in the target did not need: the component of
`DifferentialGraded.Bimodule.precompHomotopyNatTrans` is defined through the opaque inverse of
`DifferentialGradedModule.homotopyCategoryEquivalence`, so it has to be traded for the component
of `DifferentialGraded.Bimodule.precompModuleNatTrans` on differential graded modules. That is
`DifferentialGraded.Bimodule.homHomotopyDescent_precompHomotopyNatTrans`. The remaining two of the
four squares making up the restricted identification are naturality squares of
`DifferentialGradedModule.degreeZeroCohomologyOnHomotopyIso'` and
`DifferentialGradedModule.gradedCohomologyFunctorIso` and need nothing specific.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
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

/-- Precomposition with a homomorphism of differential graded `(A, B)`-bimodules, on the
`R`-linear co-Yoneda functors of the homotopy category `K(B, d)`. -/
def coyonedaPrecompHomotopyCategory (f : M ⟶ N) :
    (linearCoyoneda R (HomotopyCategory B)).obj
        (Opposite.op ((toHomotopyCategory B).obj N.rightModule)) ⟶
      (linearCoyoneda R (HomotopyCategory B)).obj
        (Opposite.op ((toHomotopyCategory B).obj M.rightModule)) :=
  (linearCoyoneda R (HomotopyCategory B)).map ((toHomotopyCategory B).map f.rightHom).op

/-- **Tag 09LC is natural in the bimodule, on a representative.** The homomorphism `M ⟶ P`
attached to the image of a degree-zero cocycle of `Hom^•_B(N, P)` under precomposition with `f` is
`f` followed by the homomorphism `N ⟶ P` attached to the cocycle. -/
theorem homOfCocycle_cocyclesEquiv_gradedCocyclesMap_precomp (f : M ⟶ N)
    (P : DifferentialGradedModule B)
    (c : ((homModuleFunctor A B N.rightModule N.leftAction).obj P).gradedCocycles 0) :
    homOfCocycle B ((homPresentation M P).cocyclesEquiv 0
        (gradedCocyclesMap ((precompModuleNatTrans f).app P) 0 c)) =
      (f.rightHom ≫ homOfCocycle B ((homPresentation N P).cocyclesEquiv 0 c) :
        M.rightModule ⟶ P) := by
  apply DifferentialGradedModule.Hom.ext
  have hval := precompModuleNatTrans_homogeneousEquiv f P 0 (c : _)
  show ((homPresentation M P).homogeneousEquiv 0
      (((precompModuleNatTrans f).app P).gradedMap 0 (c : _))).1 = _
  rw [hval]
  rfl

/-- **Tag 09LC is natural in the bimodule, on differential graded modules.** -/
theorem homCohomologyZeroFunctorIso_precompModuleNatTrans (f : M ⟶ N) :
    Functor.whiskerRight (precompModuleNatTrans f) (gradedCohomologyFunctor A 0) ≫
        (homCohomologyZeroFunctorIso A B M.rightModule M.leftAction).hom =
      (homCohomologyZeroFunctorIso A B N.rightModule N.leftAction).hom ≫
        Functor.whiskerLeft (toHomotopyCategory B) (coyonedaPrecompHomotopyCategory f) := by
  ext P : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    show (toHomotopyCategory B).map (homOfCocycle B
        ((homPresentation M P).cocyclesEquiv 0
          (gradedCocyclesMap ((precompModuleNatTrans f).app P) 0 c))) =
      (toHomotopyCategory B).map f.rightHom ≫ (toHomotopyCategory B).map
        (homOfCocycle B ((homPresentation N P).cocyclesEquiv 0 c))
    rw [homOfCocycle_cocyclesEquiv_gradedCocyclesMap_precomp, Functor.map_comp]

/-- **Tag 09LC is natural in the bimodule, restricted to differential graded modules.** The four
squares composed here are: the descent identification of precomposition
(`DifferentialGraded.Bimodule.homHomotopyDescent_precompHomotopyNatTrans`), the naturality of
`DifferentialGradedModule.degreeZeroCohomologyOnHomotopyIso'` and of
`DifferentialGradedModule.gradedCohomologyFunctorIso`, and the identification on differential
graded modules. -/
theorem homCohomologyZeroRestrictedIso_precompHomotopyNatTrans (f : M ⟶ N)
    (P : DifferentialGradedModule B) :
    (degreeZeroCohomologyOnHomotopy' A).map
          ((precompHomotopyNatTrans f).app ((toHomotopyCategory B).obj P)) ≫
        (homCohomologyZeroRestrictedIso A B M.rightModule M.leftAction).hom.app P =
      (homCohomologyZeroRestrictedIso A B N.rightModule N.leftAction).hom.app P ≫
        (coyonedaPrecompHomotopyCategory f).app ((toHomotopyCategory B).obj P) := by
  have h4 := NatTrans.congr_app (homCohomologyZeroFunctorIso_precompModuleNatTrans f) P
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h4
  have h3 := (gradedCohomologyFunctorIso A 0).hom.naturality ((precompModuleNatTrans f).app P)
  have h2 := (degreeZeroCohomologyOnHomotopyIso' A).hom.naturality
    ((precompModuleNatTrans f).app P)
  have h1 : (degreeZeroCohomologyOnHomotopy' A).map
        ((precompHomotopyNatTrans f).app ((toHomotopyCategory B).obj P)) ≫
      (degreeZeroCohomologyOnHomotopy' A).map
        ((homHomotopyDescent M.rightModule M.leftAction).hom.app P) =
      (degreeZeroCohomologyOnHomotopy' A).map
        ((homHomotopyDescent N.rightModule N.leftAction).hom.app P) ≫
      (degreeZeroCohomologyOnHomotopy' A).map
        ((toHomotopyCategory A).map ((precompModuleNatTrans f).app P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, homHomotopyDescent_precompHomotopyNatTrans]
  simp only [homCohomologyZeroRestrictedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc
      ((degreeZeroCohomologyOnHomotopy' A).map
        ((toHomotopyCategory A).map ((precompModuleNatTrans f).app P))),
    show (degreeZeroCohomologyOnHomotopy' A).map
        ((toHomotopyCategory A).map ((precompModuleNatTrans f).app P)) ≫
        (degreeZeroCohomologyOnHomotopyIso' A).hom.app
          ((homModuleFunctor A B M.rightModule M.leftAction).obj P) = _ from h2,
    Category.assoc, ← Category.assoc
      ((forgetToCochainComplex A ⋙ HomologicalComplex.homologyFunctor
        (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map ((precompModuleNatTrans f).app P)),
    h3, Category.assoc, h4]

/-- **Tag 09LC is natural in the bimodule.** The identification of the degree-zero cohomology of
the internal hom with the morphism module of `K(B, d)` carries precomposition with a homomorphism
of differential graded `(A, B)`-bimodules, the underived half of Tag 0BYV, to precomposition on
the morphism modules.

This is one of the two naturality statements behind the compatibility of Tag 0CS5 with Tag 0BYV. -/
theorem homCohomologyZeroNatIso_precompHomotopyNatTrans (f : M ⟶ N) :
    Functor.whiskerRight (precompHomotopyNatTrans f) (degreeZeroCohomologyOnHomotopy' A) ≫
        (homCohomologyZeroNatIso A B M.rightModule M.leftAction).hom =
      (homCohomologyZeroNatIso A B N.rightModule N.leftAction).hom ≫
        coyonedaPrecompHomotopyCategory f := by
  refine CategoryTheory.Quotient.natTrans_ext _ _ ?_
  ext P : 2
  exact homCohomologyZeroRestrictedIso_precompHomotopyNatTrans f P

end DifferentialGraded.Bimodule

end
