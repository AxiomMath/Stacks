module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Bijectivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete

/-!
# Bijectivity on étale fundamental groups makes base change essentially surjective

Let `j : U ⟶ X` be a morphism of connected schemes and `ū` a geometric point of `U`. If the
induced continuous homomorphism `π₁(U, ū) ⟶ π₁(X, ū)` of Stacks 0BND is bijective, then every
finite étale cover of `U` is isomorphic to the base change of a finite étale cover of `X`. This is
the Galois-category statement `CategoryTheory.GaloisFunctorData.essSurj_of_bijective` applied to
the base-change functor, through the identification
`AlgebraicGeometry.autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom` of the abstract
automorphism groups with the étale fundamental groups.

## Main results

* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_bijective_etaleFundamentalGroupMap`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-- **A bijection on étale fundamental groups makes base change essentially surjective.** Let
`j : U ⟶ X` be a morphism of connected schemes and `ū` a geometric point of `U`. If
`π₁(U, ū) ⟶ π₁(X, ū)` is bijective, then every finite étale cover of `U` is isomorphic to the base
change of a finite étale cover of `X`. -/
theorem essSurj_finiteEtaleBaseChange_of_bijective_etaleFundamentalGroupMap {U X : Scheme.{u}}
    [ConnectedSpace U] [ConnectedSpace X] (j : U ⟶ X) (u : GeometricPoint U)
    (hbij : Function.Bijective (etaleFundamentalGroupMap j u)) :
    (finiteEtaleBaseChange j).EssSurj := by
  let H := finiteEtaleBaseChange j
  let F := finiteEtaleFiberFintypeFunctor X (u.map j)
  let F' := finiteEtaleFiberFintypeFunctor U u
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso j u
  let d := galoisFunctorDataOfFiberIso F F' H t
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  refine GaloisFunctorData.essSurj_of_bijective F F' H t d ?_
  have hcomp : (autMulEquivEtaleFundamentalGroup X (u.map j)) ∘ d.hom =
      (etaleFundamentalGroupMap j u) ∘ (autMulEquivEtaleFundamentalGroup U u) :=
    funext (autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom j u d)
  refine (Function.Bijective.of_comp_iff'
    (autMulEquivEtaleFundamentalGroup X (u.map j)).bijective _).mp ?_
  rw [hcomp]
  exact hbij.comp (autMulEquivEtaleFundamentalGroup U u).bijective

end AlgebraicGeometry

end
