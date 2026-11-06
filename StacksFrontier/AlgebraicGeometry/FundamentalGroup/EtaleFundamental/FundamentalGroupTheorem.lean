module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.MorphismMapEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory

/-!
# The main theorem on the étale fundamental group

Let `X` be a connected scheme and let `x` be a geometric point of `X`. Stacks Tag 0BND collects
three assertions about `π₁(X, x) = Aut F_x`:

1. the geometric fibre functor `F_x` makes `FÉt_X` equivalent to the category of finite sets with a
   continuous `π₁(X, x)`-action;
2. for a second geometric point `x'` there is an isomorphism `t : F_x ≅ F_{x'}`; conjugation by `t`
   is an isomorphism `π₁(X, x) ≅ π₁(X, x')` of topological groups, compatible with the equivalences
   of (1), and independent of `t` up to an inner automorphism of the target;
3. a morphism `f : X ⟶ Y` of connected schemes induces a continuous homomorphism
   `π₁(X, x) ⟶ π₁(Y, f ∘ x)` for which the square formed by base change `FÉt_Y ⥤ FÉt_X`, the two
   equivalences of (1) and restriction of the action commutes.

Each of the three is available in this library for a fibre functor satisfying the Galois-category
axioms of Stacks Tag 0BMY, and those axioms hold for `F_x` on a connected scheme
(`Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor`, Stacks Tag 0BNB). This file
records the resulting hypothesis-free statements.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleEquivalence` — assertion (1), which is also part (3) of
  Stacks Tag 03VF: finite étale covers of a connected scheme are equivalent to the finite
  continuous `π₁(X, x)`-sets, by an equivalence whose underlying sets are the geometric fibres and
  whose action is evaluation of natural automorphisms.
* `AlgebraicGeometry.nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace` — the opening clause of
  assertion (2): the geometric fibre functors of a connected scheme at two geometric points are
  isomorphic.
* `AlgebraicGeometry.nonempty_etaleFundamentalGroupContinuousMulEquiv` — the existence half of
  assertion (2): the étale fundamental groups of a connected scheme at two geometric points are
  isomorphic as topological groups.
* `AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquiv_action` and
  `AlgebraicGeometry.isInnerConjugate_etaleFundamentalGroupContinuousMulEquiv` — the remaining two
  halves of assertion (2): compatibility with the actions of (1), and independence of the choice of
  `t` up to inner conjugation.
* `AlgebraicGeometry.exists_finiteEtaleEquivalence_mapIso` — the commuting square of assertion (3).
  The induced homomorphism itself is `AlgebraicGeometry.etaleFundamentalGroupMap` and its
  characterisation is `AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection`.

## Implementation notes

The equivalence of (1) and the comparison isomorphism of (3) are produced as data by
`AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory` and
`AlgebraicGeometry.exists_finiteEtaleEquivalenceOfIsGaloisCategory_mapIso`; the statements here
refer to that data rather than re-choosing it, so each proof is the conditional statement with its
instance argument supplied by the Galois-category instance.

Assertion (2) is stated for `AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquiv`, the
transport of fundamental groups along `t` as an isomorphism of *topological* groups, which is the
form Stacks 0BND asserts; its underlying multiplicative equivalence is
`AlgebraicGeometry.etaleFundamentalGroupMulEquiv t` definitionally, which is what
`AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquiv_apply` records.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 03VF](https://stacks.math.columbia.edu/tag/03VF)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
* [Stacks Project, Tag 0BMY](https://stacks.math.columbia.edu/tag/0BMY)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.FundamentalGroup
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tags 0BND (1) and 03VF (3).** Finite étale covers of a connected scheme `X`
are equivalent to finite sets with a continuous action of `π₁(X, x)`, by an equivalence whose
underlying finite sets are the geometric fibres at `x` and whose action is evaluation of natural
automorphisms. -/
@[stacks 0BND "(1) the equivalence of FÉt_X with the finite continuous π₁(X, x)-sets; (2) and (3) \
not covered here", stacks 03VF "(3) the functor sending a finite étale Y/X to F_x(Y) with its \
natural action is an equivalence onto the finite discrete continuous π₁(X, x)-sets; (1) and (2) \
are not covered here"]
theorem exists_finiteEtaleEquivalence (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    ∃ E : FiniteEtaleOver X ≌ ContAction FintypeCat.{u} (EtaleFundamentalGroup X x),
      ∃ α : E.functor ⋙
          forget₂ (ContAction FintypeCat.{u} (EtaleFundamentalGroup X x))
            FintypeCat.{u} ⋙ FintypeCat.incl ≅ finiteEtaleFiberFunctor x,
        ∀ (Y : FiniteEtaleOver X) (σ : EtaleFundamentalGroup X x)
          (y : (E.functor.obj Y).obj.V.obj),
          (α.hom.app Y) (ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ).asHom y) =
            (σ.asIso.app Y).hom ((α.hom.app Y) y) :=
  exists_finiteEtaleEquivalence_of_isGaloisCategory X x

/-- **Stacks Project, Tag 0BND (2), existence of the isomorphism of fibre functors.** Given a
second geometric point `x'` of a connected scheme `X`, there is an isomorphism
`t : F_x ≅ F_{x'}` between the two geometric fibre functors on `FÉt_X`. -/
@[stacks 0BND "(2) existence of an isomorphism t : F_x ≅ F_x' of the geometric fibre functors at \
two base points; the comparison of fundamental groups it induces, that comparison's independence \
up to inner conjugation and its compatibility with (1) are separate, and (1) and (3) are not \
covered here"]
theorem nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace (X : Scheme.{u}) [ConnectedSpace X]
    (x x' : GeometricPoint X) :
    Nonempty (finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :=
  nonempty_finiteEtaleFiberFunctorIso X x x'

/-- **Stacks Project, Tag 0BND (2), existence.** The étale fundamental groups of a connected
scheme at two geometric points are isomorphic as topological groups: the two geometric fibre
functors are isomorphic, and conjugation by such an isomorphism is a homeomorphic group
isomorphism. -/
@[stacks 0BND "(2) existence of the comparison of two base points, as topological groups; its \
independence up to inner conjugation and its compatibility with (1) are separate, and (1) and \
(3) are not covered here"]
theorem nonempty_etaleFundamentalGroupContinuousMulEquiv (X : Scheme.{u}) [ConnectedSpace X]
    (x x' : GeometricPoint X) :
    Nonempty (EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup X x') :=
  (nonempty_finiteEtaleFiberFunctorIso X x x').map etaleFundamentalGroupContinuousMulEquiv

/-- The transport of étale fundamental groups along an isomorphism of geometric fibre functors acts
as conjugation, whether it is read as an isomorphism of topological groups or of groups. -/
theorem etaleFundamentalGroupContinuousMulEquiv_apply {X : Scheme.{u}} [ConnectedSpace X]
    {x x' : GeometricPoint X} (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupContinuousMulEquiv t σ = etaleFundamentalGroupMulEquiv t σ :=
  rfl

/-- **Stacks Project, Tag 0BND (2), independence of the choice.** Two isomorphisms of the geometric
fibre functors at two geometric points induce isomorphisms of étale fundamental groups that differ
by an inner automorphism of the target. -/
@[stacks 0BND "(2) independence of the base-point comparison up to inner conjugation; its \
existence and its compatibility with (1) are separate, and (1) and (3) are not covered here"]
theorem isInnerConjugate_etaleFundamentalGroupContinuousMulEquiv {X : Scheme.{u}}
    [ConnectedSpace X] {x x' : GeometricPoint X}
    (t₁ t₂ : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    IsInnerConjugate (etaleFundamentalGroupContinuousMulEquiv t₁).toMulEquiv.toMonoidHom
      (etaleFundamentalGroupContinuousMulEquiv t₂).toMulEquiv.toMonoidHom :=
  isInnerConjugate_etaleFundamentalGroupMulEquiv t₁ t₂

/-- **Stacks Project, Tag 0BND (2), compatibility with the equivalences.** The change-of-base-point
isomorphism of topological groups intertwines the actions on the geometric fibres underlying the
two equivalences of Tag 0BND (1) at the two base points. -/
@[stacks 0BND "(2) compatibility of the base-point comparison with the actions of (1); its \
existence and its independence up to inner conjugation are separate, and (1) and (3) are not \
covered here"]
theorem etaleFundamentalGroupContinuousMulEquiv_action {X : Scheme.{u}} [ConnectedSpace X]
    {x x' : GeometricPoint X} (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    (Y : FiniteEtaleOver X) (σ : EtaleFundamentalGroup X x)
    (y : ((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.V.obj) :
    t.hom.app Y
        ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y
          (ConcreteCategory.hom
            (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.ρ σ).asHom y)) =
      (finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').hom.app Y
        (ConcreteCategory.hom
          (((finiteEtaleEquivalenceOfIsGaloisCategory X x').functor.obj Y).obj.ρ
            (etaleFundamentalGroupContinuousMulEquiv t σ)).asHom
          ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').inv.app Y
            (t.hom.app Y
              ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y y)))) :=
  etaleFundamentalGroupMulEquiv_action t Y σ y

/-- **Stacks Project, Tag 0BND (3), the commuting square.** For a morphism `f : X ⟶ Y` of connected
schemes, base change `FÉt_Y ⥤ FÉt_X` agrees under the equivalences of Tag 0BND (1) with restriction
of the action along `AlgebraicGeometry.etaleFundamentalGroupMap`, and the comparison isomorphism is
the canonical projection of geometric fibres. -/
@[stacks 0BND "(3) the square comparing base change with restriction along the induced \
homomorphism; the homomorphism and the equation determining it are separate, and (1) and (2) are \
not covered here"]
theorem exists_finiteEtaleEquivalence_mapIso {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X) :
    ∃ η : (finiteEtaleEquivalenceOfIsGaloisCategory Y (x.map f)).functor ⋙
          ContAction.res FintypeCat (etaleFundamentalGroupMap f x) ≅
        finiteEtaleBaseChange f ⋙
          (finiteEtaleEquivalenceOfIsGaloisCategory X x).functor,
      ∀ (V : FiniteEtaleOver Y)
        (a : (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj
          ((finiteEtaleBaseChange f).obj V)).obj.V.obj)),
        (finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso Y (x.map f)).hom.app V
            ((η.inv.app V).hom.hom a) =
          finiteEtaleFiberProjection f x V
            ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app
              ((finiteEtaleBaseChange f).obj V) a) :=
  exists_finiteEtaleEquivalenceOfIsGaloisCategory_mapIso f x

end AlgebraicGeometry

end
