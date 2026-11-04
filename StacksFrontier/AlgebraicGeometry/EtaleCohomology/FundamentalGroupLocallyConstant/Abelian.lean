module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteModuleSheafScalarAction

/-!
# Finite locally constant abelian sheaves and the étale fundamental group

Let `X` be a connected scheme and `x` a geometric point of it. The finite locally constant
sheaves of abelian groups on the small étale site of `X` form a category equivalent to the
category of finite discrete `π₁(X, x)`-modules. This is part (2) of Stacks Tag 0DV5.

## Main results

* `AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence` — **Tag 0DV5 (2)**.

## Implementation notes

Part (2) is part (1) with extra structure, which is exactly how the source proves it: a finite
locally constant sheaf of abelian groups is a commutative group object among the finite locally
constant sheaves of sets, a finite discrete `π₁(X, x)`-module is a commutative group object
among the finite continuous `π₁(X, x)`-sets, and the equivalence of part (1) preserves finite
products. That transport is
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`, which takes the
equivalence of part (1) as its only input; here that input is
`AlgebraicGeometry.finiteLocallyConstantSetsEquivalence`, composed with
`AlgebraicGeometry.finiteContinuousGSetEquivalence` to read the finite continuous `G`-sets as a
full subcategory of all continuous `G`-sets.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1)

/-- The equivalence of Tag 0DV5 (1), read with the finite continuous `π₁(X, x)`-sets presented
as a full subcategory of all continuous `π₁(X, x)`-sets. This is the shape consumed by the
transport of commutative group objects. -/
public noncomputable def finiteLocallyConstantSetsEquivalence' :
    (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
      (ContinuousGSet.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  (finiteLocallyConstantSetsEquivalence B X x).trans finiteContinuousGSetEquivalence.symm

/-- **Stacks Project, Tag 0DV5, part (2).** For a connected scheme `X` with a geometric point
`x`, the finite locally constant sheaves of abelian groups on `X_étale` are equivalent to the
finite `π₁(X, x)`-modules, that is, to the finite abelian groups with a continuous action of the
étale fundamental group.

Part (1) of the tag is `AlgebraicGeometry.finiteLocallyConstantSetsEquivalence` and part (3) is
`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence`. -/
@[stacks 0DV5 "(2) finite locally constant sheaves of abelian groups are the finite \
  π₁(X, x)-modules"]
public noncomputable def finiteLocallyConstantAbelianSheafEquivalence :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
      (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  finiteLocallyConstantAbelianEquivalenceOfSetEquivalence
    (SmallEtale.topology B X.1 X.2) (EtaleFundamentalGroup X.1 x)
    (finiteLocallyConstantSetsEquivalence' B X x)

/-! ### Additivity of the equivalence of part (2) -/

/-- An equivalence carries a zero object to a zero object: it is initial and terminal, and both
are preserved. -/
public theorem isZero_equivalence_functor_obj {A : Type*} [Category* A] {B : Type*} [Category* B]
    (e : A ≌ B) {X : A} (h : Limits.IsZero X) : Limits.IsZero (e.functor.obj X) :=
  have hi : Limits.IsInitial (e.functor.obj X) := h.isInitial.isInitialObj e.functor X
  have ht : Limits.IsTerminal (e.functor.obj X) := h.isTerminal.isTerminalObj e.functor X
  ⟨fun Y ↦ ⟨⟨⟨hi.to Y⟩, fun f ↦ hi.hom_ext f _⟩⟩,
    fun Y ↦ ⟨⟨⟨ht.from Y⟩, fun f ↦ ht.hom_ext f _⟩⟩⟩

/-- **The equivalence of part (2) is additive.** Both sides are preadditive, the finite locally
constant abelian sheaves have binary products and a zero object, and an equivalence preserves
both; a functor between preadditive categories preserving binary products and zero morphisms is
additive. -/
public instance additive_finiteLocallyConstantAbelianSheafEquivalence :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.Additive := by
  set e := finiteLocallyConstantAbelianSheafEquivalence B X x
  let : Limits.HasZeroObject
      (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
    ⟨⟨e.functor.obj 0, isZero_equivalence_functor_obj e (Limits.isZero_zero _)⟩⟩
  let : e.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_map_zero_object
      ((isZero_equivalence_functor_obj e (Limits.isZero_zero _)).iso (Limits.isZero_zero _))
  exact Functor.additive_of_preserves_binary_products e.functor

end AlgebraicGeometry

end
