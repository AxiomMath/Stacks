module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp

/-!
# The composition law for the comparison of Tag 01CD, at the re-seated monoidal spelling

`Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp` is the compatibility of the
comparison of [Stacks, Tag 01CD] with the composition law `f^* g^* ≅ (f ≫ g)^*` for pullback. It
is stated for `Stacks.PullbackGradedAlgebra.monoidalCategory`, the monoidal structure of Tag 01CA
obtained by `CategoryTheory.Monoidal.induced`, because that is the structure whose structural
morphisms have section formulas. **This file restates it for
`SheafOfModules.monoidalCategorySheafTensor`**, the structure obtained by
`CategoryTheory.MonoidalCategory.reseat`, which is the one `Stacks.PullbackSheafTensor` and every
consumer of `Stacks.PullbackSheafTensor.sheafTensorComparison` work in.

The two structures agree on every structural morphism —
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree` is that file — but
they are *not* definitionally equal, and the restatement is not a `rfl`: asking
the kernel to accept `Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp` against the
re-seated statement is a `(deterministic) timeout at isDefEq` after 200000 heartbeats.

## Main results

* `Stacks.RingedSpace.tensorHom_eq_strict`: **the two monoidal structures of Tag 01CA on the
  modules of a ringed space have the same tensor product of morphisms.** This is the member of
  the `Stacks.RingedSpace.*_eq_strict` family for `⊗ₘ`; it follows from the two whiskerings by
  `CategoryTheory.MonoidalCategory.tensorHom_def`.
* `Stacks.PullbackSheafTensor.tensorSheafMap_eq_tensorHom`: the tensor product bifunctor of Tag
  01CA on a pair of morphisms is `⊗ₘ` for the re-seated structure.
* `Stacks.PullbackSheafTensor.sheafTensorComparison_comp`: **the comparison of Tag 01CD is
  compatible with the composition law for pullback**, at the re-seated spelling.

## Implementation notes

**The substitution of the tail is done by `conv_rhs => rw`, and that is the only shape that
works.** `Stacks.PullbackTensorComposition.comparison_comp` is free of any monoidal instance —
its tail is the tensor product bifunctor applied to a pair of morphisms — so the whole
restatement is one replacement of that tail by `⊗ₘ`. Of three ways of making that
replacement, two fail:

* passing the equation and the instance-free statement to a tail-replacement lemma over a bare
  category is a `(deterministic) timeout at isDefEq`;
* writing the instance-free statement out as a declaration of its own, so that the replacement
  has nothing left to unify, is a `(deterministic) timeout at whnf` — the cost is in the pair's
  type ascription, whose source objects have to be solved from the two morphisms;
* `conv_rhs => rw [← tensorSheafMap_eq_tensorHom]` followed by `exact` costs about two seconds.

So on this crossing the usual preference for an `apply` of a bare-category lemma over a rewrite
is reversed. Nothing is rewritten *on a module* here, and no isomorphism of
`AlgebraicGeometry.Scheme.Modules` occurs: the rewrite is of one equation between two spellings
of the same morphism of the modules of a ringed space, where there is a single `Category`
instance in play.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.RingedSpace

/-- **The two monoidal structures of Tag 01CA on `Mod(𝒪_Z)` have the same tensor product of
morphisms.** Both are the right whiskering followed by the left whiskering, and the two
structures agree on each of those.

This is the companion of `Stacks.RingedSpace.whiskerLeft_eq_strict`,
`whiskerRight_eq_strict` and `associator_eq_strict`. Unlike the associator and the tensor
product on objects, it is not a `rfl`: `CategoryTheory.MonoidalCategory.reseat` defines the
tensor product of morphisms through the re-seated bifunctor and not through the whiskerings. -/
theorem tensorHom_eq_strict {Z : RingedSpace.{u, u}}
    {A A' B B' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)}
    (u : A ⟶ A') (v : B ⟶ B') :
    @MonoidalCategoryStruct.tensorHom _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct
        A A' B B' u v =
      @MonoidalCategoryStruct.tensorHom _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct
        A A' B B' u v :=
  (@MonoidalCategory.tensorHom_def _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf) _ _ _ _ u v).trans
    ((congrArg₂ (fun a b ↦ a ≫ b)
        (whiskerRight_eq_strict u B) (whiskerLeft_eq_strict A' v)).trans
      (@MonoidalCategory.tensorHom_def _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z) _ _ _ _ u v).symm)

end Stacks.RingedSpace

namespace Stacks.PullbackSheafTensor

attribute [local instance] monoidalSheafTensor

open Stacks.RingedSpace (pullbackFunctor structureRingSheaf)

/-- **The tensor product bifunctor of Tag 01CA on a pair of morphisms is `⊗ₘ`** for the re-seated
monoidal structure. The two spellings are not definitionally equal; neither is usable against a
goal stated with the other. -/
theorem tensorSheafMap_eq_tensorHom {Z : RingedSpace.{u, u}}
    {A B A' B' : _root_.SheafOfModules.{u} (structureRingSheaf Z)} (u : A ⟶ A') (v : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩)).map
        ((u, v) : ((A, B) : _ × _) ⟶ (A', B')) = u ⊗ₘ v :=
  (Stacks.PullbackTensorCoherence.tensorSheaf_map_eq_tensorHom u v).trans
    (Stacks.RingedSpace.tensorHom_eq_strict u v).symm

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the composition law for pullback**,
at the re-seated monoidal spelling: for `f : X ⟶ Y` and `j : Y ⟶ Z`, reading the pullback along
`f ≫ j` of a tensor product through the composition law and then splitting it agrees with
splitting along `j`, pulling back along `f`, splitting again and then reading each factor through
the composition law.

This is `Stacks.PullbackTensorComposition.comparison_comp`, whose statement uses the tensor
product bifunctor rather than `⊗ₘ` and so mentions no monoidal structure at all, with its tail
replaced; see the implementation notes for why that replacement is a `conv_rhs => rw` and not an
`apply`. -/
theorem sheafTensorComparison_comp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    (Stacks.PullbackTensorCoherence.pullbackCompIso f j).hom.app (A ⊗ B) ≫
        sheafTensorComparison (f ≫ j) A B =
      (pullbackFunctor f).map (sheafTensorComparison j A B) ≫
        sheafTensorComparison f ((pullbackFunctor j).obj A) ((pullbackFunctor j).obj B) ≫
          ((Stacks.PullbackTensorCoherence.pullbackCompIso f j).hom.app A ⊗ₘ
            (Stacks.PullbackTensorCoherence.pullbackCompIso f j).hom.app B) := by
  conv_rhs => rw [← tensorSheafMap_eq_tensorHom]
  exact Stacks.PullbackTensorComposition.comparison_comp f j A B

end Stacks.PullbackSheafTensor

end
