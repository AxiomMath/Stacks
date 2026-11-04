module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct

/-!
# The complex-level projection formula for a closed embedding, on summands

`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso` is the
isomorphism of complexes

`Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`

for a morphism of ringed spaces `f` whose underlying map is a homeomorphism onto a closed subset.
It is built as the totalization of a termwise isomorphism of bicomplexes followed by the
comparison `Tot(f_*(-)) ⟶ f_*(Tot(-))`.  Nothing about it can be computed from that description
alone; what a consumer needs is its restriction to each summand of the total complex, which is
what this file supplies.

## Main results

* `ι_total_map_comp_totalMap`, in the root namespace: **the summand formula in the abstract.**
  For an additive functor `G` and a morphism of bicomplexes `φ : K ⟶ G(L)`, the summand
  inclusion of `Tot K` followed by `Tot φ` and then the comparison `Tot(G(-)) ⟶ G(Tot -)` is the
  component of `φ` followed by `G` of the summand inclusion of `Tot L`.
* `tensorSheaf_map_left_eq`: the two presentations of the tensor product of sheaves of modules
  agree on a morphism in the left variable. This follows from the canonical paired-map and
  component equations and is stated because a rewrite cannot cross between the presentations.
* `map_projectionFormulaMap'_comp_counit`: **the termwise projection-formula morphism of
  [Stacks, Tag 0B53]'s underived predecessor, transposed.**  Pulling back
  `Stacks.ProjectionFormula.projectionFormulaMap'` and following with the counit of `f^* ⊣ f_*`
  gives the comparison of [Stacks, Tag 01CD] followed by the counit in the left tensor factor.
* `ι_complexProjectionFormulaIso_hom`: **the summand formula for
  `complexProjectionFormulaIso`.**  On the `(p, q)` summand it is the termwise projection-formula
  morphism `projectionFormulaMap' f (A.X p) (B.X q)` followed by `f_*` of the `(p, q)` summand
  inclusion on the other side.

## Implementation notes

*Why the abstract summand formula is separated out.*  Unfolding `complexProjectionFormulaIso`
in place does not work.  That definition introduces a `HasTotal` instance for the source
bicomplex by transport along the termwise isomorphism, and the resulting term is not type-correct
at the transparency a rewrite works at: the instance it carries and the instance a rewrite
synthesises are equal only by proof irrelevance, which `rw` and `dsimp` do not use.  Stated
abstractly, with every instance an explicit binder, the formula is proved by ordinary rewriting;
the consumer then supplies the instances and discharges the match with `exact`, whose definitional
equality check does see through the difference.  This is the device that makes the file need no
relaxed transparency and no raised limits.

*Why the summand inclusions are written as `HomologicalComplex₂.ιTotal` and not as
`HomologicalComplex.ιMapBifunctor`.*  The two are the same map — the latter is an abbreviation for
the former — but `ιMapBifunctor` is declared in a section whose variables include
`PreservesZeroMorphisms` for the tensor bifunctor, and that hypothesis is not found by instance
search once the complexes have forced the category into the spelling
`structureSheafRing`.  Writing the bicomplex out and taking `ιTotal` of it
avoids the binder, and the statement elaborates.

*Why the complexes are taken in the `Modules` spelling.*  The library spells the category of
modules on a ringed space both as `SheafOfModules (structureSheafRing X)` and
as `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`, and the degreewise pushforward
correspondingly as `RingedSpaceModuleAdjunction.modulePushforward` and as
`StacksDraft.KFlat.modulePushforward`.  The tensor product that the total complexes are built
from is indexed by the second, so a statement mixing the two produces a composite whose two
halves carry different category instances, and then even associativity of composition is not
available to a rewrite.  Everything below is therefore stated in the second spelling, with the
two local reducibility attributes collapsing them where the inputs use the first.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.ProjectionFormula
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.ClosedEmbeddingPushforward
open Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open scoped CategoryTheory.Prod

universe u

/-! ### The summand formula in the abstract -/

section Abstract

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]

/-- **A summand of the totalization of a bicomplex mapped to a pushed-forward one.**  For an
additive functor `G`, a bicomplex `L` on the source and a morphism of bicomplexes
`φ : K ⟶ G(L)`, the `(p, q)` summand inclusion of `Tot K`, followed by the totalization of `φ`
and then the comparison `Tot(G(-)) ⟶ G(Tot -)`, is the `(p, q)` component of `φ` followed by `G`
of the `(p, q)` summand inclusion of `Tot L`.

Every instance is an explicit binder, which is what lets a consumer whose instances are
definitionally but not syntactically these ones apply the formula by `exact`. -/
lemma ι_total_map_comp_totalMap (G : C ⥤ D) [G.Additive]
    (L : HomologicalComplex₂ C c₁ c₂) [L.HasTotal c₁₂]
    (K : HomologicalComplex₂ D c₁ c₂) [K.HasTotal c₁₂]
    [(HomologicalComplex₂.TotalMap.mapBicomplex G L).HasTotal c₁₂]
    (φ : K ⟶ HomologicalComplex₂.TotalMap.mapBicomplex G L)
    (p : I₁) (q : I₂) (n : I₁₂) (hpq : ComplexShape.π c₁ c₂ c₁₂ (p, q) = n) :
    K.ιTotal c₁₂ p q n hpq ≫ (HomologicalComplex₂.total.map φ c₁₂).f n ≫
        (HomologicalComplex₂.TotalMap.totalMap (c₁₂ := c₁₂) G L).f n =
      (φ.f p).f q ≫ G.map (L.ιTotal c₁₂ p q n hpq) := by
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc]
  exact congrArg _ (HomologicalComplex₂.TotalMap.ι_totalMapf G L n p q hpq)

end Abstract

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit`
-- transparency already, but its reduct stops at an explicit-constructor projection while
-- `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`; these two Mathlib
-- definitions are the gap between them.
attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The two tensor presentations, and the termwise morphism transposed -/

/-- The two presentations of the tensor product of sheaves of modules agree on a morphism in the
left variable: the curried `Stacks.SheafOfModules.Tensor.sheafTensor` applied to `g` and
evaluated at `N` is the uncurried `Stacks.RingedSpace.tensorSheaf` applied to `g ×ₘ 𝟙 N`.

This follows from the canonical paired-map and component equations. It is stated because a
rewrite in the middle of a term indexed by one of
the spellings of the sheaf of rings produces a goal that is not type-correct at the transparency
`simp` works at, so the identification has to be applied as an equation and not found by
unfolding. -/
lemma tensorSheaf_map_left_eq (Z : RingedSpace.{u, u})
    {M M' : SheafOfModules.{u} (structureRingSheaf Z)} (g : M ⟶ M')
    (N : SheafOfModules.{u} (structureRingSheaf Z)) :
    ((sheafTensor.{u, u, u, u, u} Z.sheaf).map g).app N =
      (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} Z.sheaf)).map (g ×ₘ 𝟙 N) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Z.sheaf g (𝟙 N)).trans
    (Stacks.SheafOfModules.Tensor.sheafTensor_map_app Z.sheaf g N).symm).symm

/-- **The termwise projection-formula morphism, transposed.**  Pulling back
`Stacks.ProjectionFormula.projectionFormulaMap'` along `f` and following with the counit of
`f^* ⊣ f_*` gives the comparison of [Stacks, Tag 01CD] followed by `f^*f_* ⟶ id` in the left
tensor factor.

There is no hypothesis on `f`: this is the defining transpose relation of
`projectionFormulaMap'`, which is an instance of the abstract adjunction-tensor morphism, and it
holds for every morphism of ringed spaces. -/
@[reassoc]
lemma map_projectionFormulaMap'_comp_counit (G : SheafOfModules.{u} (structureSheafRing X))
    (H : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullback f).map (projectionFormulaMap' f G H) ≫
        (modulePullbackPushforwardAdjunction f).counit.app
          (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj ((modulePullback f).obj H)) =
      (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso f
          ((modulePushforward f).obj G) H).hom ≫
        ((sheafTensor.{u, u, u, u, u} X.sheaf).map
          ((modulePullbackPushforwardAdjunction f).counit.app G)).app
          ((modulePullback f).obj H) := by
  have h := ((pullbackAdjunction f).homEquiv
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)))
        |>.obj ((pushforwardFunctor f).obj G, H))
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)))
        |>.obj (G, (pullbackFunctor f).obj H))).symm_apply_apply
    ((comparisonNatTrans f).app ((pushforwardFunctor f).obj G, H) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
        ((pullbackAdjunction f).counit.app G ×ₘ 𝟙 ((pullbackFunctor f).obj H)))
  exact h.trans (congrArg
    (fun morphism =>
      (comparisonNatTrans f).app ((pushforwardFunctor f).obj G, H) ≫ morphism)
    (tensorSheaf_map_left_eq X ((pullbackAdjunction f).counit.app G)
      ((pullbackFunctor f).obj H)).symm)

/-! ### The summand formula for the complex-level projection formula -/

/-- **The complex-level projection formula on a summand.**  For `f` a homeomorphism onto a closed
subset and arbitrary complexes `A^•` on `X` and `B^•` on `Y`, the `(p, q)` summand inclusion of
`Tot(f_*A^• ⊗_{𝒪_Y} B^•)` followed by `complexProjectionFormulaIso` is the termwise
projection-formula morphism at `A^p` and `B^q`, followed by `f_*` of the `(p, q)` summand
inclusion of `Tot(A^• ⊗_{𝒪_X} f^*B^•)`.

This is `ι_total_map_comp_totalMap` at `G = f_*` and `φ` the termwise isomorphism of bicomplexes
`projectionBicomplexIso`, whose `(p, q)` component is the ordinary projection formula for a
closed embedding; the two `HasTotal` instances the statement of `complexProjectionFormulaIso`
carries are supplied here and matched definitionally. -/
lemma ι_complexProjectionFormulaIso_hom
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor.{u, u, u, u, u} Y.sheaf).mapBifunctorHomologicalComplex
                (.up ℤ) (.up ℤ)).obj
            ((pushforwardComplex f).obj A)).obj B)
          (.up ℤ) p q n hpq ≫
        (complexProjectionFormulaIso f hf A B).hom.f n =
      projectionFormulaMap' f (A.X p) (B.X q) ≫
        (StacksDraft.KFlat.modulePushforward f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor.{u, u, u, u, u} X.sheaf).mapBifunctorHomologicalComplex
                  (.up ℤ) (.up ℤ)).obj A).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq) := by
  let : (modulePushforward f).Additive :=
    modulePushforward_additive f
  let : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  let : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  let : (StacksDraft.KFlat.modulePushforward f).Additive :=
    StacksDraft.KFlat.modulePushforward_additive f
  let := HomologicalComplex₂.hasTotal_of_iso (projectionBicomplexIso f hf A B) (.up ℤ)
  have key := ι_total_map_comp_totalMap (c₁₂ := ComplexShape.up ℤ)
    (StacksDraft.KFlat.modulePushforward f)
    ((((sheafTensor.{u, u, u, u, u} X.sheaf).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj A).obj
      ((pullbackComplex f).obj B))
    ((((sheafTensor.{u, u, u, u, u} Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((pushforwardComplex f).obj A)).obj B)
    (projectionBicomplexIso f hf A B).hom p q n hpq
  exact key

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

end
