module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtPureMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses

/-!
# Naturality of the comparison `Lp^*R𝓗om ⊗ Lq^*R𝓗om ⟶ R𝓗om(⊠, ⊠)` in the target

`Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap` is the comparison

`Lp^*R𝓗om(K, K') ⊗^𝐋 Lq^*R𝓗om(M, M') ⟶ R𝓗om(K ⊠ M, K' ⊠ M')`

through which the Künneth morphism for Ext of [Stacks, Tag 0FXY] is built: the tensor product of
the two pullback comparisons of [Stacks, Tag 08I3] followed by the comparison of
[Stacks, Tag 0FXP] on `W`. This file proves that it is natural in the two target objects `K'`
and `M'`, by proving that each of its constituents is.

## Main results

* `Stacks.Cohomology.DerivedKunnethExt.sheafHomEvalEquiv_comp_map`: the bijection of
  [Stacks, Tag 08DI], in the form `Stacks.Cohomology.DerivedKunnethExt.sheafHomEvalEquiv`, is
  natural in the target.
* `Stacks.Cohomology.DerivedKunnethExt.tensorMap_map_comp_sheafHomEval`: evaluation
  `R𝓗om(A, B) ⊗^𝐋 A ⟶ B` is natural in `B`.
* `Stacks.Cohomology.DerivedKunnethExt.sheafHomTensorMap_naturality_target`: the comparison of
  [Stacks, Tag 0FXP] is natural in the two target objects.
* `Stacks.Cohomology.DerivedKunnethExt.pullbackSheafHomMap_naturality_target`: the comparison
  of [Stacks, Tag 08I3] is natural in the target.
* `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap_naturality_target`: **the comparison
  `boxSheafHomMap` is natural in `K'` and `M'`**.

## References

* [Stacks Project, Tag 0FXP](https://stacks.math.columbia.edu/tag/0FXP)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0FXY](https://stacks.math.columbia.edu/tag/0FXY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose

-- The derived internal hom is declared over the ring sheaf of the ringed site of opens while the
-- objects here live over `Tensor.ringSheaf`, and `convert` closes the instance arguments of the
-- two readings at `.instances` transparency only with this attribute.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The bijection of [Stacks, Tag 08DI], read as `curryPair`, is natural in the target. This is
`Stacks.Cohomology.DerivedInternalHomPullback.curriedTargetNatural_ringedSpace`. -/
theorem curryPair_targetNatural :
    DerivedInternalHomPullback.EquivalenceTranspose.CurriedTargetNatural
      (Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (internalHomTensorPair Z) (curryPair Z) :=
  DerivedInternalHomPullback.curriedTargetNatural_ringedSpace Z

/-- **The bijection of [Stacks, Tag 08DI] is natural in the target.** For
`x : C ⟶ R𝓗om(A, B)` and `k : B ⟶ B'`, the transpose of `x ≫ R𝓗om(A, k)` is the transpose of
`x` followed by `k`. -/
theorem sheafHomEvalEquiv_comp_map {C A B B' : DerivedCategory (Mod Z.sheaf)}
    (x : C ⟶ sheafHomObj Z A B) (k : B ⟶ B') :
    sheafHomEvalEquiv Z C A B'
        (x ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op A)).map k) =
      sheafHomEvalEquiv Z C A B x ≫ k := by
  have hh := curryPair_targetNatural Z C A B B' k x
  rw [sheafHomEvalEquiv_eq_curryPair, sheafHomEvalEquiv_eq_curryPair, Category.assoc]
  convert congrArg (((tensorBridge Z).inv.app C).app A ≫ ·) hh using 2

/-- **Evaluation is natural in the target.** For `k : B ⟶ B'`,

`(R𝓗om(A, k) ⊗ A) ≫ ev_{A, B'} = ev_{A, B} ≫ k`. -/
theorem tensorMap_map_comp_sheafHomEval (A : DerivedCategory (Mod Z.sheaf))
    {B B' : DerivedCategory (Mod Z.sheaf)} (k : B ⟶ B') :
    tensorMap Z (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op A)).map k) (𝟙 A) ≫
        sheafHomEval Z A B' =
      sheafHomEval Z A B ≫ k := by
  have h1 : tensorMap Z (𝟙 (sheafHomObj Z A B)) (𝟙 A) = 𝟙 _ := by
    simp [tensorMap]
  have h := sheafHomEvalEquiv_comp_map Z (𝟙 (sheafHomObj Z A B)) k
  rw [sheafHomEvalEquiv_apply, sheafHomEvalEquiv_apply, h1, Category.id_comp,
    Category.id_comp] at h
  exact h

/-- **The transpose of `R𝓗om(A, k)` is evaluation followed by `k`.** -/
theorem sheafHomEvalEquiv_map (A : DerivedCategory (Mod Z.sheaf))
    {B B' : DerivedCategory (Mod Z.sheaf)} (k : B ⟶ B') :
    sheafHomEvalEquiv Z _ A B'
        (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op A)).map k) =
      sheafHomEval Z A B ≫ k :=
  (sheafHomEvalEquiv_apply Z _ A B' _).trans (tensorMap_map_comp_sheafHomEval Z A k)

/-- **The comparison of [Stacks, Tag 0FXP] is natural in the two target objects.** For
`x : A' ⟶ A''` and `y : B' ⟶ B''`,

`(R𝓗om(A, x) ⊗ R𝓗om(B, y)) ≫ c_{A, A'', B, B''} = c_{A, A', B, B'} ≫ R𝓗om(A ⊗ B, x ⊗ y)`. -/
theorem sheafHomTensorMap_naturality_target (A : DerivedCategory (Mod Z.sheaf))
    {A' A'' : DerivedCategory (Mod Z.sheaf)} (B : DerivedCategory (Mod Z.sheaf))
    {B' B'' : DerivedCategory (Mod Z.sheaf)} (x : A' ⟶ A'') (y : B' ⟶ B'') :
    tensorMap Z (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op A)).map x)
        (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).map y) ≫
        sheafHomTensorMap Z A A'' B B'' =
      sheafHomTensorMap Z A A' B B' ≫
        ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op (tensorObj Z A B))).map
          (tensorMap Z x y) := by
  apply (sheafHomEvalEquiv Z _ _ _).injective
  rw [sheafHomEvalEquiv_tensorMap_comp_sheafHomTensorMap, sheafHomEvalEquiv_comp_map,
    sheafHomEvalEquiv_sheafHomTensorMap, sheafHomEvalEquiv_map, sheafHomEvalEquiv_map,
    Category.assoc, tensorMap_comp]

end OneSpace

section Pullback

variable {Z W : RingedSpace.{u, u}} (h : W ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison of [Stacks, Tag 08I3] is natural in the target.** For `k : B ⟶ B'`,

`Lh^*R𝓗om(A, k) ≫ c_{A, B'} = c_{A, B} ≫ R𝓗om(Lh^*A, Lh^*k)`.

This is `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_naturality_target` at
the data the comparison is built from, at the spelling of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt`. -/
theorem pullbackSheafHomMap_naturality_target (A : DerivedCategory (Mod Z.sheaf))
    {B B' : DerivedCategory (Mod Z.sheaf)} (k : B ⟶ B') :
    (derivedPullbackFunctor h).map
        (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op A)).map k) ≫
        pullbackSheafHomMap h A B' =
      pullbackSheafHomMap h A B ≫
        ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj
          (op ((derivedPullbackFunctor h).obj A))).map ((derivedPullbackFunctor h).map k) := by
  rw [pullbackSheafHomMap_eq_homComparison, pullbackSheafHomMap_eq_homComparison]
  exact DerivedInternalHomPullback.Transpose.homComparison_naturality_target
    (derivedPullbackFunctor h) (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom W.sheaf) (internalHomTensorPair Z)
    (internalHomTensorPair W) (curryPair Z) (curryPair W) (pullbackTensorPairIso h)
    (curryPair_naturalLeft Z) (curryPair_targetNatural Z) (curryPair_naturalLeft W)
    (curryPair_targetNatural W) A k

end Pullback

section Kunneth

variable {X Y W : RingedSpace.{u, u}} (p : W ⟶ X) (q : W ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison `Lp^*R𝓗om(K, K') ⊗^𝐋 Lq^*R𝓗om(M, M') ⟶ R𝓗om(K ⊠ M, K' ⊠ M')` is natural
in `K'` and `M'`.** For `φ : K' ⟶ K''` and `ψ : M' ⟶ M''`,

`(Lp^*R𝓗om(K, φ) ⊗ Lq^*R𝓗om(M, ψ)) ≫ c_{K, K'', M, M''} = c_{K, K', M, M'} ≫ R𝓗om(K ⊠ M, φ ⊠ ψ)`,

where `φ ⊠ ψ = Lp^*φ ⊗ Lq^*ψ`. Both constituents of the comparison are natural:
`pullbackSheafHomMap_naturality_target` for the two pullback comparisons of
[Stacks, Tag 08I3], and `sheafHomTensorMap_naturality_target` for the comparison of
[Stacks, Tag 0FXP]. -/
theorem boxSheafHomMap_naturality_target (K : DerivedCategory (Mod X.sheaf))
    {K' K'' : DerivedCategory (Mod X.sheaf)} (M : DerivedCategory (Mod Y.sheaf))
    {M' M'' : DerivedCategory (Mod Y.sheaf)} (φ : K' ⟶ K'') (ψ : M' ⟶ M'') :
    tensorMap W
        ((derivedPullbackFunctor p).map
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).map φ))
        ((derivedPullbackFunctor q).map
          (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op M)).map ψ)) ≫
        boxSheafHomMap p q K K'' M M'' =
      boxSheafHomMap p q K K' M M' ≫
        ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op (boxProd p q K M))).map
          (tensorMap W ((derivedPullbackFunctor p).map φ) ((derivedPullbackFunctor q).map ψ)) := by
  unfold boxSheafHomMap
  rw [← Category.assoc, tensorMap_comp, pullbackSheafHomMap_naturality_target,
    pullbackSheafHomMap_naturality_target, ← tensorMap_comp, Category.assoc,
    sheafHomTensorMap_naturality_target, Category.assoc]

end Kunneth

end Stacks.Cohomology.DerivedKunnethExt

end
