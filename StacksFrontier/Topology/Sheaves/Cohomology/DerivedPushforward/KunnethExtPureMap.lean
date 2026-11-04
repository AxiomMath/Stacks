module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtPureTensor

/-!
# Pure maps under the Künneth morphism for Ext

This file computes the transposes of the morphism `R SheafHom(A, A') ⊗^𝐋 R SheafHom(B, B') ⟶
R SheafHom(A ⊗^𝐋 B, A' ⊗^𝐋 B')` of [Stacks, Tag 0FXP], of the canonical map of [Stacks, Tag 08I3]
and of the comparison `boxSheafHomMap` against pure tensors of morphisms into derived internal
homs.

## Main definitions

* `sheafHomEvalEquiv`: the bijection `(C ⟶ R SheafHom(A, B)) ≃ (C ⊗^𝐋 A ⟶ B)`,
  `x ↦ (x ⊗ 1) ≫ ev`.
* `pullbackEvalIso`: the comparison `Lh^*C ⊗^𝐋 Lh^*A ≅ Lh^*(C ⊗^𝐋 A)`.

## Main results

* `sheafHomEvalEquiv_tensorMap_comp_sheafHomTensorMap`: the morphism of [Stacks, Tag 0FXP] at a
  pure pair.
* `sheafHomEvalEquiv_map_comp_pullbackSheafHomMap`: the canonical map of [Stacks, Tag 08I3]
  against a morphism into the derived internal hom.
* `sheafHomEvalEquiv_tensorMap_comp_boxSheafHomMap`: the comparison `boxSheafHomMap` at a pure
  pair.
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

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The flip of the middle two factors is natural in its first two arguments. -/
theorem middleFour_natural_left {H H' G G' : DerivedCategory (Mod Z.sheaf)} (x : H ⟶ H')
    (y : G ⟶ G') (A B : DerivedCategory (Mod Z.sheaf)) :
    tensorMap Z (tensorMap Z x y) (𝟙 (tensorObj Z A B)) ≫ middleFour Z H' G' A B =
      middleFour Z H G A B ≫ tensorMap Z (tensorMap Z x (𝟙 A)) (tensorMap Z y (𝟙 B)) := by
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  have h := tensorμ_natural x y (𝟙 A) (𝟙 B)
  rwa [id_tensorHom_id] at h

/-- Evaluation as a bijection: `x ↦ (x ⊗ 1) ≫ ev` identifies morphisms `C ⟶ R SheafHom(A, B)`
with morphisms `C ⊗^𝐋 A ⟶ B`. It is the tensor–internal-hom bijection of [Stacks, Tag 08DI]
followed by the comparison of the two derived tensor products. -/
def sheafHomEvalEquiv (C A B : DerivedCategory (Mod Z.sheaf)) :
    (C ⟶ sheafHomObj Z A B) ≃ (tensorObj Z C A ⟶ B) :=
  (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite Z.sheaf) C A B).toEquiv.trans
    ((((tensorBridge Z).app C).app A).homCongr (Iso.refl B))

/-- The bijection `sheafHomEvalEquiv` is tensoring with the identity followed by evaluation. -/
theorem sheafHomEvalEquiv_apply (C A B : DerivedCategory (Mod Z.sheaf))
    (x : C ⟶ sheafHomObj Z A B) :
    sheafHomEvalEquiv Z C A B x = tensorMap Z x (𝟙 A) ≫ sheafHomEval Z A B :=
  (congrArg (((tensorBridge Z).inv.app C).app A ≫ ·) (Category.comp_id _)).trans
    (tensorMap_id_comp_sheafHomEval Z A B C x).symm

/-- `sheafHomEvalEquiv` is the bijection of [Stacks, Tag 08DI] preceded by the comparison of the
two derived tensor products. -/
theorem sheafHomEvalEquiv_eq (C A B : DerivedCategory (Mod Z.sheaf))
    (x : C ⟶ sheafHomObj Z A B) :
    sheafHomEvalEquiv Z C A B x = ((tensorBridge Z).inv.app C).app A ≫
      AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) C A B x :=
  (sheafHomEvalEquiv_apply Z C A B x).trans (tensorMap_id_comp_sheafHomEval Z A B C x)

/-- `sheafHomEvalEquiv` is natural in the source. -/
theorem sheafHomEvalEquiv_comp {C C' : DerivedCategory (Mod Z.sheaf)}
    (A B : DerivedCategory (Mod Z.sheaf)) (g : C' ⟶ C) (x : C ⟶ sheafHomObj Z A B) :
    sheafHomEvalEquiv Z C' A B (g ≫ x) = tensorMap Z g (𝟙 A) ≫ sheafHomEvalEquiv Z C A B x := by
  have h : tensorMap Z (g ≫ x) (𝟙 A) = tensorMap Z g (𝟙 A) ≫ tensorMap Z x (𝟙 A) :=
    (congrArg (tensorMap Z (g ≫ x)) (Category.id_comp (𝟙 A)).symm).trans
      (tensorMap_comp Z g x (𝟙 A) (𝟙 A)).symm
  refine (sheafHomEvalEquiv_apply Z C' A B (g ≫ x)).trans ?_
  refine ((congrArg (· ≫ sheafHomEval Z A B) h).trans (Category.assoc _ _ _)).trans ?_
  exact congrArg (tensorMap Z g (𝟙 A) ≫ ·) (sheafHomEvalEquiv_apply Z C A B x).symm

/-- The transpose of the morphism of [Stacks, Tag 0FXP] under `sheafHomEvalEquiv` is the flip of
the middle two factors followed by the tensor product of the two evaluations. -/
theorem sheafHomEvalEquiv_sheafHomTensorMap (A A' B B' : DerivedCategory (Mod Z.sheaf)) :
    sheafHomEvalEquiv Z _ _ _ (sheafHomTensorMap Z A A' B B') =
      middleFour Z (sheafHomObj Z A A') (sheafHomObj Z B B') A B ≫
        tensorMap Z (sheafHomEval Z A A') (sheafHomEval Z B B') := by
  have h : (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite Z.sheaf)
        (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B'))
        (tensorObj Z A B) (tensorObj Z A' B')).toEquiv (sheafHomTensorMap Z A A' B B') =
        ((tensorBridge Z).hom.app (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B'))).app
          (tensorObj Z A B) ≫
        middleFour Z (sheafHomObj Z A A') (sheafHomObj Z B B') A B ≫
          tensorMap Z (sheafHomEval Z A A') (sheafHomEval Z B B') := by
    rw [sheafHomTensorMap, Equiv.apply_symm_apply]
  refine (sheafHomEvalEquiv_eq Z _ _ _ _).trans ?_
  refine (congrArg (((tensorBridge Z).inv.app _).app _ ≫ ·) h).trans ?_
  exact Iso.inv_hom_id_app_app_assoc (tensorBridge Z) _ _ _

/-- The morphism of [Stacks, Tag 0FXP] at a pure pair: for `x : C ⟶ R SheafHom(A, A')`
and `y : D ⟶ R SheafHom(B, B')`, the transpose of
`C ⊗^𝐋 D --x ⊗ y--> R SheafHom(A, A') ⊗^𝐋 R SheafHom(B, B') --> R SheafHom(A ⊗^𝐋 B, A' ⊗^𝐋 B')`
is the flip of the middle two factors followed by the tensor product of the transposes of `x`
and of `y`. -/
theorem sheafHomEvalEquiv_tensorMap_comp_sheafHomTensorMap
    {C D A A' B B' : DerivedCategory (Mod Z.sheaf)}
    (x : C ⟶ sheafHomObj Z A A') (y : D ⟶ sheafHomObj Z B B') :
    sheafHomEvalEquiv Z _ _ _ (tensorMap Z x y ≫ sheafHomTensorMap Z A A' B B') =
      middleFour Z C D A B ≫
        tensorMap Z (sheafHomEvalEquiv Z C A A' x) (sheafHomEvalEquiv Z D B B' y) := by
  rw [sheafHomEvalEquiv_comp, sheafHomEvalEquiv_sheafHomTensorMap,
    reassoc_of% (middleFour_natural_left Z x y A B), tensorMap_comp, sheafHomEvalEquiv_apply,
    sheafHomEvalEquiv_apply]

end OneSpace

section Pullback

variable {Z W : RingedSpace.{u, u}} (h : W ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived tensor product the derived internal hom is stated over, as a functor on pairs. -/
abbrev internalHomTensorPair (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    DerivedCategory (Mod Z.sheaf) × DerivedCategory (Mod Z.sheaf) ⥤ DerivedCategory (Mod Z.sheaf) :=
  DerivedInternalHomPullback.internalHomTensorUncurried Z

/-- The bijection of [Stacks, Tag 08DI], as a family of bijections. -/
abbrev curryPair (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A B C : DerivedCategory (Mod Z.sheaf)) :
    (A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) ≃
      ((internalHomTensorPair Z).obj (A, B) ⟶ C) :=
  (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
    (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv

/-- The monoidality isomorphism of [Stacks, Tag 079U] at the derived tensor product the derived
internal hom is stated over. -/
def pullbackTensorPairIso :
    internalHomTensorPair Z ⋙ derivedPullbackFunctor h ≅
      (derivedPullbackFunctor h).prod (derivedPullbackFunctor h) ⋙ internalHomTensorPair W :=
  DerivedInternalHomPullback.pullbackTensorIso h

/-- The canonical map `pullbackSheafHomMap` is the comparison
`DerivedInternalHomPullback.Transpose.homComparison` built from the bijections `curryPair` and the
isomorphism `pullbackTensorPairIso`. -/
theorem pullbackSheafHomMap_eq_homComparison (A B : DerivedCategory (Mod Z.sheaf)) :
    pullbackSheafHomMap h A B =
      DerivedInternalHomPullback.Transpose.homComparison (derivedPullbackFunctor h)
        (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
        (Stacks.SheafOfModules.derivedSheafHom W.sheaf) (internalHomTensorPair Z)
        (internalHomTensorPair W) (curryPair Z) (curryPair W)
        (pullbackTensorPairIso h) A B :=
  rfl

/-- `sheafHomEvalEquiv` is `curryPair` preceded by the comparison of the two derived tensor
products. -/
theorem sheafHomEvalEquiv_eq_curryPair (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (C A B : DerivedCategory (Mod Z.sheaf)) (x : C ⟶ sheafHomObj Z A B) :
    sheafHomEvalEquiv Z C A B x = ((tensorBridge Z).inv.app C).app A ≫ curryPair Z C A B x :=
  sheafHomEvalEquiv_eq Z C A B x

/-- `curryPair` is `sheafHomEvalEquiv` preceded by the comparison of the two derived tensor
products. -/
theorem curryPair_eq_sheafHomEvalEquiv (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (C A B : DerivedCategory (Mod Z.sheaf)) (x : C ⟶ sheafHomObj Z A B) :
    curryPair Z C A B x = ((tensorBridge Z).hom.app C).app A ≫ sheafHomEvalEquiv Z C A B x := by
  rw [sheafHomEvalEquiv_eq_curryPair, Iso.hom_inv_id_app_app_assoc]

/-- The bijection of [Stacks, Tag 08DI] is natural in its source variable. -/
theorem curryPair_naturalLeft (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    DerivedInternalHomPullback.Transpose.TensorHomEquivNaturalLeft
      (Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (internalHomTensorPair Z) (curryPair Z) :=
  DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace Z

section Crossing

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-- The canonical map of [Stacks, Tag 08I3] against a morphism into the derived internal hom: for
`x : C ⟶ R SheafHom(A, B)` the transpose of `Lh^*x` followed by the canonical map is the
monoidality comparison of [Stacks, Tag 079U] followed by the derived pullback of the transpose of
`x`. -/
theorem curryPair_map_comp_pullbackSheafHomMap {C A B : DerivedCategory (Mod Z.sheaf)}
    (x : C ⟶ sheafHomObj Z A B) :
    curryPair W _ _ _ ((derivedPullbackFunctor h).map x ≫ pullbackSheafHomMap h A B) =
      (pullbackTensorPairIso h).inv.app (C, A) ≫
        (derivedPullbackFunctor h).map (curryPair Z _ _ _ x) := by
  have hh := DerivedInternalHomPullback.Transpose.map_comp_homComparison_adjoint
    (derivedPullbackFunctor h) (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom W.sheaf) (internalHomTensorPair Z)
    (internalHomTensorPair W) (curryPair Z) (curryPair W) (pullbackTensorPairIso h)
    (curryPair_naturalLeft Z) (curryPair_naturalLeft W) x
  convert hh using 2
  rfl

/-- The comparison `Lh^*C ⊗^𝐋 Lh^*A ≅ Lh^*(C ⊗^𝐋 A)` through which the canonical map of
[Stacks, Tag 08I3] is computed: the monoidality isomorphism of [Stacks, Tag 079U] at the derived
tensor product the derived internal hom is stated over, conjugated by the comparisons of the two
derived tensor products. -/
def pullbackEvalIso (C A : DerivedCategory (Mod Z.sheaf)) :
    tensorObj W ((derivedPullbackFunctor h).obj C) ((derivedPullbackFunctor h).obj A) ≅
      (derivedPullbackFunctor h).obj (tensorObj Z C A) :=
  (((tensorBridge W).app _).app _).symm ≪≫ ((pullbackTensorPairIso h).app (C, A)).symm ≪≫
    (derivedPullbackFunctor h).mapIso (((tensorBridge Z).app C).app A)

/-- The canonical map of [Stacks, Tag 08I3] against a morphism into the derived internal hom,
read through `sheafHomEvalEquiv`: for `x : C ⟶ R SheafHom(A, B)`, the transpose of
`Lh^*x ≫ (Lh^*R SheafHom(A, B) ⟶ R SheafHom(Lh^*A, Lh^*B))` is `pullbackEvalIso` followed by the
derived pullback of the transpose of `x`. -/
theorem sheafHomEvalEquiv_map_comp_pullbackSheafHomMap {C A B : DerivedCategory (Mod Z.sheaf)}
    (x : C ⟶ sheafHomObj Z A B) :
    sheafHomEvalEquiv W _ _ _ ((derivedPullbackFunctor h).map x ≫ pullbackSheafHomMap h A B) =
      (pullbackEvalIso h C A).hom ≫
        (derivedPullbackFunctor h).map (sheafHomEvalEquiv Z C A B x) := by
  rw [sheafHomEvalEquiv_eq_curryPair, curryPair_map_comp_pullbackSheafHomMap,
    curryPair_eq_sheafHomEvalEquiv]
  simp only [pullbackEvalIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]

end Crossing

end Pullback

/-! ### The comparison `boxSheafHomMap` at a pure pair -/

section Box

variable {X Y W : RingedSpace.{u, u}} (p : W ⟶ X) (q : W ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison `boxSheafHomMap` at a pure pair: for `x : C ⟶ R SheafHom(K, K')` on `X`
and `y : D ⟶ R SheafHom(M, M')` on `Y`, the transpose of
`Lp^*C ⊗^𝐋 Lq^*D --Lp^*x ⊗ Lq^*y--> Lp^*R SheafHom(K, K') ⊗^𝐋 Lq^*R SheafHom(M, M')
  --boxSheafHomMap--> R SheafHom(K ⊠ M, K' ⊠ M')`
is the flip of the middle two factors followed by the tensor product of the derived pullbacks of
the transposes of `x` and of `y`, each preceded by `pullbackEvalIso`. -/
theorem sheafHomEvalEquiv_tensorMap_comp_boxSheafHomMap {C K K' : DerivedCategory (Mod X.sheaf)}
    {D M M' : DerivedCategory (Mod Y.sheaf)} (x : C ⟶ sheafHomObj X K K')
    (y : D ⟶ sheafHomObj Y M M') :
    sheafHomEvalEquiv W _ _ _ (tensorMap W ((derivedPullbackFunctor p).map x)
        ((derivedPullbackFunctor q).map y) ≫ boxSheafHomMap p q K K' M M') =
      middleFour W ((derivedPullbackFunctor p).obj C) ((derivedPullbackFunctor q).obj D)
          ((derivedPullbackFunctor p).obj K) ((derivedPullbackFunctor q).obj M) ≫
        tensorMap W ((pullbackEvalIso p C K).hom ≫
            (derivedPullbackFunctor p).map (sheafHomEvalEquiv X C K K' x))
          ((pullbackEvalIso q D M).hom ≫
            (derivedPullbackFunctor q).map (sheafHomEvalEquiv Y D M M' y)) := by
  rw [boxSheafHomMap, ← Category.assoc, tensorMap_comp,
    sheafHomEvalEquiv_tensorMap_comp_sheafHomTensorMap,
    sheafHomEvalEquiv_map_comp_pullbackSheafHomMap, sheafHomEvalEquiv_map_comp_pullbackSheafHomMap]

end Box

end Stacks.Cohomology.DerivedKunnethExt

end
