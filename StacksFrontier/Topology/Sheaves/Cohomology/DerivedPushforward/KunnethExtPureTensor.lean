module

public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionTransposeReduction
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Künneth morphisms at a pure pair of morphisms

Let `a : X ⟶ S`, `b : Y ⟶ S`, `p : W ⟶ X`, `q : W ⟶ Y` and `f : W ⟶ S` be morphisms of ringed
spaces with `p ≫ a = f` and `q ≫ b = f`.  The relative Künneth morphism of [Stacks, Tag 0FLP]
and the Künneth morphism for Ext of [Stacks, Tag 0FXY] are both morphisms out of a derived
tensor product on `S`,

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ Rf_*(K ⊠ M)` and
`Ra_*R𝓗om(K, K') ⊗^𝐋_{𝒪_S} Rb_*R𝓗om(M, M') ⟶ Rf_*(R𝓗om(K ⊠ M, K' ⊠ M'))`.

Each of them is computed at a pure pair: given `s : Z₁ ⟶ Ra_*(-)` and `t : Z₂ ⟶ Rb_*(-)`, the
adjoint transpose under `Lf^* ⊣ Rf_*` of the composite of `s ⊗ t` with the Künneth morphism is
expressed in terms of `s` and `t` alone.

## Main results

* `Stacks.Cohomology.DerivedKunnethExt.homEquiv_symm_kunnethMap`: the relative Künneth morphism
  of [Stacks, Tag 0FLP] at a pure pair.
* `Stacks.Cohomology.DerivedKunnethExt.homEquiv_symm_kunnethExtMap`: the Künneth morphism for
  Ext of [Stacks, Tag 0FXY] at a pure pair.
* `Stacks.Cohomology.DerivedKunnethExt.tensorMap_comp`: derived tensor products of morphisms
  compose factorwise.
* `Stacks.Cohomology.DerivedKunnethExt.tensorMap_id_comp_sheafHomEval`: evaluating at a morphism
  into the derived internal hom gives its transpose.

## References

* [Stacks Project, Tag 0FXY](https://stacks.math.columbia.edu/tag/0FXY)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The derived tensor product of morphisms, and evaluation at a morphism -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Derived tensor products of morphisms compose factorwise. -/
theorem tensorMap_comp {A A' A'' B B' B'' : DerivedCategory (Mod Z.sheaf)} (x : A ⟶ A')
    (x' : A' ⟶ A'') (y : B ⟶ B') (y' : B' ⟶ B'') :
    tensorMap Z x y ≫ tensorMap Z x' y' = tensorMap Z (x ≫ x') (y ≫ y') :=
  (CategoryTheory.bifunctor_map_comp_both (Functor.uncurry.obj
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)) x x' y y').symm

/-- Evaluating at a morphism into the derived internal hom gives its transpose. For
`x : C ⟶ R SheafHom(A, B)` the composite

`C ⊗^𝐋_{𝒪_Z} A --x ⊗ 1--> R SheafHom(A, B) ⊗^𝐋_{𝒪_Z} A --eval--> B`

is the image of `x` under the tensor–internal-hom bijection of [Stacks, Tag 08DI], up to the
comparison `Stacks.Cohomology.DerivedKunnethExt.tensorBridge` of the two derived tensor
products. -/
theorem tensorMap_id_comp_sheafHomEval (A B C : DerivedCategory (Mod Z.sheaf))
    (x : C ⟶ sheafHomObj Z A B) :
    tensorMap Z x (𝟙 A) ≫ sheafHomEval Z A B =
      ((tensorBridge Z).inv.app C).app A ≫
        AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) C A B x := by
  have hnat : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).map x).app A ≫
        ((tensorBridge Z).inv.app (sheafHomObj Z A B)).app A =
      ((tensorBridge Z).inv.app C).app A ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite Z.sheaf)).map x).app A :=
    CategoryTheory.NatTrans.congr_app ((tensorBridge Z).inv.naturality x) A
  have hcl : ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite Z.sheaf)).map x).app A ≫
        AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) (sheafHomObj Z A B) A B
          (𝟙 (sheafHomObj Z A B)) =
      AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) C A B x :=
    (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source
          (Stacks.SheafOfModules.ringedSite Z.sheaf) (A := sheafHomObj Z A B) (A' := C) (B := A)
          (Z := B) x (𝟙 (sheafHomObj Z A B))).symm.trans
      (congrArg (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) C A B) (Category.comp_id x))
  rw [tensorMap, CategoryTheory.Functor.map_id, Category.comp_id, sheafHomEval,
    ← Category.assoc, hnat, Category.assoc]
  conv_lhs => rw [hcl]

end OneSpace

/-! ### The two Künneth morphisms at a pure pair -/

section Kunneth

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The relative Künneth morphism of [Stacks, Tag 0FLP] at a pure pair. For
`s : Z₁ ⟶ Ra_*K` and `t : Z₂ ⟶ Rb_*M` the adjoint transpose of

`Z₁ ⊗^𝐋_{𝒪_S} Z₂ --s ⊗ t--> Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M --Künneth--> Rf_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is the monoidality isomorphism of [Stacks, Tag 079U] for `Lf^*` at `(Z₁, Z₂)`, followed by the
derived tensor product on `W` of `Lf^*s` and of `Lf^*t`, each followed by the counit leg of its
side. -/
theorem homEquiv_symm_kunnethMap {Z₁ Z₂ : DerivedCategory (Mod S.sheaf)}
    (K : DerivedCategory (Mod X.sheaf)) (M : DerivedCategory (Mod Y.sheaf))
    (s : Z₁ ⟶ (derivedPushforwardFunctor a).obj K)
    (t : Z₂ ⟶ (derivedPushforwardFunctor b).obj M) :
    ((derivedAdjunction f).homEquiv _ _).symm
        (tensorMap S s t ≫ Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app (Z₁, Z₂) ≫
        tensorMap W
          ((derivedPullbackFunctor f).map s ≫
            (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p f hp).app K)
          ((derivedPullbackFunctor f).map t ≫
            (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg b q f hq).app M) :=
  Stacks.Cohomology.DerivedKunneth.homEquiv_symm_adjunctionBitensorMap
    (derivedAdjunction f) _ _
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p f hp)
    (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg b q f hq) s t

/-- The Künneth morphism for Ext of [Stacks, Tag 0FXY] at a pure pair. For
`s : Z₁ ⟶ Ra_*R𝓗om(K, K')` and `t : Z₂ ⟶ Rb_*R𝓗om(M, M')` the adjoint transpose of

`Z₁ ⊗^𝐋_{𝒪_S} Z₂ --s ⊗ t--> Ra_*R𝓗om(K, K') ⊗^𝐋_{𝒪_S} Rb_*R𝓗om(M, M')
  --Künneth--> Rf_*(R𝓗om(K ⊠ M, K' ⊠ M'))`

is the monoidality isomorphism of [Stacks, Tag 079U] for `Lf^*` at `(Z₁, Z₂)`, followed by the
derived tensor product on `W` of `Lf^*s` and of `Lf^*t` — each followed by the counit leg of its
side — followed by `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`. -/
theorem homEquiv_symm_kunnethExtMap {Z₁ Z₂ : DerivedCategory (Mod S.sheaf)}
    (K K' : DerivedCategory (Mod X.sheaf)) (M M' : DerivedCategory (Mod Y.sheaf))
    (s : Z₁ ⟶ (derivedPushforwardFunctor a).obj (sheafHomObj X K K'))
    (t : Z₂ ⟶ (derivedPushforwardFunctor b).obj (sheafHomObj Y M M')) :
    ((derivedAdjunction f).homEquiv _ _).symm
        (tensorMap S s t ≫ kunnethExtMap a b p q f hp hq K K' M M') =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app (Z₁, Z₂) ≫
        tensorMap W
          ((derivedPullbackFunctor f).map s ≫
            (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p f hp).app
              (sheafHomObj X K K'))
          ((derivedPullbackFunctor f).map t ≫
            (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg b q f hq).app
              (sheafHomObj Y M M')) ≫
        boxSheafHomMap p q K K' M M' := by
  refine Eq.trans (congrArg _ (Category.assoc (tensorMap S s t)
      (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
        (sheafHomObj X K K') (sheafHomObj Y M M'))
      ((derivedPushforward f).map (boxSheafHomMap p q K K' M M'))).symm)
    (Eq.trans ((derivedAdjunction f).homEquiv_naturality_right_symm _ _) ?_)
  exact Eq.trans (congrArg (· ≫ boxSheafHomMap p q K K' M M')
      (homEquiv_symm_kunnethMap a b p q f hp hq (sheafHomObj X K K') (sheafHomObj Y M M') s t))
    (Category.assoc _ _ _)

end Kunneth

end Stacks.Cohomology.DerivedKunnethExt

end
