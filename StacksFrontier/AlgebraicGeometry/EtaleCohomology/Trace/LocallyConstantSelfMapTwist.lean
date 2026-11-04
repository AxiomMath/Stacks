module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.LocallyConstantPushforward

/-!
# The canonical map `M_X ⟶ s_* M_X` on locally constant maps

Under the identification of the constant sheaf `M_X` with the sheaf of locally constant
`M`-valued maps ([Stacks, Tag 03P5]), the canonical map `M_X ⟶ s_* M_X` of a self-map `s` of `X`
(adjoint to `s^{-1} M_X ≅ M_X`) is the pull back of locally constant maps along the base change
of `s`. This identifies the deck action on `f_* M_V` of a Galois cover used in Step 8 of the proof
of [Stacks, Tag 03UG] with the twist `M_V ⟶ a_* M_V` on which Step 9 operates.

## Main results

* `Stacks.EtaleCohomology.constantSheafToLocallyConstant_comp_locallyConstantToDirectImage`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 8.
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {X : Scheme.{u}} (s : X ⟶ X)

/-- **The canonical map `M_X ⟶ s_* M_X` is the pull back of locally constant maps** along the base
change of `s`, through `M_X ≅ 𝓛_X(M)`. -/
theorem constantSheafToLocallyConstant_comp_locallyConstantToDirectImage :
    constantSheafToSmallEtaleLocallyConstantMapsModule Λ X M ≫ locallyConstantToDirectImage Λ M s =
      constantSelfMapTwist Λ M s ≫ (etaleModuleDirectImage.{u, r} Λ s).map
        (constantSheafToSmallEtaleLocallyConstantMapsModule Λ X M) := by
  apply constantSheaf_hom_ext Λ M
  have h1 := constantSheafSection_comp_constantSelfMapTwist Λ M s
  show constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
      (constantSheafToSmallEtaleLocallyConstantMapsModule Λ X M).hom.app _ ≫
        (locallyConstantToDirectImage Λ M s).hom.app _ =
    (constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
      (constantSelfMapTwist Λ M s).hom.app (op (Scheme.Etale.mk (𝟙 X)))) ≫
        (constantSheafToSmallEtaleLocallyConstantMapsModule Λ X M).hom.app _
  rw [h1]
  ext m
  show (locallyConstantToDirectImage Λ M s).hom.app _
      ((constantSheafToSmallEtaleLocallyConstantMapsModule Λ X M).hom.app _
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app _ m)) =
    (constantSheafToSmallEtaleLocallyConstantMapsModule Λ X M).hom.app _
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app _ m)
  rw [constantSheafToSmallEtaleLocallyConstantMapsModule_unit,
    constantSheafToSmallEtaleLocallyConstantMapsModule_unit, locallyConstantToDirectImage_hom_app]
  rfl

section Pushforward

variable (Λ : Type r) [Ring Λ] (M : Type (max (u + 1) r)) [AddCommGroup M] [Module Λ M]
  {U V : Scheme.{u}} (f : V ⟶ U) (a : V ⟶ V) (ha : a ≫ f = f)

/-- The base change comparison for `a ≫ f = f`, followed by the projection, is the endomorphism
`W ×_U V ⟶ W ×_U V` induced by `a`. -/
lemma smallEtaleBaseChangeComp'_left_comp_fst (W : U.Etale) :
    ((smallEtaleBaseChangeComp' a f f ha.symm).hom.app W).left ≫
        pullback.fst ((smallEtaleBaseChange f).obj W).hom a =
      pullback.map W.hom f W.hom f (𝟙 _) a (𝟙 _) (by simp) (by simp [ha]) := by
  have h1 := smallEtaleBaseChangeComp'_fst_fst a f f ha.symm W
  have hc := pullback.condition (f := ((smallEtaleBaseChange f).obj W).hom) (g := a)
  have hw := MorphismProperty.Over.w ((smallEtaleBaseChangeComp' a f f ha.symm).hom.app W)
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans (h1.trans ?_)
    exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
  · calc _ = ((smallEtaleBaseChangeComp' a f f ha.symm).hom.app W).left ≫
          (pullback.fst ((smallEtaleBaseChange f).obj W).hom a ≫
            ((smallEtaleBaseChange f).obj W).hom) := Category.assoc _ _ _
      _ = ((smallEtaleBaseChangeComp' a f f ha.symm).hom.app W).left ≫
          (pullback.snd ((smallEtaleBaseChange f).obj W).hom a ≫ a) := congrArg (_ ≫ ·) hc
      _ = (((smallEtaleBaseChangeComp' a f f ha.symm).hom.app W).left ≫
          pullback.snd ((smallEtaleBaseChange f).obj W).hom a) ≫ a := (Category.assoc _ _ _).symm
      _ = ((smallEtaleBaseChange f).obj W).hom ≫ a := congrArg (· ≫ a) hw
      _ = _ := (pullback.lift_snd _ _ _).symm

/-- **The deck action on `f_* 𝓛_V(M)` is `f_*` of the pull back along `a`**, followed by the
composition isomorphism `f_* a_* = f_*`. -/
theorem locallyConstantPushforwardMap_eq_map_comp :
    locallyConstantPushforwardMap Λ M f f a ha =
      (etaleModuleDirectImage.{u, r} Λ f).map (locallyConstantToDirectImage Λ M a) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a f f ha.symm).hom.app _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  rw [locallyConstantPushforwardMap_hom_app]
  show _ =
    (locallyConstantToDirectImage Λ M a).hom.app (op ((smallEtaleBaseChange f).obj W.unop)) ≫
    ((etaleModuleDirectImageComp.{u, r} Λ a f f ha.symm).hom.app
      (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ V M)).hom.app W
  rw [etaleModuleDirectImageComp_hom_app_hom_app, locallyConstantToDirectImage_hom_app,
    ← smallEtaleBaseChangeComp'_left_comp_fst f a ha W.unop]
  rfl

end Pushforward

end Stacks.EtaleCohomology

end
