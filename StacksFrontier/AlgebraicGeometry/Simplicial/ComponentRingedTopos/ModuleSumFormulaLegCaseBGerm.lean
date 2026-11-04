module

public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegCaseBSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSite

/-!
# The case-(B) leg equation of Stacks 0D72 (6)

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE. This file proves the leg equation of Stacks 0D72 (6) in case (B),
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB`: the `φ`th summand inclusion of
the module direct-sum formula of case (B) is the canonical leg of `φ`.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB`: the leg equation of
  Stacks 0D72 (6) in case (B).
* `Stacks.PullbackMonoidalSite.pullbackIso_inv_germ_map`: in the colimit model of the pullback of
  presheaves of modules, the germ at an index `T : CostructuredArrow F.op U` of the pure tensor
  `1 ⊗ m` is carried by the inverse of the model comparison to the restriction along `T.hom` of
  `CategoryTheory.PresheafOfModules.pullbackAdjUnit` at `m`.
* `CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_presheafSumFormulaB_inv_app_tmul`: the
  presheaf-level summand inclusion of case (B) on a pure tensor.
* `CategoryTheory.CocontinuousSimplicialSite`'s
  `homEquiv_sigma_ι_comp_presheafSumFormulaB_inv_app_apply` and
  `restrict_moduleSheafFunctor_map_unit_app_pullbackAdjUnit`: the two legs of the case-(B) leg
  equation on a section, each the restriction along the cross-fibre arrow `(φ, 𝟙)` of a morphism
  `η` out of the presheaf-level pullback applied to
  `CategoryTheory.PresheafOfModules.pullbackAdjUnit`.
* `Stacks.SheafOfModules.RestrictRan.sourceMap_app_apply`: the morphism
  `Stacks.SheafOfModules.RestrictRan.sourceMap w M N α` agrees with `α` on sections.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PresheafOfModules Stacks.PullbackModel Stacks.PullbackColimit

universe u

namespace Stacks.PullbackMonoidalSite

section Germ

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] {F : C ⥤ D}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Dᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ F.op ⋙ R)

/-- The germ at an index `T` of the pure tensor `1 ⊗ m`, carried by the inverse of the model
comparison `Stacks.PullbackColimit.pullbackIso`, is the restriction along `T.hom` of
`CategoryTheory.PresheafOfModules.pullbackAdjUnit` at `m`. -/
theorem pullbackIso_inv_germ_map
    (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) {U : Dᵒᵖ}
    (T : CostructuredArrow F.op U) (m : M.obj T.left) :
    Hom.app ((Stacks.PullbackColimit.pullbackIso α).inv.app M) U
        (germ F R ((extendScalars α).obj M) T 1 (tmul (α.app T.left).hom 1 m)) =
      ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj M).map T.hom
        (pullbackAdjUnit (toRingCatPullback α) M T.left m) := by
  refine Eq.trans (congrArg
    (Hom.app ((Stacks.PullbackColimit.pullbackIso α).inv.app M) U)
    (germ_eq_map_unit F R ((extendScalars α).obj M) T (tmul (α.app T.left).hom 1 m))) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    ((Stacks.PullbackColimit.pullbackIso α).inv.app M) T.hom
    (unit F R ((extendScalars α).obj M) T.left (tmul (α.app T.left).hom 1 m))) ?_
  exact congrArg
    (fun z => ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj M).map T.hom z)
    (pullbackIso_inv_germ α M T.left m)

end Germ

end Stacks.PullbackMonoidalSite

namespace Stacks.SheafOfModules.RestrictRan

/-- The component at `W` of `Stacks.SheafOfModules.RestrictRan.sourceMap w M N α` sends a section
`x` to `α` applied to `x`. -/
theorem sourceMap_app_apply {X : Type u} [Category.{u} X] {Y : Type u} [Category.{u} Y]
    (w : X ⥤ Y) {T : Yᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} T)
    (N : PresheafOfModules.{u} (w.op ⋙ T))
    (α : (PresheafOfModules.pushforward₀.{u} w T).obj M ⟶ N) (W : Xᵒᵖ)
    (x : M.obj (w.op.obj W)) :
    ((Stacks.SheafOfModules.RestrictRan.sourceMap w M N α).app W).hom x =
      PresheafOfModules.Hom.app α W x :=
  PresheafOfModules.toPresheaf_map_app_apply α W x

end Stacks.SheafOfModules.RestrictRan

section CaseB

open AlgebraicGeometry
open Stacks.Sites.ComponentModuleSumFormula

namespace CategoryTheory.CocontinuousSimplicialSite

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  isRightAdjointPushforwardComponentB

/-- The `φ`th summand inclusion of `CategoryTheory.CocontinuousSimplicialSite.presheafSumFormulaB`,
followed by the inverse of that formula, sends the pure tensor `1 ⊗ z` over a degree-`m` object to
the restriction along the cross-fibre arrow `(φ, 𝟙)` of
`CategoryTheory.PresheafOfModules.pullbackAdjUnit` at `z`. -/
theorem sigma_ι_comp_presheafSumFormulaB_inv_app_tmul (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : PresheafOfModules.{u}
      (((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj) ⋙ forget₂ CommRingCat RingCat))
    (W : (C.underlying.obj (op m))ᵒᵖ)
    (z : X.obj (componentCostructuredArrow C W.unop φ).left) :
    PresheafOfModules.Hom.app
        ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
          (presheafSumFormulaB C P n m).inv).app X) W
        (tmul ((ringTransition C P.obj φ).app W).hom 1 z) =
      ((PresheafOfModules.pullback.{u} (toRingCatPullback
            (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).obj X).map
          (componentCostructuredArrow C W.unop φ).hom
        (pullbackAdjUnit (toRingCatPullback
            (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) X
          (componentCostructuredArrow C W.unop φ).left z) := by
  refine Eq.trans (congrArg
    (fun t : (transitionPullbackPresheafModules C P.obj φ).obj X ⟶
        (PresheafOfModules.pullback.{u} (toRingCatPullback
              (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) ⋙
            PresheafOfModules.pushforward₀OfCommRingCat
              (Grothendieck.ι C.underlying (op m)) P.obj).obj X =>
      PresheafOfModules.Hom.app t W (tmul ((ringTransition C P.obj φ).app W).hom 1 z))
    (sigma_ι_comp_presheafSumFormulaB_inv C P n m φ X)) ?_
  refine Eq.trans (congrArg
    (fun a => PresheafOfModules.Hom.app ((Stacks.PullbackColimit.pullbackIso
          (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))).inv.app X)
        (op ((Grothendieck.ι C.underlying (op m)).obj W.unop))
        (germ (Grothendieck.ι C.underlying (op n)) P.obj
          ((Stacks.PullbackModel.extendScalars
            (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))).obj X)
          (componentCostructuredArrow C W.unop φ) 1 a))
    (extendScalarsIdIso_inv_app_apply ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj) X
      (componentCostructuredArrow C W.unop φ).left z)) ?_
  exact Stacks.PullbackMonoidalSite.pullbackIso_inv_germ_map
    (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)) X
    (componentCostructuredArrow C W.unop φ) z

/-- Let `η` be a morphism out of the presheaf-level pullback of `X` along the degree-`n` component
inclusion. The transpose along extension of scalars of the presheaf-level summand inclusion
followed by the degree-`m` restriction of `η` sends a section `z` to the restriction along the
cross-fibre arrow `(φ, 𝟙)` of `η` applied to `CategoryTheory.PresheafOfModules.pullbackAdjUnit`
at `z`. -/
theorem homEquiv_sigma_ι_comp_presheafSumFormulaB_inv_app_apply
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (N : PresheafOfModules.{u} (totalRingSheafB C P).obj)
    (η : (PresheafOfModules.pullback.{u} (toRingCatPullback
        (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).obj X.val ⟶ N)
    (W : ((situation C).component m)ᵒᵖ)
    (z : X.val.obj ((transitionFunctorB C φ).op.obj W)) :
    PresheafOfModules.Hom.app
        ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).homEquiv
          ((PresheafOfModules.pushforward₀.{u} (transitionFunctorB C φ)
            (ringSheafB C P n).obj).obj X.val)
          ((PresheafOfModules.pushforward₀.{u}
            (SimplicialSiteSituation.componentFunctor (situation C) m)
            (totalRingSheafB C P).obj).obj N)
          ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
                (presheafSumFormulaB C P n m).inv).app X.val ≫
            (PresheafOfModules.pushforward₀.{u}
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              (totalRingSheafB C P).obj).map η)) W z =
      N.map (componentCostructuredArrow C W.unop φ).hom
        (PresheafOfModules.Hom.app η
          ((Grothendieck.ι C.underlying (op n)).op.obj
            (componentCostructuredArrow C W.unop φ).left)
          (pullbackAdjUnit (toRingCatPullback
              (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) X.val
            (componentCostructuredArrow C W.unop φ).left z)) := by
  refine Eq.trans (Stacks.PullbackModel.extendScalarsAdjunction_homEquiv_app_apply
    (ringTransition C P.obj φ)
    ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
          (presheafSumFormulaB C P n m).inv).app X.val ≫
      (PresheafOfModules.pushforward₀.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).map η) W z) ?_
  refine Eq.trans (congrArg
    (fun a => PresheafOfModules.Hom.app η
      (op ((Grothendieck.ι C.underlying (op m)).obj W.unop)) a)
    (sigma_ι_comp_presheafSumFormulaB_inv_app_tmul C P n m φ X.val W z)) ?_
  exact PresheafOfModules.naturality_apply η (componentCostructuredArrow C W.unop φ).hom
    (pullbackAdjUnit (toRingCatPullback
        (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) X.val
      (componentCostructuredArrow C W.unop φ).left z)

/-- Let `η` be a morphism out of the presheaf-level pullback of `X` such that the unit of
`g_{n!} ⊣ g_n^*` at `X` is, on underlying presheaves of modules, the pullback transpose of `η`.
Then the image of a section `y` under that unit, restricted along `j` and along the cross-fibre
arrow `(φ, 𝟙)`, is the restriction along `(φ, 𝟙)` of `η` applied to
`CategoryTheory.PresheafOfModules.pullbackAdjUnit` at the restriction of `y` along `j`. -/
theorem restrict_moduleSheafFunctor_map_unit_app_pullbackAdjUnit
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (η : (PresheafOfModules.pullback.{u} (toRingCatPullback
        (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).obj X.val ⟶
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val)
    (hu : (((situation C).componentModuleLowerShriekAdjunction
          (totalRingSheafB C P) n).unit.app X).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatPullback
          (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).homEquiv X.val
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val η)
    (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
          (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).obj).app
        j.right
      ((((situation C).restrict n).obj
            (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))).obj.map
          j.hom
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          (((situation C).componentModuleLowerShriekAdjunction
            (totalRingSheafB C P) n).unit.app X)).hom.app V y)) =
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val.map
          (componentCostructuredArrow C j.right.unop φ).hom
        (PresheafOfModules.Hom.app η
          ((Grothendieck.ι C.underlying (op n)).op.obj
            (componentCostructuredArrow C j.right.unop φ).left)
          (pullbackAdjUnit (toRingCatPullback
              (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) X.val
            (componentCostructuredArrow C j.right.unop φ).left
            ((X.val.presheaf.map j.hom).hom y))) := by
  refine Eq.trans (congrArg
    (fun t : X.val ⟶ (PresheafOfModules.pushforward.{u} (toRingCatPullback
          (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val =>
      (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).obj).app
          j.right
        ((((situation C).restrict n).obj
              (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
                (((situation C).componentModuleLowerShriek
                  (totalRingSheafB C P) n).obj X))).obj.map j.hom
          (PresheafOfModules.Hom.app t V y)))
    (hu.trans rfl)) ?_
  refine Eq.trans (congrArg
    (fun a : (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val.obj
        ((Grothendieck.ι C.underlying (op n)).op.obj V) =>
      (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).obj).app
          j.right
        ((((situation C).restrict n).obj
              (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
                (((situation C).componentModuleLowerShriek
                  (totalRingSheafB C P) n).obj X))).obj.map j.hom a))
    (PresheafOfModules.homEquiv_app_pullbackAdjUnit (toRingCatPullback
      (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) η V y)) ?_
  refine Eq.trans (congrArg
    (fun a : (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val.obj
        ((Grothendieck.ι C.underlying (op n)).op.obj
          (componentCostructuredArrow C j.right.unop φ).left) =>
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val.map
        (componentCostructuredArrow C j.right.unop φ).hom a)
    (PresheafOfModules.naturality_apply η ((Grothendieck.ι C.underlying (op n)).op.map j.hom)
      (pullbackAdjUnit (toRingCatPullback
          (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) X.val V y)).symm) ?_
  exact congrArg
    (fun a : ((PresheafOfModules.pullback.{u} (toRingCatPullback
          (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).obj X.val).obj
        ((Grothendieck.ι C.underlying (op n)).op.obj
          (componentCostructuredArrow C j.right.unop φ).left) =>
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val.map
        (componentCostructuredArrow C j.right.unop φ).hom
        (PresheafOfModules.Hom.app η
          ((Grothendieck.ι C.underlying (op n)).op.obj
            (componentCostructuredArrow C j.right.unop φ).left) a))
    (PresheafOfModules.naturality_apply
      ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatPullback
        (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).unit.app X.val) j.hom y).symm

/-- In case (B), the `φ`th summand inclusion of the module direct-sum formula
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaB` is the canonical leg
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`. -/
theorem moduleSumFormulaLegEqB (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    ModuleSumFormulaLegEqB C P φ := by
  refine moduleSumFormulaLegEqB_of_ranπ C P φ (fun X V j y => ?_)
  refine Eq.trans (ranπ_moduleSheafFunctor_map_comp_eq_sourceMap C P φ X _ _ _
    (homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map
      C P n m φ X) V j y) ?_
  refine Eq.trans (Stacks.SheafOfModules.RestrictRan.sourceMap_app_apply
    (transitionFunctorB C φ) _ _ _ j.right ((X.val.presheaf.map j.hom).hom y)) ?_
  refine Eq.trans (homEquiv_sigma_ι_comp_presheafSumFormulaB_inv_app_apply C P n m φ X _ _ j.right
    ((X.val.presheaf.map j.hom).hom y)) ?_
  refine Eq.trans ?_
    (ranπ_moduleSheafFunctor_map_homEquiv_moduleSumFormulaLeg_app C P φ X V j y).symm
  exact (restrict_moduleSheafFunctor_map_unit_app_pullbackAdjUnit C P φ X _
    (componentModuleLowerShriekAdjunction_unit_app_val C P n X) V j y).symm

end CategoryTheory.CocontinuousSimplicialSite

end CaseB

end
