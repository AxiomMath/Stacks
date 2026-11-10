module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedSumFormulaLegSummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionTargetSum

/-!
# The summand inclusions of the target identification of Stacks 0D9E (2)

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site and `g_n` the inclusion of the degree-`n` simplicial component.
`CategoryTheory.SimplicialSiteSituation.moduleProjectionTargetIso` constructs the identification

`g_m^*(g_{n!}O_n ⊗^L_O K) ≅ ⨁_{φ : [n] ⟶ [m]} K_m`

of the target of the canonical map of Stacks 0D9E (2) restricted to degree `m`. That construction
uses only the *existence* of the componentwise direct-sum formula of Stacks 0D72 (6). This file
describes the `φ`th summand inclusion of that identification.

The description is built in three layers, innermost first.

* At the structure sheaf of the component, the `φ`th summand inclusion of
  `…componentModuleLowerShriekUnitRestrictionSum` is the identification `O_m ≅ f_φ^*O_n` followed
  by the canonical leg `…moduleSumFormulaLeg` of Stacks 0D72 (6). This is the leg equation
  `…ModuleSumFormulaLegEq` evaluated at the structure sheaf, and it is the only layer carrying
  mathematical content; the evaluation itself is the plumbing of
  `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation`.
* At the level of functors, the `φ`th summand inclusion of
  `…componentModuleLowerShriekUnitTensorRestrictionSum` is the component's left unitor, followed by
  the previous layer tensored into the restriction, followed by Stacks 03EL.
* On derived categories, the `φ`th summand inclusion of `…moduleProjectionTargetIso` is the derived
  functor of the previous layer, read through the compositor. This is the generic
  `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv` instantiated at the target chain; no
  adjunction is involved, so the leg form
  `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_leg` is not the statement needed here.

## Main results

All in the namespace `CategoryTheory.SimplicialSiteSituation`.

* `ι_componentModuleLowerShriekUnitRestrictionSum_inv_sigma`: the `φ`th summand inclusion at the
  structure sheaf, with the direct-sum formula's own summand inclusion still on the right-hand
  side.
* `ι_componentModuleLowerShriekUnitRestrictionSum_inv`: **the same with the canonical leg of Stacks
  0D72 (6)** on the right-hand side, granted the leg equation `…ModuleSumFormulaLegEq`.
* `biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv`: **the `φ`th summand
  inclusion of the sheaf-level target identification**.
* `biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv_leg`: the same with the
  canonical leg, granted the leg equation.
* `biproduct_ι_moduleProjectionTargetIso_inv`: **the `φ`th summand inclusion of
  `…moduleProjectionTargetIso`**.
* `biproduct_ι_moduleProjectionTargetIso_inv_leg`: the same with the sheaf-level summand inclusion
  expanded into the canonical leg.

## Implementation notes

*Why the proofs are written in term mode.* The type of
`…componentModuleLowerShriekUnitRestrictionSum` mixes the two spellings of a component's modules:
its left-hand object is stated through `…componentModulesRestriction`, so the ambient category is
`AlgebraicGeometry.RingedTopos.Modules` of `…componentRingedTopos`, while the family summed over on
the right is spelled with `SheafOfModules` over `…componentRingSheaf`. The two agree by a delta
step, which the elaborator takes, but not at `implicit` transparency, so the coproduct object in
that type is not type-correct at the transparency `simp` and `rw` build their motives at: every
rewriting tactic fails there, `simp` reporting that it made no progress and `rw` that the motive is
not type correct. Term-mode `Eq.trans` and `congrArg` steps are checked at default transparency and
go through. Retyping the definition so that both sides are spelled with `SheafOfModules` is not an
option: the colimit instances of the component's modules are found only at the
`…componentRingedTopos` spelling.

*Why the chain is peeled locally rather than re-associated once.* Composition in these
categories is associative by `rfl`, so the inverse of the four-fold `CategoryTheory.Iso.trans` can
be presented right-nested by a single `show`. Doing so and then applying the summand-inclusion
lemmas of `CategoryTheory.Limits` at the head of the goal exceeds the kernel's heartbeat budget for
one declaration. Peeling one factor at a time instead — an associativity step, then the lemma for
that factor under a `congrArg` — keeps every defeq check small.

*Why the summand-inclusion lemmas carry their source and target functors explicitly.* Applied
under a `congrArg`, the natural isomorphism argument of
`CategoryTheory.Limits.HasColimit.ι_isoOfNatIso_inv` is a metavariable when its `HasColimit`
instances are synthesized, and synthesis then fails on an incomplete functor. Supplying the
functors by name leaves nothing to synthesize against.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n m : SimplexCategory)

/-- **The `φ`th summand inclusion of the direct-sum formula of Stacks 0D72 (6) at the structure
sheaf of the component.** The `φ`th inclusion of
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitRestrictionSum`, followed by
the inverse of that identification, is the identification `O_m ≅ f_φ^*O_n` of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` followed by the `φ`th summand
inclusion of the formula itself, evaluated at the structure sheaf. -/
theorem ι_componentModuleLowerShriekUnitRestrictionSum_inv_sigma (φ : n ⟶ m) :
    Sigma.ι (fun _ : n ⟶ m =>
        SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m)) φ ≫
      (S.componentModuleLowerShriekUnitRestrictionSum O n m).inv =
    (pullbackModulesObjUnitIso (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
      (Sigma.ι (fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ) φ ≫
          (S.moduleSumFormula O n m).inv).app
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ _) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun g => (g ≫ _) ≫ _)
    (HasColimit.ι_isoOfNatIso_inv_assoc
      (F := Discrete.functor (C := (S.componentRingedTopos O m).Modules)
        (((evaluation (SheafOfModules.{u}
                  (S.componentRingSheaf
                    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n))
                ((S.componentRingedTopos O m).Modules)).obj
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))).obj ∘
          fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ))
      (G := Discrete.functor (C := (S.componentRingedTopos O m).Modules)
        fun _ : n ⟶ m => SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m))
      _ (Discrete.mk φ) _)) ?_
  refine Eq.trans (congrArg (fun g => ((_ ≫ g) ≫ _) ≫ _)
    (HasColimit.ι_isoOfNatIso_inv
      (F := (Discrete.functor fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ) ⋙
        (evaluation (SheafOfModules.{u}
              (S.componentRingSheaf
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n))
            ((S.componentRingedTopos O m).Modules)).obj
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))
      (G := Discrete.functor (C := (S.componentRingedTopos O m).Modules)
        (((evaluation (SheafOfModules.{u}
                  (S.componentRingSheaf
                    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n))
                ((S.componentRingedTopos O m).Modules)).obj
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))).obj ∘
          fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ))
      _ (Discrete.mk φ))) ?_
  refine Eq.trans (congrArg (fun g => ((_ ≫ g) ≫ _) ≫ _) (Category.id_comp _)) ?_
  refine Eq.trans (congrArg (fun g => g ≫ _) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun g => (_ ≫ g) ≫ _)
    (colimitObjIsoColimitCompEvaluation_ι_inv
      (Discrete.functor fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ)
      (Discrete.mk φ) _)) ?_
  exact Category.assoc _ _ _

/-- **The `φ`th summand inclusion of the direct-sum formula of Stacks 0D72 (6) at the structure
sheaf, as the canonical leg.** Granted the leg equation
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq` — which
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEq_situation` proves in case (A) of
Stacks 09WE — the `φ`th inclusion of
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitRestrictionSum`, followed by
the inverse of that identification, is `O_m ≅ f_φ^*O_n` followed by the canonical leg
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` at the structure sheaf. -/
theorem ι_componentModuleLowerShriekUnitRestrictionSum_inv
    (hleg : S.ModuleSumFormulaLegEq O) (φ : n ⟶ m) :
    Sigma.ι (fun _ : n ⟶ m =>
        SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m)) φ ≫
      (S.componentModuleLowerShriekUnitRestrictionSum O n m).inv =
    (pullbackModulesObjUnitIso (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
      (S.moduleSumFormulaLeg O φ).app
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)) :=
  Eq.trans (S.ι_componentModuleLowerShriekUnitRestrictionSum_inv_sigma O n m φ)
    (congrArg
      (fun g => (pullbackModulesObjUnitIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom ≫ g)
      (NatTrans.congr_app (hleg φ)
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))))

/-- **The `φ`th summand inclusion of the sheaf-level target identification of Stacks 0D9E (2).**
The `φ`th biproduct inclusion of
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorRestrictionSum`,
followed by the inverse of that identification, is the inverse of the component's left unitor,
followed by the `φ`th summand inclusion at the structure sheaf tensored into the restriction, and
then Stacks 03EL at the degree-`m` inclusion.

The three middle steps of the chain — colimit preservation of `A ↦ g_m^* ⋙ (A ⊗_{O_m} -)`, the
comparison of a coproduct over a discrete category with a coproduct of values, and the summandwise
left unitor — contribute nothing beyond their standard summand-inclusion lemmas, so no new
description of `CategoryTheory.Limits.preservesColimitIso` or of
`CategoryTheory.SimplicialSiteSituation.componentModuleUnitTensorLeftUnitor` is needed. -/
theorem biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv (φ : n ⟶ m) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    letI : HasFiniteBiproducts
        ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    biproduct.ι (fun _ : n ⟶ m => S.componentModulesRestriction O m) φ ≫
        (S.componentModuleLowerShriekUnitTensorRestrictionSum O n m).inv =
      (S.restrictionTensorWhiskeredUnitIso O m).inv ≫
        (S.restrictionTensorWhiskered O m).map
            (Sigma.ι (fun _ : n ⟶ m =>
                SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m)) φ ≫
              (S.componentModuleLowerShriekUnitRestrictionSum O n m).inv) ≫
          (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  let : HasFiniteBiproducts
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  simp only [componentModuleLowerShriekUnitTensorRestrictionSum]
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Iso.trans_inv, Iso.symm_inv,
    biproduct.isoCoproduct_hom, Category.assoc, Functor.mapIso_inv, Functor.comp_map,
    Functor.whiskeringLeft_obj_map, biproduct.ι_desc_assoc, HasColimit.ι_isoOfNatIso_inv_assoc,
    Discrete.functor_obj_eq_as, Discrete.natIso_inv_app, ι_preservesColimitIso_inv_assoc,
    Iso.cancel_iso_inv_left]
  simp only [Discrete.compNatIsoDiscrete, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    Discrete.natIso_inv_app, Discrete.functor_obj_eq_as, Iso.refl_inv]
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun g => g ≫ (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom)
    (Functor.map_comp (S.restrictionTensorWhiskered O m) _ _).symm

/-- **The `φ`th summand inclusion of the sheaf-level target identification of Stacks 0D9E (2), as
the canonical leg.** This is `biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv`
with the inner summand inclusion replaced, granted the leg equation of Stacks 0D72 (6), by the
canonical leg `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` at the structure
sheaf. -/
theorem biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv_leg
    (hleg : S.ModuleSumFormulaLegEq O) (φ : n ⟶ m) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    letI : HasFiniteBiproducts
        ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    biproduct.ι (fun _ : n ⟶ m => S.componentModulesRestriction O m) φ ≫
        (S.componentModuleLowerShriekUnitTensorRestrictionSum O n m).inv =
      (S.restrictionTensorWhiskeredUnitIso O m).inv ≫
        (S.restrictionTensorWhiskered O m).map
            ((pullbackModulesObjUnitIso (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
              (S.moduleSumFormulaLeg O φ).app
                (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))) ≫
          (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom :=
  Eq.trans (S.biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv O n m φ)
    (congrArg
      (fun g => (S.restrictionTensorWhiskeredUnitIso O m).inv ≫
        (S.restrictionTensorWhiskered O m).map g ≫
          (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom)
      (S.ι_componentModuleLowerShriekUnitRestrictionSum_inv O n m hleg φ))

/-- **The `φ`th summand inclusion of the target identification of Stacks 0D9E (2).** The `φ`th
biproduct inclusion of `CategoryTheory.SimplicialSiteSituation.moduleProjectionTargetIso`, followed
by the inverse of that identification, is the derived functor of the `φ`th summand inclusion of the
sheaf-level identification
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorRestrictionSum`, read
through the compositor of the derived functors and the identification of `g_{n!}O_n ⊗^L_O -` with
the derived functor of `g_{n!}O_n ⊗_O -`.

This is `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv` instantiated at the target chain.
The target identification is derived from a composite of functors which is *not* a left adjoint
followed by a restriction — it is tensoring by the flat sheaf `g_{n!}O_n` followed by the
restriction — so the summand inclusions here are not canonical legs of an adjunction and the leg
form `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_leg` is not what is wanted. -/
theorem biproduct_ι_moduleProjectionTargetIso_inv
    (K : DerivedCategory (S.totalRingedTopos O).Modules) (φ : n ⟶ m) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    letI : HasFiniteBiproducts
        ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    biproduct.ι (fun _ : n ⟶ m => (S.derivedComponentModuleRestriction O m).obj K) φ ≫
        (S.moduleProjectionTargetIso O n m K).inv =
      (derivedNatTrans (S.componentModulesRestriction O m)
          (S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O m)
          (biproduct.ι (fun _ : n ⟶ m => S.componentModulesRestriction O m) φ ≫
            (S.componentModuleLowerShriekUnitTensorRestrictionSum O n m).inv)).app K ≫
        (derivedCompIso (S.componentModuleLowerShriekUnitTensor O n)
            (S.componentModulesRestriction O m)
            (S.componentModuleLowerShriekUnitTensor O n ⋙
              S.componentModulesRestriction O m) (Iso.refl _)).hom.app K ≫
        (S.derivedComponentModuleRestriction O m).map
          ((S.componentModuleLowerShriekUnitTensorDerivedIso O n).app K).inv := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  let : HasFiniteBiproducts
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ (S.derivedComponentModuleRestriction O m).map
      ((S.componentModuleLowerShriekUnitTensorDerivedIso O n).app K).inv)
    (biproduct_ι_derivedCompBiproductIso_inv
      ((S.totalRingedTopos O).Modules) ((S.totalRingedTopos O).Modules)
      ((S.componentRingedTopos O m).Modules)
      (S.componentModuleLowerShriekUnitTensor O n) (S.componentModulesRestriction O m)
      (fun _ : n ⟶ m => S.componentModulesRestriction O m)
      (S.componentModuleLowerShriekUnitTensorRestrictionSum O n m) K φ)) ?_
  exact Category.assoc _ _ _

/-- **The `φ`th summand inclusion of the target identification of Stacks 0D9E (2), with the
sheaf-level inclusion expanded.** This is
`CategoryTheory.SimplicialSiteSituation.biproduct_ι_moduleProjectionTargetIso_inv` with the natural
transformation it derives replaced, granted the leg equation of Stacks 0D72 (6), by the explicit
chain of `biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv_leg`: the component's
left unitor, the canonical leg of Stacks 0D72 (6) at the structure sheaf tensored into the
restriction, and Stacks 03EL. -/
theorem biproduct_ι_moduleProjectionTargetIso_inv_leg (hleg : S.ModuleSumFormulaLegEq O)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) (φ : n ⟶ m) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    letI : HasFiniteBiproducts
        ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    biproduct.ι (fun _ : n ⟶ m => (S.derivedComponentModuleRestriction O m).obj K) φ ≫
        (S.moduleProjectionTargetIso O n m K).inv =
      (derivedNatTrans (S.componentModulesRestriction O m)
          (S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O m)
          ((S.restrictionTensorWhiskeredUnitIso O m).inv ≫
            (S.restrictionTensorWhiskered O m).map
                ((pullbackModulesObjUnitIso
                      (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
                  (S.moduleSumFormulaLeg O φ).app
                    (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))) ≫
              (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom)).app K ≫
        (derivedCompIso (S.componentModuleLowerShriekUnitTensor O n)
            (S.componentModulesRestriction O m)
            (S.componentModuleLowerShriekUnitTensor O n ⋙
              S.componentModulesRestriction O m) (Iso.refl _)).hom.app K ≫
        (S.derivedComponentModuleRestriction O m).map
          ((S.componentModuleLowerShriekUnitTensorDerivedIso O n).app K).inv := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  let : HasFiniteBiproducts
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  refine Eq.trans (S.biproduct_ι_moduleProjectionTargetIso_inv O n m K φ) ?_
  exact congrArg
    (fun α => (derivedNatTrans (S.componentModulesRestriction O m)
        (S.componentModuleLowerShriekUnitTensor O n ⋙
          S.componentModulesRestriction O m) α).app K ≫
      (derivedCompIso (S.componentModuleLowerShriekUnitTensor O n)
          (S.componentModulesRestriction O m)
          (S.componentModuleLowerShriekUnitTensor O n ⋙
            S.componentModulesRestriction O m) (Iso.refl _)).hom.app K ≫
      (S.derivedComponentModuleRestriction O m).map
        ((S.componentModuleLowerShriekUnitTensorDerivedIso O n).app K).inv)
    (S.biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv_leg O n m hleg φ)

end CategoryTheory.SimplicialSiteSituation

end
