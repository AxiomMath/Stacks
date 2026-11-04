module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormula
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjection

/-!
# The restriction to a degree of the target of the projection map of Stacks 0D9E (2)

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site and `g_n` the inclusion of the degree-`n` simplicial component. The canonical map of
Stacks 0D9E (2) is `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K`, and its proof restricts that map to a degree
`m` and identifies both sides with direct sums over the simplex maps `φ : [n] ⟶ [m]`. This file
**constructs the identification of the target**,

`g_m^*(g_{n!}O_n ⊗^L_O K) ≅ ⨁_{φ : [n] ⟶ [m]} K_m`.

The construction runs on *sheaves* and is then derived, exactly as the construction of the map
itself does in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleProjection.lean`: the sheaf
`g_{n!}O_n` is flat (`…isFlat_componentModuleLowerShriek_unit`, with no flatness hypothesis on the
structure-sheaf transitions), so `g_{n!}O_n ⊗^L_O -` is the derived functor of the exact
endofunctor `g_{n!}O_n ⊗_O -` of `Mod(O)` by
`…componentModuleLowerShriekUnitTensorDerivedIso`. On sheaves the identification is the chain

`g_m^*(g_{n!}O_n ⊗_O M) ≅ g_m^*(g_{n!}O_n) ⊗_{O_m} g_m^*M ≅ (⨁_φ O_m) ⊗_{O_m} g_m^*M ≅ ⨁_φ g_m^*M`

— Stacks 03EL at the component inclusion, then the componentwise direct-sum formula of
Stacks 0D72 (6) at the structure sheaf, then distributivity of the tensor product over a finite
direct sum and the left unitor.

**No description of the summand legs of the direct-sum formula is used.** Only its existence is,
as in `…isFlat_componentModuleLowerShriek_unit`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitRestrictionSum`: the
  restriction to degree `m` of `g_{n!}O_n` as a direct sum of copies of `O_m`.
* `CategoryTheory.SimplicialSiteSituation.componentRestrictionLowerShriekUnitTensorIso`:
  Stacks 03EL at the degree-`m` inclusion with the first tensor variable fixed at `g_{n!}O_n`.
* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorRestrictionSum`:
  **`(g_{n!}O_n ⊗_O -) ⋙ g_m^* ≅ ⨁_φ g_m^*`**, on sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.moduleProjectionTargetIso`: **the identification
  `g_m^*(g_{n!}O_n ⊗^L_O K) ≅ ⨁_φ K_m`**, on unbounded derived categories.

## Implementation notes

*Why the middle of the chain is run at the level of functors and not of objects.* The passage to
derived categories is `CategoryTheory.derivedCompBiproductIso`, which consumes a presentation
`F ⋙ G ≅ ⨁ L` of a *composite of functors* as a finite direct sum of functors; so the sheaf-level
identification has to be a natural isomorphism, and each step of the chain has to come with its
naturality. Two of the three steps are therefore taken functor-first rather than object-first.

The distributivity step is the one where this matters. Pointwise it is
`Stacks.SheafOfModules.Strict.coproductUnitTensorIso`, whose naturality in the tensor factor is
not recorded; instead the whole functor `A ↦ g_m^* ⋙ (A ⊗_{O_m} -)` is shown to commute with
colimits — which is `Stacks.SheafOfModules.Strict.preservesColimit_sheafTensorFlip` after
`CategoryTheory.Limits.preservesColimit_of_evaluation`, because `A ↦ g_m^* ⋙ (A ⊗_{O_m} -)`
composed with evaluation at `M` *is* tensoring in the right variable at `g_m^*M` — and the
direct sum is extracted by `CategoryTheory.Limits.preservesColimitIso`. The summandwise step is
then the component's left unitor as an isomorphism of functors,
`…componentModuleUnitTensorLeftUnitor`.

Only the first step is pointwise: Stacks 03EL is stated between uncurried bifunctors on
`Mod(O) × Mod(O)`, and its naturality in the second variable alone is
`…componentRestrictionTensorIso_inv_naturality_right`, which is exactly what
`CategoryTheory.NatIso.ofComponents` asks for here.

*The two spellings of a component's modules cross without trouble here.* The direct-sum formula
is stated for `SheafOfModules` over `CategoryTheory.SimplicialSiteSituation.componentRingSheaf`
and everything else here for `AlgebraicGeometry.RingedTopos.Modules` of
`…componentRingedTopos`; `…componentModulesRestriction` is the former by definition, so the
crossing is a delta step and the elaborator takes it. The same is true of the summand
identification `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, which is stated at
`AlgebraicGeometry.RingedToposHom.toModulesHom` while the summand of the formula is
`…transitionPullbackModules'`, i.e. `AlgebraicGeometry.RingedToposHom.pullbackModules`: the two
readings of a morphism of ringed topoi agree only propositionally, but here the crossing is
*inside an isomorphism between two objects*, not between two adjunctions, and the kernel takes it
in under a second. It is the same crossing that
`…isFlat_componentModuleLowerShriek_unit` already makes.

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

/-- **The restriction to degree `m` of `g_{n!}O_n` is a direct sum of copies of `O_m`**, one for
each simplex map `φ : [n] ⟶ [m]`.

This is the componentwise direct-sum formula of Stacks 0D72 (6),
`CategoryTheory.SimplicialSiteSituation.moduleSumFormula`, evaluated at the structure sheaf of
the component: the formula is an isomorphism of functors into a coproduct in a functor category,
so the evaluation goes through `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation`, and
each summand `f_φ^*O_n` is `O_m` by
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`. No description of the formula's
summand legs is used. -/
def componentModuleLowerShriekUnitRestrictionSum :
    (S.componentModulesRestriction O m).obj (S.componentModuleLowerShriekUnit O n) ≅
      ∐ fun _ : n ⟶ m =>
        SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m) :=
  (S.moduleSumFormula O n m).app _ ≪≫
    colimitObjIsoColimitCompEvaluation _ _ ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun φ =>
      (pullbackModulesObjUnitIso (S.transitionRingedToposHom O φ.as).toModulesHom).symm)

/-- **Stacks 03EL at the degree-`m` component inclusion, with the first tensor variable fixed at
`g_{n!}O_n`**: the natural isomorphism `g_m^*(-) ⊗_{O_m} g_m^*(g_{n!}O_n) ≅ g_m^*(g_{n!}O_n ⊗_O -)`
of functors `Mod(O) ⥤ Mod(O_m)`.

The comparison `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso` is stated
between uncurried bifunctors, so its naturality in the second variable alone is the separate
statement `…componentRestrictionTensorIso_inv_naturality_right`, which is what the components
assembled here need. -/
def componentRestrictionLowerShriekUnitTensorIso :
    S.componentModulesRestriction O m ⋙
        (sheafTensor (S.componentRingedTopos O m).O).obj
          ((S.componentModulesRestriction O m).obj (S.componentModuleLowerShriekUnit O n)) ≅
      S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O m :=
  NatIso.ofComponents
    (fun M => ((S.componentRestrictionTensorIso O m).app
      (S.componentModuleLowerShriekUnit O n, M)).symm)
    (fun {_ _} f => S.componentRestrictionTensorIso_inv_naturality_right O m
      (S.componentModuleLowerShriekUnit O n) f)

/-- The functor `A ↦ g_m^* ⋙ (A ⊗_{O_m} -)`, sending a sheaf of `O_m`-modules to the functor
`Mod(O) ⥤ Mod(O_m)` that restricts to degree `m` and tensors with it. It is the functor the
direct sum of the restriction is extracted from. -/
abbrev restrictionTensorWhiskered :
    (S.componentRingedTopos O m).Modules ⥤
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
  sheafTensor (S.componentRingedTopos O m).O ⋙
    (Functor.whiskeringLeft _ _ _).obj (S.componentModulesRestriction O m)

/-- Tensoring in the left variable commutes with colimits, and precomposition with the
restriction is computed pointwise, so `A ↦ g_m^* ⋙ (A ⊗_{O_m} -)` commutes with colimits. -/
instance preservesColimit_restrictionTensorWhiskered {J : Type*} [Category J]
    (D : J ⥤ (S.componentRingedTopos O m).Modules) :
    PreservesColimit D (S.restrictionTensorWhiskered O m) :=
  preservesColimit_of_evaluation _ _ fun M =>
    Stacks.SheafOfModules.Strict.preservesColimit_sheafTensorFlip
      (S.componentRingedTopos O m).O D ((S.componentModulesRestriction O m).obj M)

/-- `g_m^* ⋙ (O_m ⊗_{O_m} -) ≅ g_m^*`: the left unitor of the component,
`CategoryTheory.SimplicialSiteSituation.componentModuleUnitTensorLeftUnitor`, whiskered with the
restriction. This is the summandwise step of the direct-sum identification. -/
def restrictionTensorWhiskeredUnitIso :
    (S.restrictionTensorWhiskered O m).obj
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m)) ≅
      S.componentModulesRestriction O m :=
  Functor.isoWhiskerLeft (S.componentModulesRestriction O m)
    (S.componentModuleUnitTensorLeftUnitor O m)

/-- **The restriction to degree `m` of `g_{n!}O_n ⊗_O -` is the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the restriction to degree `m`**, as an isomorphism of functors
`Mod(O) ⥤ Mod(O_m)`.

This is the sheaf-level form of the identification of the target of the canonical map of
Stacks 0D9E (2); `CategoryTheory.SimplicialSiteSituation.moduleProjectionTargetIso` is its
derived form. -/
def componentModuleLowerShriekUnitTensorRestrictionSum :
    letI : HasFiniteBiproducts
        ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O m ≅
      ⨁ fun _ : n ⟶ m => S.componentModulesRestriction O m := by
  letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  letI : HasColimitsOfShape (Discrete (n ⟶ m))
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
    functorCategoryHasColimitsOfShape
  letI : HasFiniteBiproducts
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  refine (S.componentRestrictionLowerShriekUnitTensorIso O n m).symm ≪≫
    (S.restrictionTensorWhiskered O m).mapIso
      (S.componentModuleLowerShriekUnitRestrictionSum O n m) ≪≫
    preservesColimitIso (S.restrictionTensorWhiskered O m) _ ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _) ≪≫
    HasColimit.isoOfNatIso
      (G := Discrete.functor fun _ : n ⟶ m => S.componentModulesRestriction O m)
      (Discrete.natIso fun _ => S.restrictionTensorWhiskeredUnitIso O m) ≪≫
    (biproduct.isoCoproduct fun _ : n ⟶ m => S.componentModulesRestriction O m).symm

/-- **The identification of the restriction to degree `m` of the target `g_{n!}O_n ⊗^L_O K` of
the canonical map of Stacks 0D9E (2) with `⨁_φ K_m`**, over the simplex maps `φ : [n] ⟶ [m]`.

No flatness hypothesis on the structure-sheaf transitions is needed, and neither is the
existence of the derived transition pullbacks: both sides are derived functors of exact functors
of sheaves of modules — the target because `g_{n!}O_n` is flat unconditionally — so the
identification is the derived functor of the sheaf-level
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorRestrictionSum`, read
through `CategoryTheory.derivedCompBiproductIso`. -/
def moduleProjectionTargetIso (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.derivedComponentModuleRestriction O m).obj
        ((((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
              ((S.componentModuleLowerShriek
                  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) n).obj
                (SheafOfModules.unit (S.componentRingSheaf
                  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) n))))).obj K)) ≅
      ⨁ fun _ : n ⟶ m => (S.derivedComponentModuleRestriction O m).obj K := by
  letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  letI : HasFiniteBiproducts
      ((S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O m).Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  refine (S.derivedComponentModuleRestriction O m).mapIso
      ((S.componentModuleLowerShriekUnitTensorDerivedIso O n).app K) ≪≫ ?_
  exact derivedCompBiproductIso _ _ _ (S.componentModuleLowerShriekUnitTensor O n)
    (S.componentModulesRestriction O m) (fun _ : n ⟶ m => S.componentModulesRestriction O m)
    (S.componentModuleLowerShriekUnitTensorRestrictionSum O n m) K

end CategoryTheory.SimplicialSiteSituation

end
