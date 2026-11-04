module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafSliceComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections

/-!
# The structure sheaf has the flat base change property

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `φ : x ⟶ y` an arrow of `𝒳`
lying over a morphism of schemes `a : U ⟶ V`. The comparison map
`c_φ : a_{small}^*(𝒪_𝒳|_{V_ét}) ⟶ 𝒪_𝒳|_{U_ét}` of **Stacks 0761** at the structure sheaf is an
isomorphism, for every `a`: the inverse image of the structure sheaf is the structure sheaf. In
particular the structure sheaf has the flat base change property of **Stacks 0762**, in the
source's reading on sheaves (`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`).

## The argument

The restrictions of `𝒪_𝒳` to the small étale sites are identified with their structure sheaves,
the unit modules, by the identification of Stacks 06W9
(`AlgebraicGeometry.Stack.unitRestrictSheafToSmallEtaleIso`). Under these identifications the
adjunct of `c_φ` across the adjunction of `a_{small}^*` with the pushforward along the morphism of
ringed sites `ε_a` of Stacks 070R (2) is the structure map of `ε_a`: the adjunct is the
comparison of Stacks 06W2 on sections
(`AlgebraicGeometry.Stack.homEquiv_restrictSheafPullbackComparison_val_app`), and the structure
map of `ε_a` is that comparison read on the structure sheaves
(`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`). Maps out
of a unit module are global sections, and pushing forward along `ε_a` is a bijection on global
sections because the base change functor of the small étale sites carries the final object to a
final object; the Yoneda lemma concludes, as in Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`.

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_unit`: `c_φ` is an isomorphism
  at the structure sheaf, for every arrow `φ`.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_unit`: the structure sheaf has the flat
  base change property.

## References

* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06W9](https://stacks.math.columbia.edu/tag/06W9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The unit module over a presheaf of rings `P`, and the unit module over an isomorphic presheaf
of rings `Q` with its scalars restricted along the isomorphism, are isomorphic. -/
noncomputable def presheafUnitIsoRestrictScalarsUnit {C : Type*} [Category C]
    {P Q : Cᵒᵖ ⥤ RingCat.{u}} (α : P ≅ Q) :
    PresheafOfModules.unit P ≅
      (PresheafOfModules.restrictScalars α.hom).obj (PresheafOfModules.unit Q) where
  hom := {
    app W := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (α.hom.app W)) (fun r ↦ by
      ext m
      exact ((α.hom.app W).hom.map_mul _ _).symm)
    naturality f := by
      ext
      exact ConcreteCategory.congr_hom (α.hom.naturality f) _ }
  inv := {
    app W := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (α.inv.app W)) (fun r ↦ by
      ext m
      exact (congrArg (· * _) (ConcreteCategory.congr_hom (α.hom_inv_id_app W) r)).symm.trans
        (map_mul (α.inv.app W).hom _ _).symm)
    naturality f := by
      ext
      exact ConcreteCategory.congr_hom (α.inv.naturality f) _ }
  hom_inv_id := by
    refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    exact ConcreteCategory.congr_hom (α.hom_inv_id_app W) r
  inv_hom_id := by
    refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    exact ConcreteCategory.congr_hom (α.inv_hom_id_app W) r

/-- On sections over `W`, the isomorphism `presheafUnitIsoRestrictScalarsUnit α` sends `r` to
`α.hom.app W r`. -/
@[simp]
theorem presheafUnitIsoRestrictScalarsUnit_hom_app_apply {C : Type*}
    [Category C] {P Q : Cᵒᵖ ⥤ RingCat.{u}} (α : P ≅ Q) (W : Cᵒᵖ) (r : P.obj W) :
    (presheafUnitIsoRestrictScalarsUnit α).hom.app W r = α.hom.app W r := rfl

/-- **The restriction of the structure sheaf of `𝒳` to a small étale site is the unit module.**
On sections over an étale `U`-scheme it is the identification of structure sheaves of
Stacks 06W9, `AlgebraicGeometry.Stack.localStructurePresheafIso`. -/
noncomputable def unitRestrictSheafToSmallEtaleIso (x : 𝒳) :
    SheafOfModules.unit
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)) ≅
      (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj
        (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B))) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (presheafUnitIsoRestrictScalarsUnit
      (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)))

/-- The small étale base change functor below an arrow of `𝒳` is final: it carries the final
object to a final object. -/
theorem final_smallEtaleBaseChange {x y : 𝒳} (φ : x ⟶ y) :
    (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).Final := by
  let F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
  let c := SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y)
  have : (Functor.fromPUnit.{0} c).Final :=
    Functor.final_fromPUnit_of_isTerminal (SmallEtale.finalIsTerminal E _ _)
  have : (Functor.fromPUnit.{0} (F.obj c)).Final :=
    Functor.final_fromPUnit_of_isTerminal
      (smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p φ))
  have : (Functor.fromPUnit.{0} c ⋙ F).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (F.obj c))
      (Discrete.natIso fun _ => Iso.refl _)
  exact Functor.final_of_final_comp (Functor.fromPUnit.{0} c) F

section Arrow

variable {x y : 𝒳} (φ : x ⟶ y)

/-- The adjunct of the comparison map at the structure sheaf, read through the identifications
with the unit modules, is the structure map of the morphism of ringed sites `ε_a`. -/
theorem unitRestrictSheafToSmallEtaleIso_hom_comp_homEquiv :
    (unitRestrictSheafToSmallEtaleIso B E h S hS p hp y).hom ≫
        (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).homEquiv _ _
          (restrictSheafPullbackComparison B E h S hS p hp φ
            (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)))) =
      SheafOfModules.unitToPushforwardObjUnit (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ)) ≫
        (SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ))).map
          (unitRestrictSheafToSmallEtaleIso B E h S hS p hp x).hom := by
  ext W
  have hε := ConcreteCategory.congr_hom (congrArg (fun t => t.app W)
    (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) φ)) 1
  have h1 := homEquiv_restrictSheafPullbackComparison_val_app B E h S hS p hp φ
    (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) W
  have h2 : ∀ t, (restrictionPushforwardComparison B E h S hS p hp φ
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))).val.presheaf).app W t =
      (restrictionPushforwardComparison B E h S hS p hp φ
        (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj).app W t := fun t => by
    rw [restrictionPushforwardComparison_app_eq_sliceComparisonLift,
      restrictionPushforwardComparison_app_eq_sliceComparisonLift]
    rfl
  let Ly := localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
    (etaleTopology_le_topology B)
  let Lx := localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)
  let ρ := restrictionPushforwardComparison B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  let W' := op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W.unop)
  exact ((h1 _).trans (h2 _)).trans
    ((ConcreteCategory.congr_hom (Lx.inv_hom_id_app W') _).symm.trans (congrArg (Lx.hom.app W') hε))

/-- **The comparison map of Stacks 0761 is an isomorphism at the structure sheaf**, along every
arrow of `𝒳`: the inverse image of the structure sheaf is the structure sheaf. -/
theorem isIso_restrictSheafPullbackComparison_unit :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)))) := by
  have := final_smallEtaleBaseChange B E h S hS p φ
  let ε := SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)
  let adj := sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ
  let eA := unitRestrictSheafToSmallEtaleIso B E h S hS p hp y
  let eB := unitRestrictSheafToSmallEtaleIso B E h S hS p hp x
  let c := restrictSheafPullbackComparison B E h S hS p hp φ
    (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  refine ((adj.homEquiv _ M).bijective.of_comp_iff' (fun f => c ≫ f)).mp ?_
  have hfun : (adj.homEquiv _ M) ∘ (fun f => c ≫ f) =
      fun f => adj.homEquiv _ _ c ≫ (SheafOfModules.pushforward.{u} ε).map f :=
    funext fun f => adj.homEquiv_naturality_right c f
  rw [hfun]
  refine ((((SheafOfModules.unitHomEquiv _).bijective).comp
    ((isIso_iff_coyoneda_map_bijective eA.hom).mp inferInstance _)).of_comp_iff'
    (fun f => adj.homEquiv _ _ c ≫ (SheafOfModules.pushforward.{u} ε).map f)).mp ?_
  have hsq : (SheafOfModules.unitHomEquiv _ ∘ fun g => eA.hom ≫ g) ∘
      (fun f => adj.homEquiv _ _ c ≫ (SheafOfModules.pushforward.{u} ε).map f) =
      SheafOfModules.pushforwardSections ε ∘ SheafOfModules.unitHomEquiv _ ∘
        (fun f : _ ⟶ M => eB.hom ≫ f) := by
    funext f
    simp only [Function.comp_apply]
    rw [SheafOfModules.pushforwardSections_unitHomEquiv, ← Category.assoc,
      unitRestrictSheafToSmallEtaleIso_hom_comp_homEquiv, Category.assoc, Functor.map_comp]
  rw [hsq]
  refine (SheafOfModules.bijective_pushforwardSections ε M).comp
    (((SheafOfModules.unitHomEquiv _).bijective).comp
      ((isIso_iff_coyoneda_map_bijective eB.hom).mp inferInstance _))

end Arrow

/-- **The structure sheaf has the flat base change property** of Stacks 0762, in the source's
reading on sheaves: its comparison map is an isomorphism along every arrow of `𝒳`, flat or not. -/
theorem hasFlatBaseChangePropertySheaf_unit :
    HasFlatBaseChangePropertySheafUnivLE.{u, v, w, u} B E h S hS p hp
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))) := fun φ _ =>
  isIso_restrictSheafPullbackComparison_unit B E h S hS p hp φ

end AlgebraicGeometry.Stack

end
