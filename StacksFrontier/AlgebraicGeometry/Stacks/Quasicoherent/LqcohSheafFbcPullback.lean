module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleInverseImagePushforwardComparison

/-!
# Inverse image of a module in `LQCoh^fbc` (Stacks 0771, part (3))

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0771** part (3) says that
the inverse image `f^*` carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`: the modules which are
locally quasi-coherent (**Stacks 06WJ**) and have the flat base change property
(**Stacks 0762**). The source cites **Stacks 0764** part (1) for the flat base change property
and **Stacks 06WL** for local quasi-coherence. The flat base change property is read on sheaves,
as `AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`: the comparison maps are local
isomorphisms of the small étale sites.

## Main results

* `AlgebraicGeometry.Stack.isLocallyBijective_pullbackComparison_modulePresheafPullback_iff`:
  the comparison map of `f^{-1}G` at an arrow `ψ` is a local isomorphism if and only if that of
  `G` at `f ψ` is.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_modulePresheafPullback`:
  **Stacks 0764** part (1): the inverse image of an étale sheaf of modules with the flat base
  change property has it, along every 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback`
  and `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback`:
  the inverse image preserves membership in `LQCoh^fbc`, for categories fibred in groupoids.
* `AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules_stackModuleInverseImage`: **Stacks 0771**
  part (3) on `Mod(𝒳_ét, 𝒪_𝒳)`, with the inverse image of the étale sites.
* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesPullback`: **Stacks 0771**
  part (3) on `Mod(𝒪_𝒳)`, with the inverse image of the fppf sites.
* `AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModulesPullback` and
  `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModulesPullback`: the induced functors
  `f^* : LQCoh^fbc(𝒪_𝒴) ⥤ LQCoh^fbc(𝒪_𝒳)`.

## Implementation notes

For an arrow `ψ : z ⟶ z'` of `𝒳`, the source observes that the comparison map of `f^*F` at `ψ` is
a comparison map of `F`, the one at `f ψ`. Three identifications make this precise.

* The two maps of structure sheaves `a_{small}^♯` below `ψ` and below `f ψ` are equal
  (`AlgebraicGeometry.Stack.smallEtaleStructureComparison_comp`): both are the canonical map of
  the morphism of schemes below the arrow,
  `AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`.
* The direct-image comparisons of **Stacks 06W2** match under the identification of
  **Stacks 075D** part (3) of the restricted modules
  (`AlgebraicGeometry.Stack.moduleInverseImageIso_hom_comp_pushforwardComparison`), by the
  corresponding statement for sheaves of sets.
* The comparison maps of **Stacks 06WC** are the mates of those direct-image comparisons, so they
  match too, and a local isomorphism stays one after composing with isomorphisms
  (`PresheafOfModules.isLocallyBijective_homEquiv_symm_iff_of_comm`).

The étale sheaf condition, part of local quasi-coherence, is used for the identification of
**Stacks 075D** part (3): the source's modules are sheaves on `𝒳_ét`.

The flat base change property of the inverse image (**Stacks 0764** part (1)) carries no tag here:
it is a prerequisite of **Stacks 0771** part (3).

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m

namespace PresheafOfModules

variable {C : Type*} [Category C] {D : Type*} [Category D] {b : C ⥤ D}
  {R : Cᵒᵖ ⥤ RingCat.{u}} {R' : Dᵒᵖ ⥤ RingCat.{u}}

/-- A square of presheaves of modules into direct images commutes if and only if it does on
underlying presheaves. -/
private theorem toPresheaf_square_iff {σ : R ⟶ b.op ⋙ R'}
    {M₁ M₂ : PresheafOfModules.{m} R} {N₁ N₂ : PresheafOfModules.{m} R'}
    (e : M₁ ⟶ M₂) (e' : N₁ ⟶ N₂)
    (d₁ : M₁ ⟶ (pushforward.{m} σ).obj N₁) (d₂ : M₂ ⟶ (pushforward.{m} σ).obj N₂) :
    (toPresheaf R).map e ≫ (toPresheaf R).map d₂ =
      (toPresheaf R).map d₁ ≫ Functor.whiskerLeft b.op ((toPresheaf R').map e') ↔
    e ≫ d₂ = d₁ ≫ (pushforward σ).map e' := by
  rw [← (toPresheaf R).map_injective.eq_iff, Functor.map_comp, Functor.map_comp]
  rfl

/-- Let `d₁ : M₁ ⟶ b_* N₁` and `d₂ : M₂ ⟶ b_* N₂` be maps of presheaves of modules into direct
images along equal maps of rings `σ = σ'`, which correspond under isomorphisms `M₁ ≅ M₂` and
`N₁ ≅ N₂` on underlying presheaves. If the mate `b^* M₂ ⟶ N₂` of `d₂` is locally injective and
locally surjective, so is the mate `b^* M₁ ⟶ N₁` of `d₁`. -/
theorem isLocallyBijective_homEquiv_symm_of_comm (J : GrothendieckTopology D)
    {σ σ' : R ⟶ b.op ⋙ R'} (hσ : σ = σ')
    [(pushforward.{m} (F := b) σ).IsRightAdjoint] [(pushforward.{m} (F := b) σ').IsRightAdjoint]
    {M₁ M₂ : PresheafOfModules.{m} R} {N₁ N₂ : PresheafOfModules.{m} R'}
    (e : M₁ ≅ M₂) (e' : N₁ ≅ N₂)
    (d₁ : M₁ ⟶ (pushforward σ).obj N₁) (d₂ : M₂ ⟶ (pushforward σ').obj N₂)
    (hsq : (toPresheaf R).map e.hom ≫ (toPresheaf R).map d₂ =
      (toPresheaf R).map d₁ ≫ Functor.whiskerLeft b.op ((toPresheaf R').map e'.hom))
    (h₂ : Presheaf.IsLocallyInjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ').homEquiv _ _).symm d₂)) ∧
      Presheaf.IsLocallySurjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ').homEquiv _ _).symm d₂))) :
    Presheaf.IsLocallyInjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ).homEquiv _ _).symm d₁)) ∧
      Presheaf.IsLocallySurjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ).homEquiv _ _).symm d₁)) := by
  subst hσ
  let adj := pullbackPushforwardAdjunction.{m} (F := b) σ
  have hsq' := (toPresheaf_square_iff e.hom e'.hom d₁ d₂).1 hsq
  have hmate : (pullback σ).map e.hom ≫ (adj.homEquiv _ _).symm d₂ =
      (adj.homEquiv _ _).symm d₁ ≫ e'.hom := by
    apply adj.homEquiv _ _ |>.injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, hsq']
  have hc₁ : (adj.homEquiv _ _).symm d₁ =
      (pullback σ).map e.hom ≫ (adj.homEquiv _ _).symm d₂ ≫ e'.inv := by
    rw [← Category.assoc, hmate, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  show Presheaf.IsLocallyInjective J ((toPresheaf R').map ((adj.homEquiv _ _).symm d₁)) ∧
    Presheaf.IsLocallySurjective J ((toPresheaf R').map ((adj.homEquiv _ _).symm d₁))
  rw [hc₁]
  obtain ⟨h₂i, h₂s⟩ := h₂
  simp only [Functor.map_comp]
  exact ⟨inferInstance, inferInstance⟩

/-- In the situation of `PresheafOfModules.isLocallyBijective_homEquiv_symm_of_comm`, the mate of
`d₁` is a local isomorphism if and only if the mate of `d₂` is. -/
theorem isLocallyBijective_homEquiv_symm_iff_of_comm (J : GrothendieckTopology D)
    {σ σ' : R ⟶ b.op ⋙ R'} (hσ : σ = σ')
    [(pushforward.{m} (F := b) σ).IsRightAdjoint] [(pushforward.{m} (F := b) σ').IsRightAdjoint]
    {M₁ M₂ : PresheafOfModules.{m} R} {N₁ N₂ : PresheafOfModules.{m} R'}
    (e : M₁ ≅ M₂) (e' : N₁ ≅ N₂)
    (d₁ : M₁ ⟶ (pushforward σ).obj N₁) (d₂ : M₂ ⟶ (pushforward σ').obj N₂)
    (hsq : (toPresheaf R).map e.hom ≫ (toPresheaf R).map d₂ =
      (toPresheaf R).map d₁ ≫ Functor.whiskerLeft b.op ((toPresheaf R').map e'.hom)) :
    (Presheaf.IsLocallyInjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ).homEquiv _ _).symm d₁)) ∧
      Presheaf.IsLocallySurjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ).homEquiv _ _).symm d₁))) ↔
    (Presheaf.IsLocallyInjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ').homEquiv _ _).symm d₂)) ∧
      Presheaf.IsLocallySurjective J
        ((toPresheaf R').map (((pullbackPushforwardAdjunction.{m} σ').homEquiv _ _).symm d₂))) := by
  refine ⟨fun h₁ => isLocallyBijective_homEquiv_symm_of_comm J hσ.symm e.symm e'.symm d₂ d₁ ?_ h₁,
    isLocallyBijective_homEquiv_symm_of_comm J hσ e e' d₁ d₂ hsq⟩
  subst hσ
  have hsq' := (toPresheaf_square_iff e.hom e'.hom d₁ d₂).1 hsq
  have k : e.inv ≫ d₁ = d₂ ≫ (pushforward σ).map e'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hsq', Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact (toPresheaf_square_iff e.inv e'.inv d₂ d₁).2 k

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The map of structure sheaves `a_{small}^♯` below an arrow `ψ` of `𝒳`, for the composite
structure functor `f ⋙ q`, is the one below `f ψ` for `q`: both are the canonical map of the
morphism of schemes below the arrow. -/
theorem smallEtaleStructureComparison_comp {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'}
    [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids) {z z' : 𝒳} (ψ : z ⟶ z')
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    smallEtaleStructureComparison B E h S hS (f ⋙ q) hp ψ τ hτ =
      smallEtaleStructureComparison B E h S hS q hq (f.map ψ) τ hτ := by
  rw [smallEtaleStructureComparison_eq_smallEtaleStructureMapRing,
    smallEtaleStructureComparison_eq_smallEtaleStructureMapRing]
  rfl

/-- **The direct-image comparisons of Stacks 06W2 for modules match under Stacks 075D (3).** For
an étale sheaf of modules `G` on `𝒴` and an arrow `ψ : z ⟶ z'` of `𝒳`, the comparison of
`G` at `f ψ`, preceded by the identification at `z'` of the restricted modules, is the
comparison of `f^{-1}G` at `ψ` followed by the identification at `z`, on underlying presheaves.

This is the module form of
`AlgebraicGeometry.Stack.inverseImageIso_hom_comp_restrictionPushforwardComparison`, read on
sections. -/
theorem moduleInverseImageIso_hom_comp_pushforwardComparison
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'}
    [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hf : (f ⋙ q).IsFibredOneMorphism q f)
    (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hG : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)
    {z z' : 𝒳} (ψ : z ⟶ z') :
    (PresheafOfModules.toPresheaf _).map
        (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf z').hom ≫
      (PresheafOfModules.toPresheaf _).map
        (restrictModulePushforwardComparison B E h S hS q hq (f.map ψ) (etaleTopology B)
          (etaleTopology_le_topology B) G) =
    (PresheafOfModules.toPresheaf _).map
        (restrictModulePushforwardComparison B E h S hS (f ⋙ q) hp ψ (etaleTopology B)
          (etaleTopology_le_topology B)
          ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)) ≫
      Functor.whiskerLeft
        (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (f ⋙ q) ψ)).op
        ((PresheafOfModules.toPresheaf _).map
          (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
            B E h S hS q hq f hp G hG hf z).hom) := by
  let : (f ⋙ q).IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((etaleTopology B).over (B.obj hS))).1
  have hT := inverseImageIso_hom_comp_restrictionPushforwardComparison
    B E h S hS q hq f hp hf ψ (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG)
  have e2 : restrictionPushforwardComparison B E h S hS q hq (f.map ψ)
        (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG).obj =
      Functor.whiskerRight (restrictionPushforwardComparison B E h S hS q hq (f.map ψ)
        G.presheaf) (forget AddCommGrpCat) :=
    restrictionPushforwardComparison_comp B E h S hS q hq (f.map ψ) G.presheaf
      (forget AddCommGrpCat)
  have e3 : restrictionPushforwardComparison B E h S hS (f ⋙ q) hp ψ
        ((f.sheafPushforwardContinuous (Type m)
          (associatedTopology B S hS (f ⋙ q) (etaleTopology B))
          (associatedTopology B S hS q (etaleTopology B))).obj
          (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG)).obj =
      Functor.whiskerRight (restrictionPushforwardComparison B E h S hS (f ⋙ q) hp ψ
        (f.op ⋙ G.presheaf)) (forget AddCommGrpCat) :=
    restrictionPushforwardComparison_comp B E h S hS (f ⋙ q) hp ψ (f.op ⋙ G.presheaf)
      (forget AddCommGrpCat)
  rw [e2, e3] at hT
  refine NatTrans.ext (funext fun W => ?_)
  ext x
  exact congrArg (fun k => k.app W x) hT

/-- The comparison map of **Stacks 0761** for `f^{-1}G` at an arrow `ψ` of `𝒳` is a local
isomorphism of the small étale site if and only if the one for `G` at `f ψ` is, for an étale
sheaf of modules `G` on `𝒴`. This is the identification behind **Stacks 0764 (1)**, in the form
usable in both directions. -/
theorem isLocallyBijective_pullbackComparison_modulePresheafPullback_iff
    [UnivLE.{u, m}] {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'}
    [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids)
    (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hGsh : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)
    {z z' : 𝒳} (ψ : z ⟶ z') :
    (Presheaf.IsLocallyInjective
        (SmallEtale.topology E ((f ⋙ q).obj z).left.1 (contains_base B E h S hS (f ⋙ q) z))
        ((PresheafOfModules.toPresheaf _).map
          (restrictModulePullbackComparisonUnivLE B E h S hS (f ⋙ q) hp ψ (etaleTopology B)
            (etaleTopology_le_topology B)
            ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G))) ∧
      Presheaf.IsLocallySurjective
        (SmallEtale.topology E ((f ⋙ q).obj z).left.1 (contains_base B E h S hS (f ⋙ q) z))
        ((PresheafOfModules.toPresheaf _).map
          (restrictModulePullbackComparisonUnivLE B E h S hS (f ⋙ q) hp ψ (etaleTopology B)
            (etaleTopology_le_topology B)
            ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)))) ↔
    (Presheaf.IsLocallyInjective
        (SmallEtale.topology E (q.obj (f.obj z)).left.1 (contains_base B E h S hS q (f.obj z)))
        ((PresheafOfModules.toPresheaf _).map
          (restrictModulePullbackComparisonUnivLE B E h S hS q hq (f.map ψ) (etaleTopology B)
            (etaleTopology_le_topology B) G)) ∧
      Presheaf.IsLocallySurjective
        (SmallEtale.topology E (q.obj (f.obj z)).left.1 (contains_base B E h S hS q (f.obj z)))
        ((PresheafOfModules.toPresheaf _).map
          (restrictModulePullbackComparisonUnivLE B E h S hS q hq (f.map ψ) (etaleTopology B)
            (etaleTopology_le_topology B) G))) := by
  have hf : (f ⋙ q).IsFibredOneMorphism q f := hq.isFibredOneMorphism rfl
  have : (PresheafOfModules.pushforward.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (f ⋙ q) ψ))
      (smallEtaleStructureComparison B E h S hS q hq (f.map ψ) (etaleTopology B)
        (etaleTopology_le_topology B))).IsRightAdjoint :=
    isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE.{u, v', w', m}
      B E h S hS q hq (f.map ψ) (etaleTopology B) (etaleTopology_le_topology B)
  have := isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE.{u, v, w, m}
    B E h S hS (f ⋙ q) hp ψ (etaleTopology B) (etaleTopology_le_topology B)
  exact PresheafOfModules.isLocallyBijective_homEquiv_symm_iff_of_comm _
    (smallEtaleStructureComparison_comp B E h S hS q hq f hp ψ (etaleTopology B)
      (etaleTopology_le_topology B))
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hGsh hf z')
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hGsh hf z) _ _
    (moduleInverseImageIso_hom_comp_pushforwardComparison
      B E h S hS q hq f hp hf G hGsh ψ)

/-- **Stacks 0764 (1)**, with the flat base change property of **Stacks 0762** read on sheaves. Let
`f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of `S`
and let `G` be an étale sheaf of modules on `𝒴` with the flat base change property. Then the
inverse image `f^{-1}G` has the flat base change property.

The comparison map of `f^{-1}G` at an arrow `ψ` is identified with that of `G` at `f ψ`, as in the
source by way of **Stacks 075D**; see the implementation notes of this file. -/
theorem hasSheafFlatBaseChangeProperty_modulePresheafPullback [UnivLE.{u, m}]
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'}
    [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids)
    (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hGsh : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)
    (hG : HasSheafFlatBaseChangeProperty B E h S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    HasSheafFlatBaseChangeProperty B E h S hS (f ⋙ q) hp (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) := by
  intro z z' ψ hflat
  exact (isLocallyBijective_pullbackComparison_modulePresheafPullback_iff
    B E h S hS q hq f hp G hGsh ψ).2 (hG (f.map ψ) hflat)

/-- The inverse image along a 1-morphism of categories fibred in groupoids preserves membership in
`LQCoh^fbc`: local quasi-coherence by **Stacks 06WL**
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_modulePullback`), and the flat base change
property by **Stacks 0764 (1)**
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_modulePresheafPullback`). -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback [UnivLE.{u, m}]
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'}
    [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids)
    (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS q hq G) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS (f ⋙ q) hp
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) :=
  ⟨isLocallyQuasicoherent_modulePullback B E h S hS q hq f hp (hq.isFibredOneMorphism rfl) G hG.1,
    hasSheafFlatBaseChangeProperty_modulePresheafPullback B E h S hS q hq f hp G hG.1.1 hG.2⟩

/-- The inverse image of sheaves of modules `AlgebraicGeometry.Stack.modulePullback`, along a
1-morphism `f` of categories fibred in groupoids with `f ⋙ q = p` and computed in any topology
`τ` below the fppf one, preserves membership in `LQCoh^fbc`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback [UnivLE.{u, m}]
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (G : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ))
    (hG : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS q hq G.val) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp
      ((modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).obj G).val := by
  subst hf
  exact isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback B E h S hS q hq f hp
    G.val hG

/-- The inverse image `Stacks.RelativeCech.moduleInverseImage` on the `τ`-sites is
`AlgebraicGeometry.Stack.modulePullback` at the base topology of `τ`: both are the pushforward of
sheaves of modules along the identification of the structure sheaf of the source with the
restriction of that of the target, and any two such identifications agree. -/
theorem moduleInverseImage_eq_modulePullback {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'}
    [Category.{w'} 𝒴] (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (τ : SiteKind) :
    Stacks.RelativeCech.moduleInverseImage.{u, v, v', w, w', m} B S hS p q hp hq f hf τ =
      modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf (B.baseTopology τ)
        (B.baseTopology_le_topology τ) := by
  unfold Stacks.RelativeCech.moduleInverseImage modulePullback
  congr 1
  ext1
  simp only [ringStructureSheafCoreHom]
  exact eqToHom_map (sheafToPresheaf _ _) _

section AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **Stacks 0771, part (3)**, on `Mod(𝒳_ét, 𝒪_𝒳)`: the inverse image along a 1-morphism of
algebraic stacks of the étale sites carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0771 "part (3), on Mod(𝒳_ét, 𝒪_𝒳), with the flat base change property of 0762 read on \
  sheaves; the module sections in the universe of the schemes"]
theorem lqcohSheafFbcEtaleModules_stackModuleInverseImage (F : StackModules B S hS .etale 𝒴)
    (hF : lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒴 F) :
    lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳
      ((stackModuleInverseImage B S hS .etale f).obj F) := by
  dsimp only [stackModuleInverseImage, lqcohSheafFbcEtaleModules]
  rw [moduleInverseImage_eq_modulePullback]
  exact isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback B E h S hS 𝒳.val.val.p
    𝒴.val.val.p _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p f.hom) _ _ F hF

/-- **Stacks 0771, part (3)**, on `Mod(𝒪_𝒳)`: the inverse image along a 1-morphism of algebraic
stacks of the fppf sites carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0771 "part (3), on Mod(𝒪_𝒳), with the flat base change property of 0762 read on \
  sheaves; the module sections in the universe of the schemes"]
theorem lqcohSheafFbcFppfModules_fppfModulesPullback (F : fppfModules B S hS 𝒴)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 F) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 ((fppfModulesPullback B S hS f).obj F) :=
  isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback B E h S hS 𝒳.val.val.p
    𝒴.val.val.p _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p f.hom) _ _ F hF

/-- **Stacks 0771, part (3)**, the functor
`f^* : LQCoh^fbc(𝒪_𝒴) ⥤ LQCoh^fbc(𝒪_𝒳)` on the étale sites, induced by
`AlgebraicGeometry.Stack.stackModuleInverseImage`. -/
noncomputable def lqcohSheafFbcEtaleModulesPullback :
    (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒴).FullSubcategory ⥤
      (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).FullSubcategory :=
  ObjectProperty.lift _
    ((lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒴).ι ⋙
      stackModuleInverseImage B S hS .etale f)
    (fun F => lqcohSheafFbcEtaleModules_stackModuleInverseImage B E h S hS f F.obj F.property)

/-- The functor `f^*` on `LQCoh^fbc` of the étale sites is the inverse image of modules. -/
theorem lqcohSheafFbcEtaleModulesPullback_comp_ι :
    lqcohSheafFbcEtaleModulesPullback B E h S hS f ⋙
        (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).ι =
      (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒴).ι ⋙
        stackModuleInverseImage B S hS .etale f :=
  rfl

/-- **Stacks 0771, part (3)**, the functor
`f^* : LQCoh^fbc(𝒪_𝒴) ⥤ LQCoh^fbc(𝒪_𝒳)` on the fppf sites, induced by
`AlgebraicGeometry.Stack.fppfModulesPullback`. -/
noncomputable def lqcohSheafFbcFppfModulesPullback :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory :=
  ObjectProperty.lift _
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ fppfModulesPullback B S hS f)
    (fun F => lqcohSheafFbcFppfModules_fppfModulesPullback B E h S hS f F.obj F.property)

/-- The functor `f^*` on `LQCoh^fbc` of the fppf sites is the inverse image of modules. -/
theorem lqcohSheafFbcFppfModulesPullback_comp_ι :
    lqcohSheafFbcFppfModulesPullback B E h S hS f ⋙
        (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι =
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ fppfModulesPullback B S hS f :=
  rfl

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
