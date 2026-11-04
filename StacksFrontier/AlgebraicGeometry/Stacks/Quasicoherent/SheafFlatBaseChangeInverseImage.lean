module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulePullbackOfStacks

/-!
# Inverse image preserves the flat base change property of Stacks 0762 (sheaf form)

**Stacks 0764** part (1) says that the inverse image of a module with the flat base change
property has it again, and together with **Stacks 06WL** this is **Stacks 0771** part (3): the
inverse image along a 1-morphism of algebraic stacks carries `LQCoh^fbc` into `LQCoh^fbc`.
This file proves both for the flat base change property of the source, read with the pullback of
*sheaves* (`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`: the comparison map
`c_φ` of **Stacks 06WC** is locally bijective), at every module universe above that of the schemes.

The argument is that of the library's presheaf form
(`AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_modulePresheafPullback`): by
**Stacks 075D** part (4) the comparison map of `f⁻¹G` along `ψ` and that of `G` along `f ψ` are
mates of comparisons which agree on sections under the identifications of **Stacks 075D**
part (3). Here this is read as an equation: the one comparison is the other composed with two
isomorphisms (`PresheafOfModules.exists_iso_homEquiv_symm_eq_of_sections`), so the two are locally
bijective together.

## Main results

* `PresheafOfModules.exists_iso_homEquiv_symm_eq_of_sections`.
* `Stack.isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_inverseImage_iff`:
  **Stacks 075D** part (4) for local bijectivity.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangePropertyUnivLE_modulePresheafPullback`:
  **Stacks 0764** part (1).
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback`
  and `AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChange_fppfModulePullbackOfStacks`:
  **Stacks 0771** part (3), for sheaves of modules along a strictly presented 1-morphism and for
  the fppf modules of algebraic stacks at module universe `u + 1`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
-/

@[expose] public section

open CategoryTheory

universe u v w v' w' m

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- Two pushforward comparisons, along equal maps of presheaves of rings, which agree on sections
under isomorphisms of their sources and of their targets have mates under the pullback-pushforward
adjunction which differ by isomorphisms. -/
theorem exists_iso_homEquiv_symm_eq_of_sections {φ₁ φ₂ : S ⟶ F.op ⋙ R} (hφ : φ₁ = φ₂)
    [h₁ : (pushforward.{m} φ₁).IsRightAdjoint] [h₂ : (pushforward.{m} φ₂).IsRightAdjoint]
    {M₁ M₂ : PresheafOfModules.{m} S} {N₁ N₂ : PresheafOfModules.{m} R}
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂)
    (ρ₁ : M₁ ⟶ (pushforward.{m} φ₁).obj N₁) (ρ₂ : M₂ ⟶ (pushforward.{m} φ₂).obj N₂)
    (hsq : ∀ (W : Cᵒᵖ) (n : M₁.obj W),
      ρ₂.app W (eM.hom.app W n) = eN.hom.app (Opposite.op (F.obj W.unop)) (ρ₁.app W n)) :
    ∃ (α : (pullback.{m} φ₂).obj M₂ ≅ (pullback.{m} φ₁).obj M₁) (β : N₁ ≅ N₂),
      ((pullbackPushforwardAdjunction.{m} φ₂).homEquiv _ _).symm ρ₂ =
        α.hom ≫ ((pullbackPushforwardAdjunction.{m} φ₁).homEquiv _ _).symm ρ₁ ≫ β.hom := by
  subst hφ
  let adj := pullbackPushforwardAdjunction.{m} φ₁
  have hsq' : eM.hom ≫ ρ₂ = ρ₁ ≫ (pushforward.{m} φ₁).map eN.hom := by
    ext W n
    exact hsq W n
  have hmate : (pullback.{m} φ₁).map eM.hom ≫ (adj.homEquiv _ _).symm ρ₂ =
      (adj.homEquiv _ _).symm ρ₁ ≫ eN.hom := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, hsq']
  refine ⟨(pullback.{m} φ₁).mapIso eM.symm, eN, ?_⟩
  rw [Functor.mapIso_hom, Iso.symm_hom, ← hmate, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end PresheafOfModules

namespace CategoryTheory.Presheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA]

/-- Local injectivity and local surjectivity transfer along a factorization through
isomorphisms. -/
theorem isLocallyBijective_of_eq_iso_comp_comp_iso {P₁ P₂ Q₁ Q₂ : Cᵒᵖ ⥤ A} {c₁ : P₁ ⟶ Q₁}
    {c₂ : P₂ ⟶ Q₂} (α : P₂ ≅ P₁) (β : Q₁ ≅ Q₂) (hc : c₂ = α.hom ≫ c₁ ≫ β.hom)
    (h : IsLocallyInjective J c₁ ∧ IsLocallySurjective J c₁) :
    IsLocallyInjective J c₂ ∧ IsLocallySurjective J c₂ := by
  obtain ⟨_, _⟩ := h
  subst hc
  exact ⟨inferInstance, inferInstance⟩

end CategoryTheory.Presheaf

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- Two pushforward comparisons, along equal maps of presheaves of rings, which agree on sections
under isomorphisms of their sources and of their targets have mates which are locally injective
and locally surjective together, for any topology. -/
theorem isLocallyBijective_homEquiv_symm_iff_of_sections (J : GrothendieckTopology D)
    {φ₁ φ₂ : S ⟶ F.op ⋙ R} (hφ : φ₁ = φ₂)
    [h₁ : (pushforward.{m} φ₁).IsRightAdjoint] [h₂ : (pushforward.{m} φ₂).IsRightAdjoint]
    {M₁ M₂ : PresheafOfModules.{m} S} {N₁ N₂ : PresheafOfModules.{m} R}
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂)
    (ρ₁ : M₁ ⟶ (pushforward.{m} φ₁).obj N₁) (ρ₂ : M₂ ⟶ (pushforward.{m} φ₂).obj N₂)
    (hsq : ∀ (W : Cᵒᵖ) (n : M₁.obj W),
      ρ₂.app W (eM.hom.app W n) = eN.hom.app (Opposite.op (F.obj W.unop)) (ρ₁.app W n)) :
    (Presheaf.IsLocallyInjective J ((toPresheaf R).map
        (((pullbackPushforwardAdjunction.{m} φ₁).homEquiv _ _).symm ρ₁)) ∧
      Presheaf.IsLocallySurjective J ((toPresheaf R).map
        (((pullbackPushforwardAdjunction.{m} φ₁).homEquiv _ _).symm ρ₁))) ↔
    (Presheaf.IsLocallyInjective J ((toPresheaf R).map
        (((pullbackPushforwardAdjunction.{m} φ₂).homEquiv _ _).symm ρ₂)) ∧
      Presheaf.IsLocallySurjective J ((toPresheaf R).map
        (((pullbackPushforwardAdjunction.{m} φ₂).homEquiv _ _).symm ρ₂))) := by
  obtain ⟨α, β, hc⟩ := exists_iso_homEquiv_symm_eq_of_sections hφ eM eN ρ₁ ρ₂ hsq
  exact ⟨Presheaf.isLocallyBijective_of_eq_iso_comp_comp_iso ((toPresheaf R).mapIso α)
      ((toPresheaf R).mapIso β) (by simp [hc]),
    Presheaf.isLocallyBijective_of_eq_iso_comp_comp_iso ((toPresheaf R).mapIso α.symm)
      ((toPresheaf R).mapIso β.symm) (by simp [hc])⟩

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
  (hp : (f ⋙ q).IsFiberedInGroupoids) (hf : (f ⋙ q).IsFibredOneMorphism q f)
  (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hG : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)

include hG hf in
/-- **Stacks 075D part (4) for the sheaf form of the comparison.** The comparison map of
Stacks 06WC for `f⁻¹G` along `ψ` is locally bijective exactly when the one for `G` along `f ψ`
is, at any module universe above that of the schemes. -/
theorem isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_inverseImage_iff
    [UnivLE.{u, m}] {y' y : 𝒳} (ψ : y' ⟶ y) :
    IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE B E h S hS (f ⋙ q) hp
        (etaleTopology B) (etaleTopology_le_topology B) ψ
        ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) ↔
      IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE B E h S hS q hq
        (etaleTopology B) (etaleTopology_le_topology B) (f.map ψ) G := by
  exact (PresheafOfModules.isLocallyBijective_homEquiv_symm_iff_of_sections
    (SmallEtale.topology E (q.obj (f.obj y')).left.1 (contains_base B E h S hS q (f.obj y')))
    ((smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS (f ⋙ q) hp
        (etaleTopology B) (etaleTopology_le_topology B) ψ).trans
      (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS q hq
        (etaleTopology B) (etaleTopology_le_topology B) (f.map ψ)).symm)
    (h₂ := isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE.{u, v', w', m}
      B E h S hS q hq (f.map ψ) (etaleTopology B) (etaleTopology_le_topology B))
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf y)
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf y')
    _ _
    (restrictModulePushforwardComparison_inverseImageIso_apply B E h S hS q hq f hp hf G hG ψ))

include hG hf in
/-- **Stacks 0764 part (1)**, for the flat base change property of Stacks 0762 read with the
pullback of sheaves, at any module universe above that of the schemes. -/
theorem hasSheafFlatBaseChangePropertyUnivLE_modulePresheafPullback [UnivLE.{u, m}]
    (hfbc : HasSheafFlatBaseChangeProperty B E h S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    HasSheafFlatBaseChangeProperty B E h S hS (f ⋙ q) hp (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) :=
  fun ψ hflat =>
    (isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_inverseImage_iff B E h S hS q hq f
      hp hf G hG ψ).2 (hfbc (f.map ψ) hflat)

/-- **Stacks 0771 part (3)** for sheaves of modules along a strictly presented 1-morphism of
categories fibred in groupoids, with the flat base change property of the source: the inverse
image of Stacks 06WE carries a module which is locally quasi-coherent with the flat base change
property into one, at any module universe above that of the schemes. Local quasi-coherence is
**Stacks 06WL** and the flat base change property is **Stacks 0764** part (1). -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback
    {𝒳' : Type v} [Category.{w} 𝒳'] (p : 𝒳' ⥤ BigFppfOver B S hS) (hp' : p.IsFiberedInGroupoids)
    (f' : 𝒳' ⥤ 𝒴) (hf' : f' ⋙ q = p) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    [UnivLE.{u, m}] (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ))
    (hM : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS q hq M.val) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp'
      ((modulePullback.{u, v, w, m, v', w'} B S hS p q hp' hq f' hf' τ hτ).obj M).val := by
  subst hf'
  have hfo := hq.isFibredOneMorphism (rfl : f' ⋙ q = f' ⋙ q)
  exact ⟨isLocallyQuasicoherent_modulePullback B E h S hS q hq f' hp' hfo M.val hM.1,
    hasSheafFlatBaseChangePropertyUnivLE_modulePresheafPullback B E h S hS q hq f' hp' hfo
      M.val hM.1.1 hM.2⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0771 part (3)** for algebraic stacks, at module universe `u + 1`, with the flat base
change property of the source: the inverse image `f^*` along a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`. -/
theorem locallyQuasicoherentSheafFlatBaseChange_fppfModulePullbackOfStacks
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (F : fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)
    (hF : lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴 F) :
    lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳
      ((fppfModulePullbackOfStacks B S hS f).obj F) :=
  isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback.{u, u + 1, u, u + 1, u, u + 1}
    B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) F hF

end AlgebraicGeometry.Stack
