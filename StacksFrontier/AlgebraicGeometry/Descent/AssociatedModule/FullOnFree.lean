module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssentialImage
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# Fullness of the associated-module functor on free modules

`AlgebraicGeometry.BigFppfOver.IsFullOnFree` is the one input of Stacks 03DX (1) that
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssentialImage` leaves as a hypothesis:
every morphism `𝓕^a ⟶ 𝓖^a` between the associated modules of two free `𝒪_S`-modules comes from a
morphism `𝓕 ⟶ 𝓖` of free `𝒪_S`-modules.  This file reduces it to a single statement about
*sections*.

The reduction is formal.  A morphism out of a free sheaf of modules is a family of sections of
the target (`SheafOfModules.freeHomEquiv`), so a morphism `u : M ⟶ N` through which every
morphism from a free module factors is exactly one that is surjective on sections.  Applying
this to the unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` of the adjunction between the associated-module functor
and restriction, and using that the adjunction bijection carries `β ↦ β^a` to
`β ↦ β ≫ unit`, turns fullness on free modules into surjectivity of the unit on global
sections.

## Main results

* `SheafOfModules.exists_comp_eq_of_surjective_sectionsMap`: a morphism that is surjective on
  sections is one through which every morphism out of a free module factors.
* `SheafOfModules.surjective_sectionsMap_of_isIso`: an isomorphism is surjective on sections.
* `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullback_map`: under the
  pullback–pushforward adjunction, the pullback of `β` corresponds to `β` composed with the
  unit.
* `SheafOfModules.exists_pullback_map_eq_of_surjective_sectionsMap_unit`: fullness of the
  pullback functor on free modules, from surjectivity of the unit on sections.
* `SheafOfModules.pullback_additive`: the pullback of sheaves of modules along a morphism of
  ringed sites is an additive functor, hence preserves finite coproducts.  Additivity of the
  pushforward, which this deduces it from, is already in the tree at
  `StacksFrontier/CategoryTheory/Sites/Modules/OverFunctorExact.lean`.
* `AlgebraicGeometry.BigFppfOver.isFullOnFree_of_surjective_sectionsMap_unit` and
  `AlgebraicGeometry.BigFppfOver.isFullOnFree_of_isIso_unit`: the same for the
  associated-module functor of the big fppf site of `S`, where the conclusion is
  `AlgebraicGeometry.BigFppfOver.IsFullOnFree` itself.

## Implementation notes

Everything here is stated for `τ = fppf` only, as in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor`: the morphism of ringed sites
whose pullback is `𝓕 ↦ 𝓕^a` is built on `AlgebraicGeometry.BigFppfOver.structureSheaf`, which
exists in the library only for the localized fppf topology.

Nothing here is tagged: the reduction is an implication, not one of the clauses of Stacks 03DX.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

namespace SheafOfModules

section Sections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Surjectivity on sections is fullness on free modules.**  If `u : M ⟶ N` is surjective on
sections then every morphism from a free sheaf of modules to `N` factors through `u`: a morphism
out of `free I` is a family of sections indexed by `I`, and lifting the family lifts the
morphism. -/
public theorem exists_comp_eq_of_surjective_sectionsMap {M N : SheafOfModules.{u} R} (u : M ⟶ N)
    (hu : Function.Surjective (sectionsMap u)) {I : Type u} (γ : free I ⟶ N) :
    ∃ β : free (R := R) I ⟶ M, β ≫ u = γ := by
  choose s hs using fun i => hu (freeHomEquiv N γ i)
  refine ⟨(freeHomEquiv M).symm s, ?_⟩
  rw [freeHomEquiv_symm_comp, funext hs]
  exact (freeHomEquiv N).symm_apply_apply γ

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- An isomorphism of sheaves of modules is surjective on sections.  The hypothesis is explicit
because the morphisms this is applied to are definitionally, but not syntactically, the units of
the adjunction that instance search would have to recognize. -/
public theorem surjective_sectionsMap_of_isIso {M N : SheafOfModules.{u} R} (u : M ⟶ N)
    (hu : IsIso u) : Function.Surjective (sectionsMap u) :=
  let := hu
  fun t => ⟨sectionsMap (inv u) t, by rw [← sectionsMap_comp, IsIso.inv_hom_id, sectionsMap_id]⟩

end Sections

section Pullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- Under the pullback–pushforward adjunction, the pullback of a morphism `β` corresponds to
`β` composed with the unit of the adjunction. -/
public theorem pullbackPushforwardAdjunction_homEquiv_pullback_map
    {M N : SheafOfModules.{u} S} (β : M ⟶ N) :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv M ((pullback.{u} φ).obj N)
        ((pullback.{u} φ).map β)
      = β ≫ (pullbackPushforwardAdjunction.{u} φ).unit.app N := by
  rw [Adjunction.homEquiv_unit, ← Functor.comp_map]
  exact ((pullbackPushforwardAdjunction.{u} φ).unit.naturality β).symm

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Fullness of the pullback on free modules, from surjectivity of the unit on sections.**
If the unit of the pullback–pushforward adjunction at `free I₁` is surjective on sections, then
every morphism between the pullbacks of `free I₂` and `free I₁` is the pullback of a morphism
`free I₂ ⟶ free I₁`. -/
public theorem exists_pullback_map_eq_of_surjective_sectionsMap_unit {I₁ I₂ : Type u}
    (hu : Function.Surjective (sectionsMap
      ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I₁))))
    (α : (pullback.{u} φ).obj (free I₂) ⟶ (pullback.{u} φ).obj (free I₁)) :
    ∃ β : free (R := S) I₂ ⟶ free I₁, (pullback.{u} φ).map β = α := by
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_surjective_sectionsMap _ hu
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ α)
  refine ⟨β, ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).injective ?_⟩
  rw [pullbackPushforwardAdjunction_homEquiv_pullback_map]
  exact hβ

omit [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Fullness of the pullback on free modules, from the unit being an isomorphism.** -/
public theorem exists_pullback_map_eq_of_isIso_unit {I₁ I₂ : Type u}
    [IsIso ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I₁))]
    (α : (pullback.{u} φ).obj (free I₂) ⟶ (pullback.{u} φ).obj (free I₁)) :
    ∃ β : free (R := S) I₂ ⟶ free I₁, (pullback.{u} φ).map β = α :=
  exists_pullback_map_eq_of_surjective_sectionsMap_unit φ
    (surjective_sectionsMap_of_isIso _ inferInstance) α

end Pullback

section Additive

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

-- `SheafOfModules.pushforward_additive`, the additivity of the pushforward, is **not** declared
-- here: it is already in the library at
-- `StacksFrontier/CategoryTheory/Sites/Modules/OverFunctorExact.lean:95`, at the same generality,
-- and that module is imported above. Redeclaring it here would make
-- the fully-qualified name `SheafOfModules.pushforward_additive` ambiguous and turn
-- module-mode elaboration of the library's root module into a hard error.

variable [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- The pullback of sheaves of modules along a morphism of ringed sites is additive, being a
left adjoint of an additive functor. -/
public instance pullback_additive : (pullback.{u} φ).Additive :=
  (pullbackPushforwardAdjunction.{u} φ).left_adjoint_additive

end Additive

end SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reduction of `IsFullOnFree` to a statement about sections.**  If the unit
`𝓕 ⟶ (𝓕^a)|_{S_Zar}` of the adjunction between the associated-module functor and restriction is
surjective on global sections at every free `𝒪_S`-module, then the associated-module functor of
the big fppf site of `S` is full on free modules. -/
public theorem isFullOnFree_of_surjective_sectionsMap_unit
    (h : ∀ I : Type u, Function.Surjective (SheafOfModules.sectionsMap
      ((associatedModuleAdjunction B S hS).unit.app
        (SheafOfModules.free (R := S.ringCatSheaf) I)))) :
    IsFullOnFree B S hS := fun I₁ _ α =>
  SheafOfModules.exists_pullback_map_eq_of_surjective_sectionsMap_unit
    (structureMap B S hS) (h I₁) α

/-- **The reduction of `IsFullOnFree` to the unit being an isomorphism.** -/
public theorem isFullOnFree_of_isIso_unit
    (h : ∀ I : Type u, IsIso ((associatedModuleAdjunction B S hS).unit.app
      (SheafOfModules.free (R := S.ringCatSheaf) I))) :
    IsFullOnFree B S hS :=
  isFullOnFree_of_surjective_sectionsMap_unit B S hS fun I =>
    SheafOfModules.surjective_sectionsMap_of_isIso _ (h I)

end AlgebraicGeometry.BigFppfOver

end
