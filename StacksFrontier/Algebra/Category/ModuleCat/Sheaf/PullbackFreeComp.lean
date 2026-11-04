module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMate
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The free identifications are compatible with the contraction of an iterated pullback

Let `F : C ⥤ D` and `G : D ⥤ D'` be continuous functors between sites and let
`φ : S ⟶ F_*R` and `ψ : R ⟶ G_*R'` be morphisms of sheaves of rings. Extension of scalars
carries a free sheaf of modules to a free sheaf of modules on the same index type, by Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`, and the iterated extension of scalars is
extension of scalars along the composite, by Mathlib's
`CategoryTheory.SheafOfModules.pullbackComp`. This file proves that **the two agree**: going
around the iterated pullback and identifying the free module at each of the two stages is the
same as contracting the iterated pullback first and identifying once.

This is the coherence the full faithfulness half of Stacks Tag 0EXD needs. A square of schemes
gives a comparison of the two composite transition functors of Stacks Tag 0EXE, and that
comparison is built out of two contractions of an iterated extension of scalars; the square of
Hom-sets of *free* modules which full faithfulness of the comparison functor asks for is the
naive square of extensions of scalars only once that comparison is known to agree with the free
identifications, which is exactly what is proved here.

## Main results

* `Stacks.SheafOfModules.pullbackComp_hom_app_unit_comp_pullbackObjUnitToUnit`: **the comparison
  of the unit sheaves is compatible with the contraction of an iterated pullback.** No finality
  hypothesis is needed, so this holds whenever the two extensions of scalars exist.
* `Stacks.SheafOfModules.pullbackComp_hom_app_free_comp_pullbackObjFreeIso_hom`: **the free
  identifications are compatible with the contraction of an iterated pullback**, for an arbitrary
  index type.

## Implementation notes

The free statement is reduced to the unit statement and not proved directly: a free sheaf of
modules is a coproduct of copies of the unit sheaf, extension of scalars preserves that
coproduct, and Mathlib's
`CategoryTheory.SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom` says the free
identification turns the `i`-th tautological inclusion into the unit comparison followed by the
`i`-th tautological inclusion. So both sides of the free statement agree after each tautological
inclusion as soon as the unit statement holds, and `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`
finishes.

The unit statement is proved by transposing across the composite of the two
pullback–pushforward adjunctions, where it becomes a statement about *pushforwards*, i.e. about
restriction of scalars, and there both sides are computed on sections by the two ring maps in
succession. The transposition of the contraction is
`Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp`, which identifies its mate with the
contraction of the iterated pushforward, together with
`CategoryTheory.unit_conjugateEquiv`; everything else is the naturality of the two adjunctions'
unit.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {F : C ⥤ D} {G : D ⥤ D'}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

omit [Functor.IsContinuous (F ⋙ G) J K'] in
/-- **The comparison of the unit sheaves with their pushforwards is compatible with the
contraction of an iterated pushforward.** Both sides send a section of `S` over `U` to the image
of its image under `φ` under `ψ`. -/
theorem unitToPushforwardObjUnit_comp_pushforwardComp_inv :
    unitToPushforwardObjUnit (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ≫
        (_root_.SheafOfModules.pushforwardComp.{u} φ ψ).inv.app (unit R') =
      unitToPushforwardObjUnit φ ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map (unitToPushforwardObjUnit ψ) := by
  ext U
  exact rfl

section Pullback

variable [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- **The comparison of the unit sheaves is compatible with the contraction of an iterated
pullback.** Extension of scalars along `ψ` of the unit comparison of `φ`, followed by the unit
comparison of `ψ`, is the contraction of the iterated extension of scalars followed by the unit
comparison of the composite.

No finality hypothesis appears: the three morphisms compared are the transposes of the three
`Stacks.SheafOfModules.unitToPushforwardObjUnit`, and the identity between those is
`Stacks.SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardComp_inv`. -/
theorem pullbackComp_hom_app_unit_comp_pullbackObjUnitToUnit :
    (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (unit S) ≫
        pullbackObjUnitToUnit (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) =
      (_root_.SheafOfModules.pullback.{u} ψ).map (pullbackObjUnitToUnit φ) ≫
        pullbackObjUnitToUnit ψ := by
  have hconj : conjugateEquiv
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} ψ))
      (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom =
      (_root_.SheafOfModules.pushforwardComp.{u} φ ψ).inv :=
    congrArg Iso.hom (conjugateIsoEquiv_pullbackComp.{u} φ ψ)
  have hL : ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} ψ)).homEquiv (unit S) (unit R')
        ((_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (unit S) ≫
          pullbackObjUnitToUnit (F := F ⋙ G)
            (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) =
      unitToPushforwardObjUnit (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ≫
        (_root_.SheafOfModules.pushforwardComp.{u} φ ψ).inv.app (unit R') := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      ← unit_conjugateEquiv
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} ψ))
        (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom (unit S),
      hconj, Category.assoc, ← NatTrans.naturality, ← Category.assoc,
      ← Adjunction.homEquiv_unit,
      _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hR : ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} ψ)).homEquiv (unit S) (unit R')
        ((_root_.SheafOfModules.pullback.{u} ψ).map (pullbackObjUnitToUnit φ) ≫
          pullbackObjUnitToUnit ψ) =
      unitToPushforwardObjUnit φ ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map (unitToPushforwardObjUnit ψ) := by
    rw [Adjunction.comp_homEquiv]
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left,
      _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
      Adjunction.homEquiv_naturality_right,
      _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  refine (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} ψ)).homEquiv
      (unit S) (unit R')).injective ?_
  rw [hL, hR]
  exact unitToPushforwardObjUnit_comp_pushforwardComp_inv φ ψ

section Free

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [HasWeakSheafify K' AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.Final] [G.Final] [(F ⋙ G).Final]

omit [Functor.IsContinuous (F ⋙ G) J K'] [(F ⋙ G).Final] in
/-- **A transformation of an iterated pullback into a single pullback which is compatible with
the unit identifications is compatible with the free identifications.** The target morphism of
sheaves of rings `χ` and the transformation `τ` are parameters and the unit compatibility is a
hypothesis, so that nothing here mentions a composite morphism of sheaves of rings.

A free sheaf of modules is a coproduct of copies of the unit sheaf and extension of scalars
preserves that coproduct, so both sides agree as soon as they agree after each tautological
inclusion; there Mathlib's
`CategoryTheory.SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom` leaves exactly the
hypothesis.

The continuous functor `H` along which `χ` pushes forward is a parameter of its own and is *not*
required to be the composite `F ⋙ G`: the statement never uses the relation between them, and a
consumer whose `χ` is pushed forward along a functor only definitionally equal to `F ⋙ G` — the
inverse image of opens along a composite of morphisms of schemes, say — would otherwise have to
present it in the composite spelling, in which instance resolution for its extension of scalars
does not succeed. -/
theorem free_comp_pullbackObjFreeIso_hom_of_unit {H : C ⥤ D'}
    [Functor.IsContinuous H J K'] [H.Final]
    (χ : S ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K').obj R')
    [(_root_.SheafOfModules.pushforward.{u} χ).IsRightAdjoint]
    (τ : _root_.SheafOfModules.pullback.{u} φ ⋙ _root_.SheafOfModules.pullback.{u} ψ ⟶
      _root_.SheafOfModules.pullback.{u} χ)
    (hτ : τ.app (unit S) ≫ pullbackObjUnitToUnit χ =
      (_root_.SheafOfModules.pullback.{u} ψ).map (pullbackObjUnitToUnit φ) ≫
        pullbackObjUnitToUnit ψ)
    (I : Type u) :
    τ.app (free (R := S) I) ≫ (pullbackObjFreeIso χ I).hom =
      (_root_.SheafOfModules.pullback.{u} ψ).map (pullbackObjFreeIso φ I).hom ≫
        (pullbackObjFreeIso ψ I).hom := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (_root_.SheafOfModules.pullback.{u} φ ⋙ _root_.SheafOfModules.pullback.{u} ψ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ fun i => ?_
  have hnat := τ.naturality (ιFree (R := S) i)
  dsimp only [Functor.comp_obj, Functor.comp_map, cofan_mk_inj] at hnat ⊢
  rw [← Category.assoc, hnat, Category.assoc,
    _root_.SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom, ← Category.assoc, hτ]
  simp [← Functor.map_comp_assoc]

/-- **The free identifications are compatible with the contraction of an iterated pullback.**
Extension of scalars along `ψ` of the free identification of `φ`, followed by the free
identification of `ψ`, is the contraction of the iterated extension of scalars followed by the
free identification of the composite.

This is
`Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit` at the contraction itself, whose
unit compatibility is
`Stacks.SheafOfModules.pullbackComp_hom_app_unit_comp_pullbackObjUnitToUnit`. -/
theorem pullbackComp_hom_app_free_comp_pullbackObjFreeIso_hom (I : Type u) :
    (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (free (R := S) I) ≫
        (pullbackObjFreeIso (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) I).hom =
      (_root_.SheafOfModules.pullback.{u} ψ).map (pullbackObjFreeIso φ I).hom ≫
        (pullbackObjFreeIso ψ I).hom :=
  free_comp_pullbackObjFreeIso_hom_of_unit φ ψ _
    (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom
    (pullbackComp_hom_app_unit_comp_pullbackObjUnitToUnit φ ψ) I

end Free

end Pullback

end Stacks.SheafOfModules

end
