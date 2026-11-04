module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictionAlongCocontinuous

/-!
# Presentations and generating sections across a fully faithful functor

Let `Φ : Mod(R₁) ⥤ Mod(R₂)` be a functor between categories of sheaves of modules which preserves
colimits and carries the structure sheaf to the structure sheaf.  Such a functor carries a
presentation of a module `M` — a cokernel presentation by free modules, Mathlib's
`SheafOfModules.Presentation` — to a presentation of `Φ M` with the same index types; this is
Mathlib's `SheafOfModules.Presentation.map`.  This file proves the converse when `Φ` is moreover
fully faithful: a presentation of `Φ M` comes from a presentation of `M`, again with the same
index types, so finiteness of a presentation is reflected as well as preserved.  It is the
presentation counterpart of `Stacks.Sheaves.GlobalTypeComparison`, which does the same for the
global types of Modules on Sites, Definition 03DE.

It also records that restriction of sheaves of modules along `Over.map f`, Mathlib's
`SheafOfModules.overMap`, preserves colimits over an essentially small site, at the universe of
the coefficient rings; `Stacks.SheafOfModules.overMap_preservesColimits` proves the same when the
universe of the module sections dominates the universes of the site.

## Main definitions

* `Stacks.SheafOfModules.presentationOfMap`: a presentation of `Φ M` pulled back to a presentation
  of `M` with the same index types.

## Main results

* `Stacks.SheafOfModules.presentationOfMap_isFinite`: the pulled-back presentation is finite
  when the given one is.
* `Stacks.SheafOfModules.presentation_map_isFinite`: `Presentation.map` keeps a presentation
  finite.
* `Stacks.SheafOfModules.preservesColimitsOfSize_overMap`: restriction along `Over.map f`
  preserves colimits over an essentially small site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

section Presentation

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {R₁ : Sheaf J₁ RingCat.{w}}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{w}}
  [HasSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (Φ : _root_.SheafOfModules.{w} R₁ ⥤ _root_.SheafOfModules.{w} R₂)
  [PreservesColimitsOfSize.{w, w} Φ]
  (η : _root_.SheafOfModules.unit R₂ ≅ Φ.obj (_root_.SheafOfModules.unit R₁))

/-- A presentation whose two index types are finite is finite. -/
private theorem presentation_isFinite_of_finite {M : _root_.SheafOfModules.{w} R₁}
    (P : M.Presentation) (h₁ : Finite P.generators.I) (h₂ : Finite P.relations.I) :
    P.IsFinite :=
  ⟨⟨h₁⟩, ⟨h₂⟩⟩

include η

/-- `SheafOfModules.Presentation.map` keeps a finite presentation finite: it leaves the two index
types unchanged. -/
theorem presentation_map_isFinite {M : _root_.SheafOfModules.{w} R₁} (P : M.Presentation)
    [P.IsFinite] : (P.map Φ η).IsFinite :=
  presentation_isFinite_of_finite _ (inferInstanceAs (Finite P.generators.I))
    (inferInstanceAs (Finite P.relations.I))

variable [Φ.Full] [Φ.Faithful]

/-- **A presentation of `Φ M` comes from a presentation of `M`**, for a fully faithful,
colimit-preserving `Φ` carrying the structure sheaf to the structure sheaf.  The two free modules
of the given presentation are images of free modules, the two maps of the presentation are images
of maps by fullness, and the cokernel is reflected by full faithfulness. -/
def presentationOfMap {M : _root_.SheafOfModules.{w} R₁} (P : (Φ.obj M).Presentation) :
    M.Presentation :=
  let eI := _root_.SheafOfModules.mapFreeIso Φ P.generators.I η
  let eK := _root_.SheafOfModules.mapFreeIso Φ P.relations.I η
  let f' : _root_.SheafOfModules.free P.relations.I ⟶
      _root_.SheafOfModules.free P.generators.I :=
    (kernel P.generators.π).freeHomEquiv.symm P.relations.s ≫ kernel.ι P.generators.π
  let f := Φ.preimage (eK.inv ≫ f' ≫ eI.hom)
  let g := Φ.preimage (eI.inv ≫ P.generators.π)
  have H : f ≫ g = 0 := Φ.map_injective (by
    simp only [f, g, f', Functor.map_comp, Functor.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, kernel.condition, comp_zero, Functor.map_zero])
  have l : IsColimit (CokernelCofork.ofπ (Φ.map g)
      (by rw [← Φ.map_comp, H, Φ.map_zero]) : Cofork (Φ.map f) 0) :=
    Cofork.isColimitOfIsos _ P.isColimit _ eK eI (Iso.refl _)
      (by simp only [f, f', Functor.map_preimage, Iso.hom_inv_id_assoc, Category.assoc])
      (by simp) (by simp [g])
  _root_.SheafOfModules.presentationOfIsCokernelFree f g H
    (isColimitOfReflects Φ ((isColimitMapCoconeCoforkEquiv' Φ H).symm l))

/-- The presentation pulled back along `Φ` has the generators of the given one. -/
theorem presentationOfMap_generators_I {M : _root_.SheafOfModules.{w} R₁}
    (P : (Φ.obj M).Presentation) :
    (presentationOfMap Φ η P).generators.I = P.generators.I := rfl

/-- The presentation pulled back along `Φ` has the relations of the given one. -/
theorem presentationOfMap_relations_I {M : _root_.SheafOfModules.{w} R₁}
    (P : (Φ.obj M).Presentation) :
    (presentationOfMap Φ η P).relations.I = P.relations.I := rfl

/-- **The presentation pulled back along `Φ` is finite when the given one is.** -/
theorem presentationOfMap_isFinite {M : _root_.SheafOfModules.{w} R₁}
    (P : (Φ.obj M).Presentation) [P.IsFinite] : (presentationOfMap Φ η P).IsFinite :=
  presentation_isFinite_of_finite _ (inferInstanceAs (Finite P.generators.I))
    (inferInstanceAs (Finite P.relations.I))

end Presentation

section OverMap

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) {X Y : C} (f : X ⟶ Y)

/-- The comparison of `SheafOfModules.overMap` is the identity: the restriction of `R.over Y`
along `Over.map f` is `R.over X` on the nose. -/
theorem pushforwardOverMapIso_inv_eq_id :
    (Sheaf.pushforwardOverMapIso R f).inv = 𝟙 (R.over X) := by
  ext : 2
  rfl

/-- `SheafOfModules.overMap` is restriction along `Over.map f` with the identity of the restricted
sheaf of rings as structure map. -/
def overMapIsoPushforwardId :
    _root_.SheafOfModules.overMap.{w} R f ≅
      _root_.SheafOfModules.pushforward.{w} (F := Over.map f)
        (𝟙 (((Over.map f).sheafPushforwardContinuous RingCat.{w} (J.over X) (J.over Y)).obj
          (R.over Y))) :=
  _root_.SheafOfModules.pushforwardCongr (pushforwardOverMapIso_inv_eq_id R f)

/-- **Restriction of sheaves of modules along `Over.map f` preserves colimits** at the universe
of the coefficient rings, over an essentially small slice: `Over.map f` is continuous and
cocontinuous, so restriction along it is a left adjoint
(`Stacks.SheafOfModules.restrictionAdjunction`). -/
theorem preservesColimitsOfSize_overMap [EssentiallySmall.{w} (Over X)]
    [LocallySmall.{w} (Over Y)] :
    PreservesColimitsOfSize.{w, w} (_root_.SheafOfModules.overMap.{w} R f) := by
  have h : PreservesColimitsOfSize.{w, w} (_root_.SheafOfModules.pushforward.{w}
      (F := Over.map f) (𝟙 (((Over.map f).sheafPushforwardContinuous RingCat.{w} (J.over X)
        (J.over Y)).obj (R.over Y)))) :=
    (restrictionAdjunction.{w} (Over.map f) (J.over X) (J.over Y)
      (R.over Y)).leftAdjoint_preservesColimits
  exact @preservesColimits_of_natIso _ _ _ _ _ _ (overMapIsoPushforwardId R f).symm h

end OverMap

end Stacks.SheafOfModules

end
