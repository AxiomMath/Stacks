module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePresentationRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetNormalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift

/-!
# Restricting a presentation over a slice to a site with a final object, above the rings

`Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal` restricts a global
presentation of `M` over a slice `C/y` (Stacks 03DE (6)) along a continuous and cocontinuous
functor `σ : C' ⥤ C` from a site with a final object `e` and an arrow `σ(e) ⟶ y`, at the universe
of the coefficient rings. This file proves it for modules whose sections lie in the universe
`max u v r z` containing the sites, above the universe `r` of the rings, the form in which
quasi-coherence is stated there (`SheafOfModules.HasGlobalPresentation`): the conclusion is a
presentation by global sections of the restricted module read over the structure sheaf raised to
that universe (`Stacks.Modules.sheafRingULiftUp`), where a presentation by global sections
(`SheafOfModules.IsPresentedByGlobalSections`) is stated at a single universe.

## Main results

* `Stacks.SheafOfModules.isPresentedByGlobalSections_map_pushforward_of_isTerminal`: if `M.over y`
  has a global presentation, then the restriction of `M` along `σ`, read through a
  colimit-preserving functor `U'` carrying the universe lift of the structure sheaf to a structure
  sheaf, is presented by global sections.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)

universe r z u₁ v₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}} (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))
  {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
  {𝒪' : C'ᵒᵖ ⥤ CommRingCat.{r}} (h𝒪' : Presheaf.IsSheaf J' (structureRingPresheaf 𝒪'))
  {e : C'} (he : IsTerminal e) (σ : C' ⥤ C) [σ.IsContinuous J' J] [σ.IsCocontinuous J' J]
  (y : C) (φ : σ.obj e ⟶ y)
  (χ : structureSheaf 𝒪' h𝒪' ⟶
    (σ.sheafPushforwardContinuous RingCat.{r} J' J).obj (structureSheaf 𝒪 h𝒪)) (hχ : IsIso χ)

include hset he φ hχ in
/-- **A global presentation over a slice restricts, along a continuous and cocontinuous functor
from a site with a final object into the site, to a presentation by global sections over rings in
the universe of the sections**, for modules with sections in the universe `max u₁ v₁ r z`
containing the sites: read through a colimit-preserving functor `U'` carrying the universe lift of
the structure sheaf to a structure sheaf. -/
theorem isPresentedByGlobalSections_map_pushforward_of_isTerminal
    {R'' : Sheaf J' RingCat.{max u₁ v₁ r z}}
    (U' : _root_.SheafOfModules.{max u₁ v₁ r z} (structureSheaf 𝒪' h𝒪') ⥤
      _root_.SheafOfModules.{max u₁ v₁ r z} R'')
    (hU' : PreservesColimitsOfSize.{max u₁ v₁ r z, max u₁ v₁ r z} U')
    (hU'₀ : U'.PreservesZeroMorphisms)
    (ηU : U'.obj (_root_.SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ z}
      (_root_.SheafOfModules.unit (structureSheaf 𝒪' h𝒪'))) ≅ _root_.SheafOfModules.unit R'')
    (M : _root_.SheafOfModules.{max u₁ v₁ r z} (structureSheaf 𝒪 h𝒪))
    (hM : (M.over y).HasGlobalPresentation) :
    (U'.obj ((_root_.SheafOfModules.pushforward.{max u₁ v₁ r z} χ).obj
      M)).IsPresentedByGlobalSections := by
  have := hχ
  have := isContinuous_equivalenceOfIsTerminal_inverse J' he
  have := isCocontinuous_equivalenceOfIsTerminal_inverse J' he
  have := Functor.isContinuous_overPost J' J σ e
  let v : C' ⥤ Over y := (Over.equivalenceOfIsTerminal he).inverse ⋙ Over.post σ ⋙ Over.map φ
  have : v.IsContinuous J' (J.over y) := Functor.isContinuous_comp _ _ _ (J'.over e) _
  have : (Over.post σ ⋙ Over.map φ).IsCocontinuous (J'.over e) (J.over y) :=
    CategoryTheory.isCocontinuous_comp (L := J.over y) _ _ (J'.over e) (J.over (σ.obj e))
  have : v.IsCocontinuous J' (J.over y) :=
    CategoryTheory.isCocontinuous_comp (L := J.over y) _ _ J' (J'.over e)
  let ψ : structureSheaf 𝒪' h𝒪' ⟶
      (v.sheafPushforwardContinuous RingCat.{r} J' (J.over y)).obj ((structureSheaf 𝒪 h𝒪).over y) :=
    χ
  have : IsIso ψ := inferInstanceAs (IsIso χ)
  have : HasSheafify J' AddCommGrpCat.{max u₁ v₁ r z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u₁ v₁ r z, v₁, u₁} J'
  have : J'.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ r z} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u₁ v₁ r z, u₁, v₁}
      J'
  have : HasSheafify (J.over y) AddCommGrpCat.{max u₁ v₁ r z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u₁ v₁ r z, v₁, max u₁ v₁} (J.over y)
  have : (J.over y).WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ r z} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u₁ v₁ r z,
      max u₁ v₁, v₁} (J.over y)
  have h₁ := (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) y).property
  have h₂ := (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) y).property
  let E := Stacks.Modules.sheafRingULiftEquiv.{max u₁ v₁, v₁, r, z, max u₁ v₁ r z}
    (J := J.over y) (𝒪 := (Over.forget y).op ⋙ 𝒪) h₁ h₂
  let Uy := E.inverse
  let Dy := E.functor
  have h₀ : (Uy.obj (M.over y)).IsPresentedByGlobalSections :=
    _root_.SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal
      Over.mkIdTerminal
      (Stacks.Modules.hasGlobalPresentation_sheafRingULiftUp.{max u₁ v₁, v₁, r, z}
        (J := J.over y) (𝒪 := (Over.forget y).op ⋙ 𝒪) h₁ h₂ (M.over y) hM)
  let G := (Dy ⋙ _root_.SheafOfModules.pushforward.{max u₁ v₁ r z} ψ) ⋙ U'
  have hψ : PreservesColimitsOfSize.{max u₁ v₁ r z, max u₁ v₁ r z}
      (_root_.SheafOfModules.pushforward.{max u₁ v₁ r z} ψ) :=
    pushforward_preservesColimits.{u₁, v₁, max u₁ v₁ r z, max u₁ v₁, v₁, r} v ψ
  have hDy : PreservesColimitsOfSize.{max u₁ v₁ r z, max u₁ v₁ r z} Dy :=
    E.toAdjunction
      |>.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{max u₁ v₁ r z, max u₁ v₁ r z} G :=
    @comp_preservesColimits _ _ _ _ _ _ (Dy ⋙ _root_.SheafOfModules.pushforward.{max u₁ v₁ r z} ψ)
      U' (@comp_preservesColimits _ _ _ _ _ _ Dy _ hDy hψ) hU'
  have : G.PreservesZeroMorphisms := by
    have : (Dy ⋙ _root_.SheafOfModules.pushforward.{max u₁ v₁ r z} ψ).PreservesZeroMorphisms :=
      ⟨fun _ _ => rfl⟩
    exact Functor.preservesZeroMorphisms_comp _ _
  have : IsIso ((_root_.SheafOfModules.toSheaf.{r} (structureSheaf 𝒪' h𝒪')).map
      (_root_.SheafOfModules.unitToPushforwardObjUnit ψ)) :=
    isIso_toSheaf_map_unitToPushforwardObjUnit ψ
  have : IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit ψ) :=
    isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf.{r} (structureSheaf 𝒪' h𝒪'))
  let η₁ : (_root_.SheafOfModules.pushforward.{max u₁ v₁ r z} ψ).obj
      (Dy.obj (_root_.SheafOfModules.unit _)) ≅
      _root_.SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ z}
        ((_root_.SheafOfModules.pushforward.{r} ψ).obj (_root_.SheafOfModules.unit _)) :=
    (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y f; ext x; rfl))
  let η : G.obj (_root_.SheafOfModules.unit _) ≅ _root_.SheafOfModules.unit _ :=
    U'.mapIso (η₁ ≪≫
      (_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, v₁, r, r, max u₁ v₁ z}).mapIso
        (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit ψ)).symm) ≪≫ ηU
  have hDU : Dy.obj (Uy.obj (M.over y)) = M.over y :=
    rfl
  let ρ : G.obj (Uy.obj (M.over y)) ≅
      U'.obj ((_root_.SheafOfModules.pushforward.{max u₁ v₁ r z} χ).obj M) :=
    U'.mapIso ((_root_.SheafOfModules.pushforward.{max u₁ v₁ r z} ψ).mapIso (eqToIso hDU))
  exact Stacks.Sheaves.LocalizedPullback.isPresentedByGlobalSections_map G η ρ h₀

end Stacks.SheafOfModules
