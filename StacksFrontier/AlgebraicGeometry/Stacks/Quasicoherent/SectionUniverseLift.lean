module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.CategoryTheory.Sites.Modules.MixedUniverseTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Changing the universes commutes with sheafification of presheaves of modules

Let `α : R₀ ⟶ R.obj` be a locally bijective morphism from a presheaf of rings to a sheaf of
rings, so that sheaves of `R`-modules are the sheafification of presheaves of `R₀`-modules.
Raising the universe of the sections commutes with that sheafification: the sheafification of
the universe lift of a presheaf of modules is the universe lift of the sheafification. Likewise,
lowering the universe of the coefficient rings commutes with sheafification. A global
presentation, and hence quasi-coherence, of a sheaf of modules is carried to the universe lift of
its sections.

## Main definitions

* `PresheafOfModules.uliftSheafificationUnit`: the universe lift of the sheafification unit of a
  presheaf of modules, read as a morphism into the universe lift of the sheafification.
* `PresheafOfModules.sheafificationUliftObjIso`: raising the universe of the sections commutes
  with sheafification of presheaves of modules.
* `Stacks.Modules.sheafificationRingULiftDownIso`: lowering the universe of the coefficient
  rings commutes with sheafification of presheaves of modules.

## Main results

* `SheafOfModules.uliftForPresentation_val` and
  `SheafOfModules.restrictScalars_uliftForPresentation`: raising the universe of the sections of
  a sheaf of modules is the presheaf-level universe lift of its sections, and commutes with
  restriction of scalars.
* `PresheafOfModules.toPresheaf_map_uliftSheafificationUnit`: on sections, the universe lift of
  the sheafification unit is the sheafification unit whiskered by the universe lift of abelian
  groups.
* `PresheafOfModules.w_uliftSheafificationUnit`: the universe lift of the sheafification unit is
  inverted by sheafification.
* `SheafOfModules.hasGlobalPresentation_uliftForPresentation` and
  `SheafOfModules.isQuasicoherentOnSite_uliftForPresentation`: a global presentation, resp.
  quasi-coherence, of a sheaf of modules is one of the universe lift of its sections.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- Raising the universe of the sections of a sheaf of modules is the presheaf-level universe
lift of its underlying presheaf of modules. -/
theorem uliftForPresentation_val (M : SheafOfModules.{m} R) :
    (uliftForPresentation.{u, v, r, m, t} M).val = M.val.uliftSections.{t} :=
  rfl

/-- Raising the universe of the sections of a sheaf of modules commutes with restriction of
scalars along a morphism of coefficient rings. -/
theorem restrictScalars_uliftForPresentation {R₀ : Cᵒᵖ ⥤ RingCat.{r}} (α : R₀ ⟶ R.obj)
    (M : SheafOfModules.{m} R) :
    (PresheafOfModules.restrictScalars α).obj
        ((forget R).obj (uliftForPresentation.{u, v, r, m, t} M)) =
      ((PresheafOfModules.restrictScalars α).obj ((forget R).obj M)).uliftSections.{t} :=
  rfl

end SheafOfModules

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{r}} {R : Sheaf J RingCat.{r}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

section

/-- The universe lift of the sheafification unit of a presheaf of modules, read as a morphism
from the universe lift of the presheaf into the universe lift of the sections of its
sheafification. -/
noncomputable def uliftSheafificationUnit (M : PresheafOfModules.{m} R₀) :
    M.uliftSections.{t} ⟶ (restrictScalars α).obj ((SheafOfModules.forget R).obj
      (SheafOfModules.uliftForPresentation.{u, v, r, m, t} ((sheafification.{m} α).obj M))) :=
  ulift.{t}.map ((sheafificationAdjunction.{m} α).unit.app M)

/-- On sections, the universe lift of the sheafification unit of a presheaf of modules is the
sheafification unit of its presheaf of abelian groups, whiskered by the universe lift of abelian
groups. -/
theorem toPresheaf_map_uliftSheafificationUnit (M : PresheafOfModules.{m} R₀) :
    (toPresheaf R₀).map (uliftSheafificationUnit.{u, v, r, m, t} α M) =
      Functor.whiskerRight (CategoryTheory.toSheafify J M.presheaf)
        AddCommGrpCat.uliftFunctor.{t} :=
  rfl

end

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}]

/-- The universe lift of the sheafification unit of a presheaf of modules is inverted by
sheafification. -/
theorem w_uliftSheafificationUnit (M : PresheafOfModules.{m} R₀) :
    (J.W.inverseImage (toPresheaf R₀)) (uliftSheafificationUnit.{u, v, r, m, t} α M) := by
  have h₁ : Presheaf.IsLocallyInjective J
      ((toPresheaf R₀).map (uliftSheafificationUnit.{u, v, r, m, t} α M)) := by
    rw [toPresheaf_map_uliftSheafificationUnit]
    exact Presheaf.isLocallyInjective_whiskerRight_uliftFunctor J _
  have h₂ : Presheaf.IsLocallySurjective J
      ((toPresheaf R₀).map (uliftSheafificationUnit.{u, v, r, m, t} α M)) := by
    rw [toPresheaf_map_uliftSheafificationUnit]
    exact Presheaf.isLocallySurjective_whiskerRight_uliftFunctor J _
  exact GrothendieckTopology.W_of_isLocallyBijective J _

/-- Raising the universe of the sections commutes with sheafification of presheaves of modules:
the sheafification of the universe lift of `M` is the universe lift of the sheafification of
`M`. -/
noncomputable def sheafificationUliftObjIso [HasWeakSheafify J AddCommGrpCat.{max t m}]
    (M : PresheafOfModules.{m} R₀) :
    (sheafification.{max t m} α).obj M.uliftSections.{t} ≅
      SheafOfModules.uliftForPresentation.{u, v, r, m, t} ((sheafification.{m} α).obj M) :=
  Localization.isoOfHom (sheafification.{max t m} α) (J.W.inverseImage (toPresheaf R₀))
      (uliftSheafificationUnit.{u, v, r, m, t} α M) (w_uliftSheafificationUnit α M) ≪≫
    (asIso (sheafificationAdjunction.{max t m} α).counit).app _

end

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A global presentation of a sheaf of modules gives one of the universe lift of its sections. -/
theorem hasGlobalPresentation_uliftForPresentation {M : SheafOfModules.{m} R}
    (h : M.HasGlobalPresentation) :
    (uliftForPresentation.{u, v, r, m, max u v r} M).HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  let γ : uliftForPresentation.{u, v, r, r, max u v m} (unit R) ≅
      uliftForPresentation.{u, v, r, r, max u v r m} (unit R) :=
    (uliftForPresentationSelfIso'.{u, v, r, m, max u v r m}
      (uliftForPresentation.{u, v, r, r, max u v m} (unit R))).symm ≪≫
        uliftForPresentationCompIso.{u, v, r, r, max u v m, max u v r m} (unit R)
  let δ : uliftForPresentation.{u, v, r, max u v r m, max u v r}
        (uliftForPresentation.{u, v, r, m, max u v r} M) ≅
      uliftForPresentation.{u, v, r, m, max u v r} M :=
    uliftForPresentationSelfIso'.{u, v, r, m, max u v r} _
  refine ⟨I, K, P, Q, fun i ↦ γ.inv ≫ ι i, fun k ↦ γ.inv ≫ κ k,
    ⟨isColimit_cofan_comp_iso γ.symm ι hP⟩, ⟨isColimit_cofan_comp_iso γ.symm κ hQ⟩,
    a, b ≫ δ.inv, ?_, ⟨?_⟩⟩
  · rw [← Category.assoc, hab, zero_comp]
  · exact hb.ofIsoColimit (Cofork.ext δ.symm rfl)

/-- If a sheaf of modules is quasi-coherent, so is the universe lift of its sections. -/
theorem isQuasicoherentOnSite_uliftForPresentation {M : SheafOfModules.{m} R}
    (h : M.IsQuasicoherentOnSite) :
    (uliftForPresentation.{u, v, r, m, max u v r} M).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasGlobalPresentation U
    exact ⟨I, V, f, hcover,
      fun i ↦ hasGlobalPresentation_uliftForPresentation.{max u v, v, r, m} (hpres i)⟩

end SheafOfModules

namespace Stacks.Modules

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}}
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

universe z

/-- The sheafification unit of a presheaf of modules over the universe lift of the coefficient
rings, read as a morphism of presheaves of modules over the original coefficient rings. -/
noncomputable def sheafificationRingULiftDownUnit
    (P : PresheafOfModules.{m} (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪))) :
    (presheafRingULiftDown.{u, v, r, z, m} 𝒪).obj P ⟶
      (PresheafOfModules.restrictScalars
            (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj
        ((SheafOfModules.forget (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).obj
          ((sheafRingULiftDown.{u, v, r, z, m} h𝒪 hset).obj
            ((PresheafOfModules.sheafification.{m}
              (𝟙 (structureSheafRingULift.{u, v, r, z} hset).obj)).obj P))) :=
  (presheafRingULiftDown.{u, v, r, z, m} 𝒪).map
    ((PresheafOfModules.sheafificationAdjunction.{m}
      (𝟙 (structureSheafRingULift.{u, v, r, z} hset).obj)).unit.app P)

/-- On sections, lowering the universe of the coefficient rings leaves the sheafification unit
of a presheaf of modules unchanged. -/
theorem toPresheaf_map_sheafificationRingULiftDownUnit
    (P : PresheafOfModules.{m} (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪))) :
    (PresheafOfModules.toPresheaf
          (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map
        (sheafificationRingULiftDownUnit.{u, v, r, m, z} h𝒪 hset P) =
      CategoryTheory.toSheafify J P.presheaf :=
  rfl

/-- Lowering the universe of the coefficient rings commutes with sheafification of presheaves
of modules. -/
noncomputable def sheafificationRingULiftDownIso
    (P : PresheafOfModules.{m} (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪))) :
    (PresheafOfModules.sheafification.{m}
          (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj
        ((presheafRingULiftDown.{u, v, r, z, m} 𝒪).obj P) ≅
      (sheafRingULiftDown.{u, v, r, z, m} h𝒪 hset).obj
        ((PresheafOfModules.sheafification.{m}
          (𝟙 (structureSheafRingULift.{u, v, r, z} hset).obj)).obj P) :=
  Localization.isoOfHom
      (PresheafOfModules.sheafification.{m}
            (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj))
      (J.W.inverseImage (PresheafOfModules.toPresheaf
            (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj))
      (sheafificationRingULiftDownUnit.{u, v, r, m, z} h𝒪 hset P)
      (by
        change J.W ((PresheafOfModules.toPresheaf
              (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map
          (sheafificationRingULiftDownUnit.{u, v, r, m, z} h𝒪 hset P))
        rw [toPresheaf_map_sheafificationRingULiftDownUnit]
        exact J.W_toSheafify _) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction.{m}
      (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).counit).app _

end Stacks.Modules

end
