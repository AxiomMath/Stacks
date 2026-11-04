module

public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage

/-!
# Coherence and proper support along an isomorphism of algebraic spaces

The inverse image along an isomorphism `e : X₁ ≅ X₂` of algebraic spaces over `S` preserves and
reflects coherence and support proper over a base, the base being read on `X₁` along `e ≫ g`; and
proper support over `Y` depends on the target `Y` only up to isomorphism.

## Main results

* `AlgebraicGeometry.Space.isCoherent_modulePullback_iso_iff`: on locally Noetherian spaces, the
  inverse image along an isomorphism preserves and reflects coherence.
* `AlgebraicGeometry.Space.hasProperSupport_modulePullback_iso_iff`: the inverse image along an
  isomorphism preserves and reflects proper support.
* `AlgebraicGeometry.Space.hasProperSupport_comp_isIso_iff`: proper support over `Y` is unchanged
  by composing with an isomorphism `Y ⟶ Y'`.

## References

* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Proper support over `Y` along a morphism only depends on the morphism. -/
theorem hasProperSupport_congr_hom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {g g' : X ⟶ Y}
    (hgg : g = g') (hg : IsLocallyOfFiniteType B S hS g)
    (hg' : IsLocallyOfFiniteType B S hS g')
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u}) :
    HasProperSupport B S hS hX hY g hg F ↔ HasProperSupport B S hS hX hY g' hg' F := by
  subst hgg; rfl

/-- **Proper support over `Y` depends on `Y` only up to isomorphism.** -/
theorem hasProperSupport_comp_isIso_iff {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (g : X ⟶ Y) (ρ : Y ⟶ Y') [IsIso ρ]
    (hg : IsLocallyOfFiniteType B S hS g) (hgρ : IsLocallyOfFiniteType B S hS (g ≫ ρ))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u}) :
    HasProperSupport B S hS hX hY' (g ≫ ρ) hgρ F ↔ HasProperSupport B S hS hX hY g hg F := by
  refine exists_congr fun hcl ↦ ?_
  change IsProper B S hS (_ ≫ (g ≫ ρ)) ↔ IsProper B S hS (_ ≫ g)
  rw [← Category.assoc, isProper_comp_isIso_iff]

variable {B S hS}

/-- **The inverse image along an isomorphism of a module with proper support has proper
support**, read along the composite with the isomorphism. -/
theorem hasProperSupport_modulePullback_iso {X₁ X₂ Y : AlgebraicSpaces B S hS} (e : X₁ ⟶ X₂)
    [IsIso e] (g : X₂ ⟶ Y) (hg : IsLocallyOfFiniteType B S hS g.hom)
    (hg₁ : IsLocallyOfFiniteType B S hS (e ≫ g).hom) (M : Modules.{u, u} B S hS X₂.1 X₂.2)
    (hqc : M.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite M)
    (hM : HasProperSupport B S hS X₂.2 Y.2 g.hom hg ((SheafOfModules.toSheaf _).obj M)) :
    HasProperSupport B S hS X₁.2 Y.2 (e ≫ g).hom hg₁
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS e).obj M)) := by
  obtain ⟨_, hp⟩ := hM
  have sq : IsPullback e (e ≫ g) g (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨isClosed_supportOfSheaf_modulePullback B S hS e M hft,
    isProperOver_supportOfSheaf_modulePullback B S hS sq hg M hqc hft hp⟩

/-- **The inverse image along an isomorphism preserves and reflects proper support.** -/
theorem hasProperSupport_modulePullback_iso_iff {X₁ X₂ Y : AlgebraicSpaces B S hS} (e : X₁ ≅ X₂)
    (g : X₂ ⟶ Y) (hg : IsLocallyOfFiniteType B S hS g.hom)
    (hg₁ : IsLocallyOfFiniteType B S hS (e.hom ≫ g).hom) (M : Modules.{u, u} B S hS X₂.1 X₂.2)
    (hqc : M.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite M) :
    HasProperSupport B S hS X₁.2 Y.2 (e.hom ≫ g).hom hg₁
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS e.hom).obj M)) ↔
      HasProperSupport B S hS X₂.2 Y.2 g.hom hg ((SheafOfModules.toSheaf _).obj M) := by
  refine ⟨fun h ↦ ?_, hasProperSupport_modulePullback_iso e.hom g hg hg₁ M hqc hft⟩
  have h2 := hasProperSupport_modulePullback_iso e.symm.hom (e.hom ≫ g) hg₁
    (by simpa using hg) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS e.hom M hqc)
    (isFiniteTypeOnSite_modulePullback B S hS e.hom M hft) h
  rw [hasProperSupport_congr_hom B S hS X₂.2 Y.2
    (by simp : (e.symm.hom ≫ e.hom ≫ g).hom = g.hom) _ hg] at h2
  exact hasProperSupport_of_iso Y.2 g.hom hg
    (((modulePushforwardCoherence B S hS).modulePullbackEquivalence e).unitIso.app M).symm h2

/-- **The inverse image along an isomorphism preserves and reflects coherence**, on locally
Noetherian spaces. -/
theorem isCoherent_modulePullback_iso_iff {X₁ X₂ : AlgebraicSpaces B S hS} (e : X₁ ≅ X₂)
    [Fact (HasEtaleLocalProperty B S hS X₁.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [Fact (HasEtaleLocalProperty B S hS X₂.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, u} B S hS X₂.1 X₂.2) :
    IsCoherent B S hS X₁.1 X₁.2 ((modulePullback B S hS e.hom).obj M) ↔
      IsCoherent B S hS X₂.1 X₂.2 M :=
  ⟨fun h ↦ isCoherent_of_iso B S hS X₂.2
    (((modulePushforwardCoherence B S hS).modulePullbackEquivalence e).unitIso.app M).symm
    (isCoherent_modulePullback B S hS e.inv _ h), isCoherent_modulePullback B S hS e.hom M⟩

end AlgebraicGeometry.Space

end
