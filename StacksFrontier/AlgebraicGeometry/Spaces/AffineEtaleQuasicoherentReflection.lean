module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleQuasicoherentDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Quasi-coherence of an `𝒪_F`-module is detected on the affine étale charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtalePushforward`:
  an `𝒪_F`-module whose restriction to the affine étale charts is quasi-coherent is itself
  quasi-coherent, for module sections in any universe containing that of the schemes.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModulePushforward_iff`: restriction
  of `𝒪_F`-modules to the affine étale charts both preserves and reflects quasi-coherence.
* `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleRestrictionEquivalence`: hence
  categories (1) and (2) of Stacks 0H06, `D_QCoh(𝒪_F)` and `D_QCoh(F_{affine,étale}, 𝒪_F)`, are
  equivalent through derived restriction, at the universe of the schemes.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleModulePushforward`: restriction of `𝒪_F`-modules to the
  affine étale charts, for module sections in any universe.

## The argument

The restriction `N` is quasi-coherent on the affine étale site, whose structure sheaf is the
presheaf of chart rings `AlgebraicGeometry.Space.affineEtaleChartRings`. After its sections are
raised to the universe of the charts, Stacks 0H04 for the chart rings
(`AlgebraicGeometry.Space.isIso_restrictionBaseChange_affineEtaleChart_of_isQuasicoherentOnSite`)
makes the base change comparisons of `N` invertible; those are the base change comparisons of
the module itself along the morphisms of affine charts, so the module is cartesian on affine
charts, and Descent, Proposition 03DX (2)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse`)
makes it quasi-coherent.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Restriction of `𝒪_F`-modules to the affine étale charts**, for module sections in any
universe: restriction along the inclusion of the affine charts, over the restricted structure
sheaf `AlgebraicGeometry.Space.affineEtaleRingRestriction`. At the universe of the schemes it is
`AlgebraicGeometry.Space.affineEtaleModuleRestriction`, by definition. -/
noncomputable def affineEtaleModulePushforward :
    Modules.{u, m} B S hS F hF ⥤ SheafOfModules.{m} (affineEtaleRingRestriction B S hS F hF) := by
  have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  exact SheafOfModules.pushforward (F := AffineEtale.inclusion B S hS F)
    (J := AffineEtale.topology B S hS F) (K := SmallEtale.topology B S hS F)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
    (𝟙 (affineEtaleRingRestriction B S hS F hF))

/-- At the universe of the schemes, restriction of modules to the affine charts is
`AlgebraicGeometry.Space.affineEtaleModuleRestriction`. -/
theorem affineEtaleModulePushforward_eq :
    affineEtaleModulePushforward.{u, u} B S hS F hF = affineEtaleModuleRestriction B S hS F hF :=
  rfl

/-- **Restriction to the affine charts reflects quasi-coherence.** An `𝒪_F`-module whose
restriction to the affine étale charts, over the restricted structure sheaf, is quasi-coherent is
quasi-coherent; the module sections lie in any universe containing that of the schemes. -/
theorem isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtalePushforward
    (G : Modules.{u, max u m} B S hS F hF)
    (hG : ((affineEtaleModulePushforward.{u, max u m} B S hS F hF).obj G).IsQuasicoherentOnSite) :
    G.IsQuasicoherentOnSite := by
  have hds : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  refine isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse G ?_
  intro U V hU hV f
  have hRing : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat) :=
    (affineEtaleRingRestriction B S hS F hF).property
  -- the restriction of `G`, read over the chart rings
  let N : SheafOfModules.{max u m}
      (⟨affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf (AffineEtale.topology B S hS F) RingCat.{u}) :=
    (affineEtaleModulePushforward.{u, max u m} B S hS F hF).obj G
  -- raise its sections to the universe of the charts
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation (M := N) hG
  -- Stacks 0H04 for the chart rings
  have h₃ := isIso_restrictionBaseChange_affineEtaleChart_of_isQuasicoherentOnSite.{u, max u m}
    B S hS F hRing _ h₂
    ((AffineEtale.inclusion B S hS F).preimage
      (X := (⟨V, hV⟩ : AffineEtale B S hS F)) (Y := ⟨U, hU⟩) f)
  -- descend the universe lift of the sections
  have h₄ := bijective_restrictionBaseChange_of_uliftForPresentation.{u + 1, u, u, max u m}
    (affineEtaleChartRings B S hS F) hRing N _ h₃
  -- the comparison of the restriction is the comparison of `G`
  have h₅ := bijective_restrictionBaseChange_of_restriction.{u, m}
    (J := SmallEtale.topology B S hS F) (K := AffineEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) (structurePresheaf B S hS F) _ G _ h₄
  rw [(AffineEtale.inclusion B S hS F).map_preimage] at h₅
  rw [bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange.{u, m} B S hS F hF G f,
    ConcreteCategory.isIso_iff_bijective]
  exact h₅

/-- **Restriction to the affine charts preserves quasi-coherence**, for module sections in any
universe: Stacks 03DM for clause (6) of Stacks 03DL along the dense subsite inclusion of
Stacks 04JS (`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`). -/
theorem isQuasicoherentOnSite_affineEtaleModulePushforward (G : Modules.{u, m} B S hS F hF)
    (hG : G.IsQuasicoherentOnSite) :
    ((affineEtaleModulePushforward.{u, m} B S hS F hF).obj G).IsQuasicoherentOnSite := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have hover : ∀ X : AffineEtale B S hS F,
      (Over.post (X := X) (AffineEtale.inclusion B S hS F)).IsContinuous
        ((AffineEtale.topology B S hS F).over X)
        ((SmallEtale.topology B S hS F).over ((AffineEtale.inclusion B S hS F).obj X)) :=
    fun X ↦
      have : (Over.post (X := X) (AffineEtale.inclusion B S hS F)).IsDenseSubsite
          ((AffineEtale.topology B S hS F).over X)
          ((SmallEtale.topology B S hS F).over ((AffineEtale.inclusion B S hS F).obj X)) :=
        Stacks.Sites.overPost_isDenseSubsite (AffineEtale.inclusion B S hS F) X
      inferInstance
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := SmallEtale.topology B S hS F) (K := AffineEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) G hG

/-- **Restriction to the affine charts preserves and reflects quasi-coherence**, for module
sections in any universe containing that of the schemes. -/
theorem isQuasicoherentOnSite_affineEtaleModulePushforward_iff
    (G : Modules.{u, max u m} B S hS F hF) :
    ((affineEtaleModulePushforward.{u, max u m} B S hS F hF).obj G).IsQuasicoherentOnSite ↔
      G.IsQuasicoherentOnSite :=
  ⟨isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtalePushforward B S hS F hF G,
    isQuasicoherentOnSite_affineEtaleModulePushforward B S hS F hF G⟩

/-- **An `𝒪_F`-module whose restriction to the affine charts is quasi-coherent is
quasi-coherent**, at the universe of the schemes and in terms of
`AlgebraicGeometry.Space.affineEtaleModuleRestriction`: the converse of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModuleRestriction`. -/
theorem isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtaleModuleRestriction
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (hM : ((affineEtaleModuleRestriction B S hS F hF).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtalePushforward.{u, u} B S hS F hF M hM

/-- **Categories (1) and (2) of Stacks 0H06 are equivalent, at the universe of the schemes**:
restriction to the affine étale charts is an exact equivalence

`D_QCoh(𝒪_F) ⟶ D_QCoh(F_{affine,étale}, 𝒪_F)`

for module sections in the universe of the schemes. It is
`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleEquivalence` with its hypothesis
discharged by the reflection of quasi-coherence under restriction to the affine charts,
`isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtaleModuleRestriction`, so it is the
restriction of the derived restriction functor
`AlgebraicGeometry.Space.affineEtaleDerivedRestrictionEquivalence`.  It is not registered under
Stacks 0H06: the tag is carried by `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChain`
and its exactness companions, at the module universe of the chain. -/
noncomputable def quasicoherentDerivedAffineEtaleRestrictionEquivalence :
    QuasicoherentDerivedCategory.{u, u} B S hS F hF ≌
      affineEtaleQuasicoherentDerivedCategory B S hS F hF :=
  quasicoherentDerivedAffineEtaleEquivalence B S hS F hF
    (isQuasicoherentOnSite_of_isQuasicoherentOnSite_affineEtaleModuleRestriction B S hS F hF)

end AlgebraicGeometry.Space

end
