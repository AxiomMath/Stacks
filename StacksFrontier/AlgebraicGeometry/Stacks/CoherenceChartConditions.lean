module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSheaves
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHomSiteAgreement
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace

/-!
# The chart conditions of Stacks 0GR5, and the passage from all charts to one

Conditions (3) and (4) of Stacks 0GR5 on an `𝒪_𝒳`-module `ℱ` over a locally Noetherian
algebraic stack `𝒳` are the two conditions of that tag which test `ℱ` after restriction to the
small étale site of an algebraic space:

3. `ℱ` is quasi-coherent and for every 1-morphism `f : 𝒰 ⟶ 𝒳` with `𝒰` the algebraic stack of a
   locally Noetherian algebraic space `U` the restriction `f^*ℱ|_{U_étale}` is coherent;
4. `ℱ` is quasi-coherent and there are an algebraic space `U` and a 1-morphism `f : 𝒰 ⟶ 𝒳` which
   is locally of finite type, flat and surjective with `f^*ℱ|_{U_étale}` coherent.

Both are stated here, and the implication (3) ⟹ (4) is proved: a locally Noetherian algebraic
stack has an algebraic-space atlas which is smooth and surjective by **Stacks 04YF**, and a
smooth 1-morphism of algebraic stacks is flat and locally of finite type, so that atlas is a
1-morphism of the kind condition (4) asks for and condition (3) applies to it.

## Main definitions

* `AlgebraicGeometry.Stack.spaceChartRestriction`: the restriction `f^*ℱ|_{U_étale}` of a module
  on the big fppf site of `𝒳` along a 1-morphism from the algebraic stack of an algebraic space.
* `AlgebraicGeometry.Stack.IsCoherentOnNoetherianSpaceCharts`: condition (3) of Stacks 0GR5.
* `AlgebraicGeometry.Stack.IsCoherentOnSomeFlatSpaceChart`: condition (4) of Stacks 0GR5.

## Main results

* `AlgebraicGeometry.Stack.isCoherentOnSomeFlatSpaceChart_of_isCoherentOnNoetherianSpaceCharts`:
  **Stacks 0GR5**, the implication (3) ⟹ (4).

## Implementation notes

The restriction of the two conditions is the functor of Stacks 073M with a 1-morphism folded in,
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` of
`StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace`, and coherence of the
result is `AlgebraicGeometry.Space.IsCoherent` of **Stacks 07UA**.  Three matchings make the
composite go through, and none of them is an assumption:

* conditions (1) and (2) of Stacks 0GR5 are about a module on the *fppf* site of `𝒳` while the
  restriction is defined on the *étale* site, and the two are bridged by
  `AlgebraicGeometry.FibredSite.restrictSiteModules`, which changes neither the presheaf of
  modules nor the presheaf of rings: a sheaf for the inherited fppf topology is a sheaf for the
  inherited étale topology;
* the two spellings of the structure sheaf of `𝒳` — `AlgebraicGeometry.Stack`
  `.ringStructureSheafCore` at `B.topology`, which conditions (1) and (2) are stated over, and
  `AlgebraicGeometry.FibredSite.ringStructureSheafCore` at `AlgebraicGeometry.SiteKind.fppf`,
  which the restriction is stated over — are the same sheaf, because the fppf value of
  `AlgebraicGeometry.BigFppfSite.baseTopology` is `B.topology`;
* the presentation of the source of the 1-morphism as the category of elements of its
  representing presheaf, which Stacks 073M asks for, is the identity for
  `AlgebraicGeometry.Stack.algebraicSpaceStack`, so
  `CategoryTheory.StacksRepresentableCFG.EquivalenceOver.refl` supplies it.

The source quantifies condition (3) over morphisms `U ⟶ 𝒳` from an algebraic space; here the
source of the 1-morphism is the algebraic stack `AlgebraicGeometry.Stack.algebraicSpaceStack` of
an algebraic space, which is how Stacks 04YF and Stacks 0CIF compare a stack with an algebraic
space in this library, and it is the form `AlgebraicGeometry.Stack.HasPropertyOnSomeSpaceAtlas`
takes.  Local Noetherianity of the algebraic space is the étale-local property of **Stacks 03E6**
at `AlgebraicGeometry.IsLocallyNoetherian`, which is what Stacks 04YF produces from local
Noetherianity of `𝒳`.

The module universe `m` is free, as it is for conditions (1) and (2).

The implication (2) ⟹ (1) is in `StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditions`, and
the implications (1) ⟹ (3) and (4) ⟹ (2), together with the equivalence of the four conditions,
are in `StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsEquivalence`.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The restriction `f^*ℱ|_{U_étale}` to the small étale site of an algebraic space `U` of the
inverse image of a module `ℱ` on the big fppf site of an algebraic stack `𝒳` along a 1-morphism
`f` from the algebraic stack of `U`.

This is `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`, the functor of Stacks 073M
with the 1-morphism folded in, applied to `ℱ` read as a sheaf of modules on the étale site of
`𝒳` by `AlgebraicGeometry.FibredSite.restrictSiteModules`.  The presentation of the source of
`f` that Stacks 073M asks for is the identity, since the algebraic stack of an algebraic space
*is* the category of elements of its representing presheaf. -/
noncomputable abbrev spaceChartRestriction (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :
    Space.Modules.{u, m} B S hS F hF :=
  Space.etaleRestrictedModuleInverseImage (U := ⟨F, hF⟩) B S hS
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, t} B S hS F hF).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)
    (FibredSite.restrictSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale M)

/-- **Condition (3) of Stacks 0GR5.**  A module on the big fppf site of an algebraic stack `𝒳` is
quasi-coherent and its restriction `f^*ℱ|_{U_étale}` along every 1-morphism from the algebraic
stack of a locally Noetherian algebraic space `U` is coherent in the sense of Stacks 07UA.

Local Noetherianity of `U` is the étale-local property of Stacks 03E6 at
`AlgebraicGeometry.IsLocallyNoetherian`. -/
abbrev IsCoherentOnNoetherianSpaceCharts (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) : Prop :=
  M.IsQuasicoherentOnSite ∧
    ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
      (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳),
      Space.HasEtaleLocalProperty B S hS F (fun Z : Scheme.{u} ↦ IsLocallyNoetherian Z) →
        Space.IsCoherent B S hS F hF (spaceChartRestriction B S hS 𝒳 F hF f M)

/-- **Condition (4) of Stacks 0GR5.**  A module on the big fppf site of an algebraic stack `𝒳` is
quasi-coherent and there is a 1-morphism `f` to `𝒳` from the algebraic stack of an algebraic
space `U` which is locally of finite type, flat and surjective and along which the restriction
`f^*ℱ|_{U_étale}` is coherent in the sense of Stacks 07UA. -/
abbrev IsCoherentOnSomeFlatSpaceChart (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) : Prop :=
  M.IsQuasicoherentOnSite ∧
    ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
      (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳),
      AlgebraicStacks.IsLocallyOfFiniteType B S hS f ∧ AlgebraicStacks.IsFlat B S hS f ∧
        IsSurjective B S hS f ∧
        Space.IsCoherent B S hS F hF (spaceChartRestriction B S hS 𝒳 F hF f M)

/-- **Stacks 0GR5, the implication (3) ⟹ (4).**  Let `𝒳` be a locally Noetherian algebraic stack
and `ℱ` a module on its big fppf site which is quasi-coherent and whose restriction to the small
étale site of every locally Noetherian algebraic-space chart is coherent.  Then there is one
chart which is locally of finite type, flat and surjective and on which the restriction is
coherent.

The chart is produced by **Stacks 04YF**: local Noetherianity of `𝒳` in the form of
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` gives, by
`AlgebraicGeometry.Stack.exists_scheme_atlas_iff_exists_space_atlas`, a smooth surjective
1-morphism from the algebraic stack of an algebraic space with the étale-local property of local
Noetherianity.  A smooth 1-morphism of algebraic stacks is flat by
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth` and locally of finite type by
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth`, so that chart is of
the kind condition (4) asks for, and condition (3) applied to it supplies the coherence. -/
@[stacks 0GR5 "condition (3) implies condition (4)"]
theorem isCoherentOnSomeFlatSpaceChart_of_isCoherentOnNoetherianSpaceCharts
    (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : IsCoherentOnNoetherianSpaceCharts.{u, m, t} B S hS 𝒳 M) :
    IsCoherentOnSomeFlatSpaceChart.{u, m, t} B S hS 𝒳 M := by
  have : ObjectProperty.IsLocal (fun Z : Scheme.{u} ↦ IsLocallyNoetherian Z)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  obtain ⟨F, hF, f, hfSurj, hfSmooth, hFN⟩ :=
    (exists_scheme_atlas_iff_exists_space_atlas.{u, t} B S hS
      (fun Z : Scheme.{u} ↦ IsLocallyNoetherian Z) 𝒳).mp h𝒳
  exact ⟨hM.1, F, hF, f,
    AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfSmooth,
    AlgebraicStacks.isFlat_of_isSmooth B S hS f hfSmooth, hfSurj, hM.2 F hF f hFN⟩

end AlgebraicGeometry.Stack

end
