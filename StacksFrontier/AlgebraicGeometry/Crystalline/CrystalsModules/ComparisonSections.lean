module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal

/-!
# The comparison map carries a pullback to the `f`-map

Let `F` be a sheaf of `𝒪_{X/S}`-modules on a crystalline site of a global crystalline situation
and let `f : (U, T, δ) ⟶ (U', T', δ')` be a morphism of that site.  The comparison map
`c_f : f^* F_{T'} ⟶ F_T` of [Stacks, Tag 07IQ] is, by definition, the transpose of the `f`-map
`F_{T'} ⟶ f_* F_T` under the adjunction between pullback and pushforward of sheaves of modules.

This file records the consequence of that definition which the direction (2) ⇒ (1) of
[Stacks, Tag 07IT] needs: for **any** morphism `σ : N ⟶ F_{T'}` of sheaves of `𝒪_{T'}`-modules,
the pullback `f^* σ` followed by `c_f` transposes to `σ` followed by the `f`-map.  Taking `N` to
be the structure sheaf, so that `σ` is a global section of `F_{T'}`, this says that *the
comparison map carries the pullback of a global section to the restriction of that section along
`f`* — which is exactly what makes the pulled-back presentation of the source's argument

> Then by the crystal property of `F` we see that this pulls back to a presentation of
> `F_{T'}` for any morphism `f`

a presentation whose generators are the restrictions of one fixed family of sections of `F` over
`(U', T', δ')`, rather than an unrelated family for each `f`.  (The source's primes are the other
way round from this library's; see the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.CrystalPresentationPullback`.)

Everything below is naturality of the adjunction in its left variable, applied to
`Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf_eq_moduleComparisonSheaf` and
its small-site counterpart.  The statements are given for both of the sites [Stacks, Tag 07IT] is
stated for, a sheaf of modules on `Cris(X/S)` being in general not the restriction of one on
`CRIS(X/S)`.

## Main results

All names below are in the namespace `Crystalline.GlobalCrystallineSituation`.

* `Thickening.homEquiv_pullbackMap_comp_moduleComparisonSheaf` — **the pullback of a morphism into
  `F_{T'}` followed by the comparison map transposes to that morphism followed by the `f`-map**, on
  the big crystalline site.
* `Thickening.pullbackMap_comp_moduleComparisonSheaf` — the same read as a formula for the
  composite itself.
* `Thickening.pullbackMap_comp_moduleComparisonSheaf_congr` — consequently two morphisms into
  `F_{T'}` with the same `f`-map image have the same image under pullback-then-comparison: **the
  composite depends only on the restriction along `f`.**
* `SmallSite.CohomologyRestriction.homEquiv_pullbackMap_comp_moduleComparisonSheaf`,
  `...pullbackMap_comp_moduleComparisonSheaf` and
  `...pullbackMap_comp_moduleComparisonSheaf_congr` — the same three on the small crystalline
  site.

## What is not proved

No `@[stacks]` attribute is placed.  What is proved is a property of the comparison map of
[Stacks, Tag 07IQ] which that tag does not state, and no clause of [Stacks, Tag 07IT] is
delivered here: the direction (2) ⇒ (1) of that tag still needs the per-object presentations of the
`F_T` to be assembled into a single global presentation of `F` on the localised crystalline site,
which nothing here does.  The state of that direction, and the two steps it still costs, are set
out in the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.CrystalPresentationPullback`.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A B : Thickening S}

/-- **The pullback of a morphism into `F_{T'}` followed by the comparison map transposes to that
morphism followed by the `f`-map**, on the big crystalline site.  This is naturality of the
adjunction between pullback and pushforward in its left variable, together with the definition of
the comparison map as the transpose of the `f`-map. -/
theorem homEquiv_pullbackMap_comp_moduleComparisonSheaf (g : A ⟶ B)
    {N : SheafOfModules.{u} B.ringRestrictionSheaf} (σ : N ⟶ moduleRestrictionSheaf M B) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g)).homEquiv N
        (moduleRestrictionSheaf M A)
        ((SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).map σ ≫
          moduleComparisonSheaf M g) =
      σ ≫ moduleFMapSheaf M g := by
  rw [Adjunction.homEquiv_naturality_left, ← moduleFMapSheaf_eq_moduleComparisonSheaf]

/-- **The pullback of a morphism into `F_{T'}` followed by the comparison map is the transpose of
that morphism followed by the `f`-map**, on the big crystalline site: the formula of
`Crystalline.GlobalCrystallineSituation.Thickening.homEquiv_pullbackMap_comp_moduleComparisonSheaf`
read as a description of the composite. -/
theorem pullbackMap_comp_moduleComparisonSheaf (g : A ⟶ B)
    {N : SheafOfModules.{u} B.ringRestrictionSheaf} (σ : N ⟶ moduleRestrictionSheaf M B) :
    (SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).map σ ≫ moduleComparisonSheaf M g =
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g)).homEquiv N
        (moduleRestrictionSheaf M A)).symm (σ ≫ moduleFMapSheaf M g) := by
  rw [← homEquiv_pullbackMap_comp_moduleComparisonSheaf M g σ, Equiv.symm_apply_apply]

/-- **The pullback of a morphism into `F_{T'}` followed by the comparison map depends only on the
`f`-map image of that morphism**, on the big crystalline site.  For `N` the structure sheaf this
says that the generators of the presentation of `F_T` obtained by pulling back a presentation of
`F_{T'}` are determined by the restrictions along `f` of the generating sections of `F_{T'}`. -/
theorem pullbackMap_comp_moduleComparisonSheaf_congr (g : A ⟶ B)
    {N : SheafOfModules.{u} B.ringRestrictionSheaf} {σ τ : N ⟶ moduleRestrictionSheaf M B}
    (h : σ ≫ moduleFMapSheaf M g = τ ≫ moduleFMapSheaf M g) :
    (SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).map σ ≫
        moduleComparisonSheaf M g =
      (SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).map τ ≫
        moduleComparisonSheaf M g := by
  rw [pullbackMap_comp_moduleComparisonSheaf, pullbackMap_comp_moduleComparisonSheaf, h]

end Thickening

namespace SmallSite

namespace CohomologyRestriction

variable (M : SheafOfModules.{u} (structureSheaf S)) {A B : CrystallineThickening S}

/-- **The pullback of a morphism into `F_{T'}` followed by the comparison map transposes to that
morphism followed by the `f`-map**, on the small crystalline site.  [Stacks, Tag 07IT] is stated
for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and a sheaf of modules on `Cris(X/S)` is in
general not the restriction of one on `CRIS(X/S)`, so the statement is repeated here; the
`f`-map and the comparison map are formed over the very same ring map
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafFMap` of the underlying
morphism of the big site. -/
theorem homEquiv_pullbackMap_comp_moduleComparisonSheaf (g : A ⟶ B)
    {N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf B.obj)}
    (σ : N ⟶ moduleRestrictionSheaf M B) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv N (moduleRestrictionSheaf M A)
        ((SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map σ ≫
          moduleComparisonSheaf M g) =
      σ ≫ moduleFMapSheaf M g := by
  rw [Adjunction.homEquiv_naturality_left, ← moduleFMapSheaf_eq_moduleComparisonSheaf]

/-- **The pullback of a morphism into `F_{T'}` followed by the comparison map is the transpose of
that morphism followed by the `f`-map**, on the small crystalline site. -/
theorem pullbackMap_comp_moduleComparisonSheaf (g : A ⟶ B)
    {N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf B.obj)}
    (σ : N ⟶ moduleRestrictionSheaf M B) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map σ ≫
        moduleComparisonSheaf M g =
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv N
        (moduleRestrictionSheaf M A)).symm (σ ≫ moduleFMapSheaf M g) := by
  rw [← homEquiv_pullbackMap_comp_moduleComparisonSheaf M g σ, Equiv.symm_apply_apply]

/-- **The pullback of a morphism into `F_{T'}` followed by the comparison map depends only on the
`f`-map image of that morphism**, on the small crystalline site. -/
theorem pullbackMap_comp_moduleComparisonSheaf_congr (g : A ⟶ B)
    {N : SheafOfModules.{u} (Thickening.ringRestrictionSheaf B.obj)}
    {σ τ : N ⟶ moduleRestrictionSheaf M B}
    (h : σ ≫ moduleFMapSheaf M g = τ ≫ moduleFMapSheaf M g) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map σ ≫
        moduleComparisonSheaf M g =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map τ ≫
        moduleComparisonSheaf M g := by
  rw [pullbackMap_comp_moduleComparisonSheaf, pullbackMap_comp_moduleComparisonSheaf, h]

end CohomologyRestriction

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
