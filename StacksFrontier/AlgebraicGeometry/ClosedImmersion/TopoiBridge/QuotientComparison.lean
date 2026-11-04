module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientComparison.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The adjunction unit along a closed immersion, and the ideal-power quotient

Let `i : Z ⟶ X` be a closed immersion of schemes. Pushforward of sheaves of modules along `i` is
fully faithful (`Stacks.ToposBridge.fullyFaithfulSchemeModulesPushforward`), so the counit of the
pullback–pushforward adjunction is an isomorphism; by the triangle identity the unit is then an
isomorphism at every object of the essential image of `i_*`, and by naturality at every object
isomorphic to one.

This is what the ideal-power quotient comparison of Stacks 0EL1 needs. For a quasi-coherent ideal
sheaf `I` on `X`, a natural number `n` and a sheaf of modules `F` on `X`, write
`ι = (I ^ n).subschemeι`. The canonical comparison
`Stacks.Algebraization.quotientSubschemeComparisonMap`
`F / I ^ n F ⟶ ι_* ι^* F` is an isomorphism as soon as the unit is an isomorphism at
`F / I ^ n F`: the unit at `F / I ^ n F` factors the comparison against the image of the quotient
projection under `ι_* ι^*`, and that image is an isomorphism because `ι^*` already inverts the
projection (`Stacks.Algebraization.isIso_pullback_map_cokernel_π`).

So the remaining obligation of Stacks 0EL1 is exactly that `F / I ^ n F` lies in the essential
image of `i_*`, which is the essential-image half of Stacks 08KS.

**That half is proved for a closed immersion of schemes**: it is
`Stacks.ClosedImmersion.pushforward_essImage_iff` and its consumer form
`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero` in
`StacksFrontier/AlgebraicGeometry/ClosedPushforward/Basic.lean`. The obligation is therefore
discharged downstream, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/SectionsComplete.lean`:
`Stacks.Algebraization.isIso_idealQuotientPushforwardMap` and `…idealQuotientPushforwardIso`
prove Stacks 0EL1 outright for an arbitrary closed immersion `v` with `v.ker = I ^ n` and an
arbitrary quasi-coherent `F`. The results below remain the useful general form — they ask only
for membership in the essential image and know nothing about quasi-coherence — but they are no
longer the end of the line.

## Main results

* `Stacks.ToposBridge.isIso_unit_app_of_mem_essImage`: for an adjunction `L ⊣ R` with `R` fully
  faithful, the unit is an isomorphism at every object of the essential image of `R`.
* `Stacks.ToposBridge.isIso_unit_app_of_essImage`: the same for the pullback–pushforward
  adjunction along a closed immersion of schemes.
* `Stacks.ToposBridge.isIso_quotientSubschemeComparisonMap_of_essImage` and
  `Stacks.ToposBridge.quotientSubschemeComparison_of_essImage`: the Stacks 0EL1 comparison, from
  membership of the ideal-power quotient in the essential image of the pushforward.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.ToposBridge

/-- For an adjunction `L ⊣ R` whose right adjoint is fully faithful, the unit is an isomorphism at
every object of the essential image of `R`.

At `R.obj F` this is the triangle identity `η_{RF} ≫ R(ε_F) = 𝟙`: the counit is an isomorphism
because `R` is fully faithful, hence so is `R(ε_F)`, hence so is `η_{RF}`. The general case
follows by naturality of the unit along an isomorphism `R.obj F ≅ G`. -/
theorem isIso_unit_app_of_mem_essImage {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Full] [R.Faithful]
    {G : C} (hG : R.essImage G) :
    IsIso (adj.unit.app G) := by
  obtain ⟨F, ⟨e⟩⟩ := hG
  have hcounit : IsIso adj.counit := Adjunction.counit_isIso_of_R_fully_faithful adj
  have hRF : IsIso (adj.unit.app (R.obj F)) := by
    have h : IsIso (adj.unit.app (R.obj F) ≫ R.map (adj.counit.app F)) := by
      rw [adj.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (R.map (adj.counit.app F))
  have hnat := adj.unit.naturality e.inv
  have key : adj.unit.app G = e.inv ≫ adj.unit.app (R.obj F) ≫ inv ((L ⋙ R).map e.inv) := by
    rw [← Category.assoc, show e.inv ≫ adj.unit.app (R.obj F) =
        adj.unit.app G ≫ (L ⋙ R).map e.inv from hnat, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

/-- For a closed immersion of schemes `i`, the unit `G ⟶ i_* i^* G` of the
pullback–pushforward adjunction on sheaves of modules is an isomorphism at every `G` in the
essential image of `i_*`. -/
theorem isIso_unit_app_of_essImage {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] {G : X.Modules}
    (hG : (Scheme.Modules.pushforward i).essImage G) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G) :=
  isIso_unit_app_of_mem_essImage (Scheme.Modules.pullbackPushforwardAdjunction i) hG

open Stacks.Algebraization in
/-- **The remaining step of Stacks 0EL1, from the essential image.** If the ideal-power quotient
`F / I ^ n F` lies in the essential image of the pushforward along the closed immersion of the
`n`-th infinitesimal neighbourhood of `I`, then the canonical comparison
`Stacks.Algebraization.quotientSubschemeComparisonMap` is an isomorphism.

The adjunction unit at `F / I ^ n F` is an isomorphism by
`Stacks.ToposBridge.isIso_unit_app_of_essImage`, and naturality of the unit along the quotient
projection `π` identifies it with the comparison followed by `(ι_* ι^*).map π`, which is an
isomorphism because `ι^*` inverts `π`
(`Stacks.Algebraization.isIso_pullback_map_cokernel_π`). -/
theorem isIso_quotientSubschemeComparisonMap_of_essImage {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    (hG : (Scheme.Modules.pushforward (I ^ n).subschemeι).essImage
      (idealPowerQuotient I n F)) :
    IsIso (quotientSubschemeComparisonMap I n F) := by
  have hunit := isIso_unit_app_of_essImage (I ^ n).subschemeι hG
  have hmap : IsIso ((Scheme.Modules.pullback (I ^ n).subschemeι ⋙
      Scheme.Modules.pushforward (I ^ n).subschemeι).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)) := by
    dsimp only [CategoryTheory.Functor.comp_map]
    infer_instance
  have key : quotientSubschemeComparisonMap I n F ≫
      (Scheme.Modules.pullback (I ^ n).subschemeι ⋙
        Scheme.Modules.pushforward (I ^ n).subschemeι).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι) =
      (Scheme.Modules.pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app
        (idealPowerQuotient I n F) := by
    rw [← cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι),
      ← Category.assoc, quotientSubschemeComparisonMap_π]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction
      (I ^ n).subschemeι).unit.naturality
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)).symm
  have h2 : IsIso (quotientSubschemeComparisonMap I n F ≫
      (Scheme.Modules.pullback (I ^ n).subschemeι ⋙
        Scheme.Modules.pushforward (I ^ n).subschemeι).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)) := by
    rw [key]
    exact hunit
  exact IsIso.of_isIso_comp_right (quotientSubschemeComparisonMap I n F)
    ((Scheme.Modules.pullback (I ^ n).subschemeι ⋙
      Scheme.Modules.pushforward (I ^ n).subschemeι).map
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι))

open Stacks.Algebraization in
/-- **The Stacks 0EL1 comparison data, from the essential image.** The isomorphism
`F / I ^ n F ≅ ι_* ι^* F` normalized by the adjunction unit, produced from membership of the
ideal-power quotient in the essential image of the pushforward. -/
def quotientSubschemeComparison_of_essImage {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    (hG : (Scheme.Modules.pushforward (I ^ n).subschemeι).essImage
      (idealPowerQuotient I n F)) :
    QuotientSubschemeComparison I n F :=
  letI := isIso_quotientSubschemeComparisonMap_of_essImage I n F hG
  QuotientSubschemeComparison.ofIsIso I n F

end Stacks.ToposBridge

end
