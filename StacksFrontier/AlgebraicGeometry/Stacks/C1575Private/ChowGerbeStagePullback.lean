module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeLocalIsos

/-!
# Pulling back the stages of the proof of Stacks 0CQ7 along a proper morphism

Every replacement of `Y` by a proper `Y'' ⟶ Y'` in the proof of [Stacks, Tag 0CQ7] (by the finite
covers of Stacks 0CQ6, and by the closed complements of the induction on the number of opens) is
carried out on the data `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData`
by pulling back the opens and the sections. This file records that operation, that it keeps the
containment of `V'` in the opens and every Zariski-local isomorphism already found, and that it
does not shrink the image of `V'` in `Y` when `Y'' ⟶ Y'` is surjective.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.LocIso`: the sections
  `x_0` and `x_k` are Zariski locally isomorphic over `V'`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.pullback`: the stage
  data pulled back along a proper morphism `Y'' ⟶ Y'`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.image_subset_pullback`:
  pulling back along a surjection does not shrink the image of `V'` in `Y`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.locIso_pullback`: a
  Zariski-local isomorphism survives pulling back.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

open ChowGerbeMerge ChowGerbeSectionCover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W V : Subfunctor Y} {n : ℕ}

/-- **`x_0` and `x_k` are Zariski locally isomorphic over `V'`**: every point of `V'` has an open
neighbourhood inside `V'` over which they are 2-isomorphic. -/
def StageData.LocIso (D : StageData hY f W V n) (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) (k : ℕ) :
    Prop :=
  ∀ v ∈ Set.range (Space.pointsMap B S hS D.V'.1.toFunctor D.V'.1.ι),
    ∃ (O : Subfunctor D.Y'.1) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ D.V'.1),
      v ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS hO.1 (D.Wi 0).2.1
          (Subfunctor.homOfLe (hOV.trans (hVW 0))) ≫ D.x 0 ≅
        algebraicSpaceStackMap.{u, w} B S hS hO.1 (D.Wi k).2.1
          (Subfunctor.homOfLe (hOV.trans (hVW k))) ≫ D.x k)

/-- **The pullback of the stage data along a proper morphism `g : Y'' ⟶ Y'`.** The new
modification is `g ≫ p`, and `V'`, the opens and the sections are pulled back along `g`. -/
noncomputable def StageData.pullback (D : StageData hY f W V n)
    {Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY'' : IsAlgebraicSpace B S hS Y'')
    (g : Y'' ⟶ D.Y'.1) (hg : Space.IsProper B S hS g) :
    StageData hY f W V n where
  Y' := ⟨Y'', hY''⟩
  qc := Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS D.Y'.2 D.qc hg.2.1.2
  qs := Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY''
    D.qs (Space.isQuasiSeparated_of_isSeparated B S hS hg.1)
  p := g ≫ D.p
  hp := Space.isProper_comp B S hS hY'' D.Y'.2 hY g D.p hg D.hp
  V' := ⟨D.V'.1.preimage g, Space.isOpenSubspace_preimage B S hS g D.V'.1 D.Y'.2 hY'' D.V'.2⟩
  hV'qc := Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal D.Y'.2 D.qs
    hY'' (Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS D.Y'.2 D.qc hg.2.1.2)
    D.V'.1 D.hV'qc g
  hV'V := fun T _ hz => D.hV'V T hz
  hV'W := fun T _ hz => D.hV'W T hz
  Wi := fun k => ⟨(D.Wi k).1.preimage g,
    Space.isOpenSubspace_preimage B S hS g (D.Wi k).1 D.Y'.2 hY'' (D.Wi k).2⟩
  hWiqc := fun k => Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal
    D.Y'.2 D.qs hY'' (Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS D.Y'.2 D.qc
      hg.2.1.2) (D.Wi k).1 (D.hWiqc k) g
  hcov := by
    intro y hy
    change y ∈ Set.range (Space.pointsMap B S hS ((W.preimage D.p).preimage g).toFunctor
      ((W.preimage D.p).preimage g).ι) at hy
    rw [Space.range_pointsMap_preimage_ι] at hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (D.hcov hy)
    exact Set.mem_iUnion.2 ⟨k, by rwa [Space.range_pointsMap_preimage_ι]⟩
  x := fun k => algebraicSpaceStackMap.{u, w} B S hS
    (Space.isOpenSubspace_preimage B S hS g (D.Wi k).1 D.Y'.2 hY'' (D.Wi k).2).1 (D.Wi k).2.1
    ((D.Wi k).1.fromPreimage g) ≫ D.x k
  hx := fun k => by
    obtain ⟨e⟩ := nonempty_comp_iso_of_iso
      (Space.isOpenSubspace_preimage B S hS g (D.Wi k).1 D.Y'.2 hY'' (D.Wi k).2).1 (D.Wi k).2.1
      hY f ((D.Wi k).1.fromPreimage g) (D.x k) _ (D.hx k)
    exact ⟨e ≪≫ eqToIso (by rw [Subfunctor.fromPreimage_ι_assoc])⟩

variable (D : StageData hY f W V n) {Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hY'' : IsAlgebraicSpace B S hS Y'') (g : Y'' ⟶ D.Y'.1) (hg : Space.IsProper B S hS g)

/-- Pulling back keeps `V'` inside every open `W_k`. -/
theorem StageData.pullback_le (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) :
    ∀ k, (D.pullback hY'' g hg).V'.1 ≤ ((D.pullback hY'' g hg).Wi k).1 :=
  fun k T _ hz => hVW k T hz

/-- Pulling back does not enlarge the image of `V'` in `Y`. -/
theorem StageData.image_pullback_subset : (D.pullback hY'' g hg).image ⊆ D.image := by
  intro y hy
  change y ∈ Set.range (Space.pointsMap B S hS (D.V'.1.preimage g).toFunctor
    ((D.V'.1.preimage g).ι ≫ g ≫ D.p)) at hy
  obtain ⟨v, rfl⟩ := hy
  refine ⟨Space.pointsMap B S hS _ (D.V'.1.fromPreimage g) v, ?_⟩
  rw [← Space.pointsMap_comp_apply, Subfunctor.fromPreimage_ι_assoc]

/-- Pulling back along a surjective `g` does not shrink the image of `V'` in `Y`. -/
theorem StageData.image_subset_pullback (hgs : Space.IsSurjective B S hS g) :
    D.image ⊆ (D.pullback hY'' g hg).image := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨y, hy⟩ := hgs (Space.pointsMap B S hS _ D.V'.1.ι v)
  have hy' : y ∈ Set.range (Space.pointsMap B S hS (D.V'.1.preimage g).toFunctor
      (D.V'.1.preimage g).ι) := by
    rw [Space.range_pointsMap_preimage_ι]
    exact ⟨v, hy.symm⟩
  obtain ⟨z, rfl⟩ := hy'
  refine ⟨z, ?_⟩
  change Space.pointsMap B S hS (D.V'.1.preimage g).toFunctor
    ((D.V'.1.preimage g).ι ≫ g ≫ D.p) z = _
  rw [Space.pointsMap_comp_apply, Space.pointsMap_comp_apply, Space.pointsMap_comp_apply, hy,
    ← Space.pointsMap_comp_apply]

/-- **A Zariski-local isomorphism survives pulling back.** -/
theorem StageData.locIso_pullback (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) {k : ℕ}
    (h : D.LocIso hVW k) :
    (D.pullback hY'' g hg).LocIso (D.pullback_le hY'' g hg hVW) k := by
  intro v hv
  change v ∈ Set.range (Space.pointsMap B S hS (D.V'.1.preimage g).toFunctor
    (D.V'.1.preimage g).ι) at hv
  rw [Space.range_pointsMap_preimage_ι] at hv
  obtain ⟨O, hO, hOV, hvO, ⟨e⟩⟩ := h _ hv
  let O' : Subfunctor Y'' := O.preimage g
  have hO' : Space.IsOpenSubspace B S hS O' :=
    Space.isOpenSubspace_preimage B S hS g O D.Y'.2 hY'' hO
  have hO'V : O' ≤ (D.pullback hY'' g hg).V'.1 := fun T _ hz => hOV T hz
  refine ⟨O', hO', hO'V, ?_, ?_⟩
  · change v ∈ Set.range (Space.pointsMap B S hS (O.preimage g).toFunctor (O.preimage g).ι)
    rwa [Space.range_pointsMap_preimage_ι]
  have e₀ := stackMap_comp_comp_eq (𝒳 := 𝒳) hO'.1 (D.Wi 0).2.1
    ((D.pullback hY'' g hg).Wi 0).2.1 hO.1
    (Subfunctor.homOfLe (hO'V.trans (D.pullback_le hY'' g hg hVW 0)))
    ((D.Wi 0).1.fromPreimage g) (O.fromPreimage g) (Subfunctor.homOfLe (hOV.trans (hVW 0)))
    (by ext T z; rfl) (D.x 0)
  have e₁ := stackMap_comp_comp_eq (𝒳 := 𝒳) hO'.1 (D.Wi k).2.1
    ((D.pullback hY'' g hg).Wi k).2.1 hO.1
    (Subfunctor.homOfLe (hO'V.trans (D.pullback_le hY'' g hg hVW k)))
    ((D.Wi k).1.fromPreimage g) (O.fromPreimage g) (Subfunctor.homOfLe (hOV.trans (hVW k)))
    (by ext T z; rfl) (D.x k)
  exact ⟨eqToIso e₀ ≪≫ Bicategory.whiskerLeftIso
    (algebraicSpaceStackMap.{u, w} B S hS hO'.1 hO.1 (O.fromPreimage g)) e ≪≫ eqToIso e₁.symm⟩

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

end
