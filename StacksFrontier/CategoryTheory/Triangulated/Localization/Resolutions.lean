module

public import StacksFrontier.CategoryTheory.Triangulated.Localization.Pretriangulated
import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a subcategory with enough resolutions

Let `C` be a pre-triangulated category and `W` a saturated multiplicative system compatible
with the triangulated structure. For a full pre-triangulated subcategory `P` of `C` the class
`W ∩ Arrows(P)` is again a saturated multiplicative system compatible with the triangulated
structure of `P`, being the class of morphisms of `P` inverted by the exact functor `P.ι ⋙ Q`;
and if every object of `C` admits a resolution `X' ⟶ X` in `W` with `X'` in `P`, then the
inclusion induces an equivalence `(W ∩ Arrows(P))⁻¹P ≌ W⁻¹C`.

## Main results

* `isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence`, in
  the `CategoryTheory.ObjectProperty` namespace: `W ∩ Arrows(P)` is a saturated multiplicative
  system compatible with the triangulated structure of `P`, and with enough resolutions the
  inclusion of `P` is a localized equivalence.

## References

* [Stacks, Tag 0GSL](https://stacks.math.columbia.edu/tag/0GSL).
-/

@[expose] public section

universe v₁ v₂ v u₁ u₂ u

/-! ### Localizing a subcategory with enough resolutions -/

section Resolutions

open CategoryTheory Limits MorphismProperty Pretriangulated

/-- A morphism of localizers `Φ` with fully faithful functor, whose source class is the
inverse image of the target class, and which has left resolutions, is a localized
equivalence, provided the target class has a calculus of right fractions and the source class
one of left fractions. It is the mirror image, for left resolutions and right fractions, of
the situation `LocalizerMorphism.isLocalizedEquivalence_of_functorial_right_resolutions`
treats for functorial resolutions, and it needs no functoriality of the resolutions. -/
private lemma isLocalizedEquivalence_of_hasLeftResolutions
    {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsInduced] [Φ.functor.Full] [Φ.functor.Faithful]
    [W₁.HasLeftCalculusOfFractions] [W₂.HasRightCalculusOfFractions]
    [Φ.HasLeftResolutions] :
    Φ.IsLocalizedEquivalence := by
  let L₁ := W₁.Q
  let L₂ := W₂.Q
  let G := Φ.localizedFunctor L₁ L₂
  have e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso Φ.functor L₁ L₂ G
  have N : ∀ {A B : C₁} (h : A ⟶ B),
      e.hom.app A ≫ G.map (L₁.map h) = L₂.map (Φ.functor.map h) ≫ e.hom.app B :=
    fun h ↦ (e.hom.naturality h).symm
  have res : ∀ {Z X} (s : Z ⟶ Φ.functor.obj X), W₂ s →
      ∃ (ρ : Φ.LeftResolution Z) (u : ρ.X₁ ⟶ X), Φ.functor.map u = ρ.w ≫ s ∧ W₁ u := by
    intro Z X s hs
    let ρ : Φ.LeftResolution Z := Classical.arbitrary _
    refine ⟨ρ, Φ.functor.preimage (ρ.w ≫ s), by simp, ?_⟩
    exact Φ.inverseImage_eq.le _ (by simpa using W₂.comp_mem _ _ ρ.hw hs)
  have hGs : G.EssSurj := by
    have h := Φ.essSurj_of_hasLeftResolutions L₂
    refine ⟨fun Y ↦ ?_⟩
    obtain ⟨X, ⟨i⟩⟩ := h.mem_essImage Y
    exact ⟨L₁.obj X, ⟨(e.app X).symm ≪≫ i⟩⟩
  have hGf : G.Full := by
    refine G.full_of_comp_essSurj L₁ (fun X₁ X₂ φ ↦ ?_)
    obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction L₂ W₂
      (e.hom.app X₁ ≫ φ ≫ e.inv.app X₂)
    obtain ⟨ρ, u, hu, huW⟩ := res ψ.s ψ.hs
    let g : W₁.RightFraction X₁ X₂ := ⟨u, huW, Φ.functor.preimage (ρ.w ≫ ψ.f)⟩
    have hφ : e.hom.app X₁ ≫ φ = ψ.map L₂ (Localization.inverts _ _) ≫ e.hom.app X₂ := by
      rw [← hψ]; simp
    have := Localization.inverts L₁ W₁ _ huW
    refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
    rw [← cancel_epi (G.map (L₁.map g.s)), ← G.map_comp,
      MorphismProperty.RightFraction.map_s_comp_map,
      ← cancel_epi (e.hom.app ρ.X₁), ← Category.assoc, N, N, Category.assoc, hφ,
      ← Category.assoc]
    congr 1
    simp only [g, hu, Functor.map_preimage, Functor.map_comp, Category.assoc,
      MorphismProperty.RightFraction.map_s_comp_map]
  have hGff : G.Faithful := by
    refine Functor.faithful_of_comp_of_hasLeftCalculusOfFractions L₁ W₁ G
      (fun X₁ X₂ f g hfg ↦ ?_)
    have h2 : L₂.map (Φ.functor.map f) = L₂.map (Φ.functor.map g) := by
      rw [← cancel_mono (e.hom.app X₂), ← N, ← N, hfg]
    rw [MorphismProperty.map_eq_iff_precomp L₂ W₂] at h2
    obtain ⟨Z, s, hsW, fac⟩ := h2
    obtain ⟨ρ, u, hu, huW⟩ := res s hsW
    have := Localization.inverts L₁ W₁ _ huW
    rw [← cancel_epi (L₁.map u), ← L₁.map_comp, ← L₁.map_comp]
    congr 1
    apply Φ.functor.map_injective
    simp only [Functor.map_comp, hu, Category.assoc, fac]
  have : G.IsEquivalence := { }
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ L₁ L₂ G

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated] (W : MorphismProperty C)

/-- Let `C` be a pre-triangulated category, let `P` be a full pre-triangulated subcategory of `C`,
and let `W` be a saturated multiplicative system of morphisms of `C` compatible with the
triangulated structure. Then `W ∩ Arrows(P)`, i.e. `W.inverseImage P.ι`, is a saturated
multiplicative system on `P` compatible with the triangulated structure, and if every object of `C`
admits a resolution by `P` — a morphism `s : X' ⟶ X` in `W` with `X'` in `P` — then the inclusion
of `P` induces an equivalence `(W ∩ Arrows(P))⁻¹P ⥤ W⁻¹C`. -/
@[stacks 0GSL, sga "4½ Etat_0 2.4.2" "(a)"]
theorem isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
    (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation] :
    (W.inverseImage P.ι).IsSaturated ∧
      (W.inverseImage P.ι).IsCompatibleWithTriangulation ∧
      (({ functor := P.ι, map := le_rfl } :
            LocalizerMorphism (W.inverseImage P.ι) W).HasLeftResolutions →
        ({ functor := P.ι, map := le_rfl } :
          LocalizerMorphism (W.inverseImage P.ι) W).IsLocalizedEquivalence) := by
  have := hW.hasLeftCalculusOfFractions
  have := hW.hasRightCalculusOfFractions
  have hQ : W.Q.IsTriangulated := Triangulated.Localization.isTriangulated_functor W.Q W
  have key : W.inverseImage P.ι =
      (isomorphisms W.Localization).inverseImage (P.ι ⋙ W.Q) := by
    rw [show (isomorphisms W.Localization).inverseImage (P.ι ⋙ W.Q)
        = ((isomorphisms W.Localization).inverseImage W.Q).inverseImage P.ι from rfl,
      show ((isomorphisms W.Localization).inverseImage W.Q) = W from hW.invertedClosure_eq]
  have h12 := Functor.isSaturated_and_isCompatibleWithTriangulation_inverseImage_isomorphisms
    (P.ι ⋙ W.Q)
  rw [← key] at h12
  refine ⟨h12.1, h12.2, fun hres ↦ ?_⟩
  have := h12.1.hasLeftCalculusOfFractions
  have : ({ functor := P.ι, map := le_rfl } :
      LocalizerMorphism (W.inverseImage P.ι) W).IsInduced := ⟨rfl⟩
  exact isLocalizedEquivalence_of_hasLeftResolutions _

end CategoryTheory.ObjectProperty

end Resolutions

end
