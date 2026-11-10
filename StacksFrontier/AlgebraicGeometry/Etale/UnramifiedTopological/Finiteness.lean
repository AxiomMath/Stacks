module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# Finiteness of the set of morphisms into an unramified scheme

Over a Noetherian base scheme, a quasi-compact unramified scheme admits only finitely many
morphisms over the base from any Noetherian scheme.

## Main results

* `AlgebraicGeometry.Unramified.finite_morphisms_over_of_unramified`: the set of morphisms from
  a Noetherian scheme to a quasi-compact unramified scheme, compatible with their maps to a
  Noetherian base, is finite.

## Implementation notes

The set `Mor_S(Y, X)` is represented by the morphisms `f : Y ⟶ X` whose composite with the
structure map of `X` equals the given structure map of `Y`.

## References

* [Stacks Project, Tag 0AKI](https://stacks.math.columbia.edu/tag/0AKI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Unramified

private lemma isOpenImmersion_of_section {T P : Scheme.{u}} (q : P ⟶ T)
    [IsOpenImmersion (pullback.diagonal q)] (s : T ⟶ P) (hs : s ≫ q = 𝟙 T) :
    IsOpenImmersion s := by
  let : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}).diagonal :=
    (MorphismProperty.hasOfPostcompProperty_iff_le_diagonal).2 le_rfl
  apply MorphismProperty.of_postcomp (W := IsOpenImmersion) (W' :=
    (@IsOpenImmersion : MorphismProperty Scheme.{u}).diagonal) s q
    (show IsOpenImmersion (pullback.diagonal q) from inferInstance)
  rw [hs]
  exact MorphismProperty.id_mem IsOpenImmersion T

private lemma mem_range_diagonal_of_projections_mem_section
    {T P : Scheme.{u}} (q : P ⟶ T) (s : T ⟶ P)
    (hs : s ≫ q = 𝟙 T) [IsOpenImmersion s]
    (z : ↥(pullback q q)) (h₁ : pullback.fst q q z ∈ Set.range s)
    (h₂ : pullback.snd q q z ∈ Set.range s) :
    z ∈ Set.range (pullback.diagonal q) := by
  let W : (pullback q q).Opens :=
    (pullback.fst q q ⁻¹ᵁ s.opensRange) ⊓ (pullback.snd q q ⁻¹ᵁ s.opensRange)
  have hfst : Set.range (W.ι ≫ pullback.fst q q) ⊆ Set.range s := by
    rintro _ ⟨x, rfl⟩; exact x.2.1
  have hsnd : Set.range (W.ι ≫ pullback.snd q q) ⊆ Set.range s := by
    rintro _ ⟨x, rfl⟩; exact x.2.2
  let a := IsOpenImmersion.lift s (W.ι ≫ pullback.fst q q) hfst
  let b := IsOpenImmersion.lift s (W.ι ≫ pullback.snd q q) hsnd
  have ha : a ≫ s = W.ι ≫ pullback.fst q q := IsOpenImmersion.lift_fac ..
  have hb : b ≫ s = W.ι ≫ pullback.snd q q := IsOpenImmersion.lift_fac ..
  have hab : a = b := by
    calc
      a = a ≫ s ≫ q := by rw [hs, Category.comp_id]
      _ = W.ι ≫ pullback.fst q q ≫ q := by rw [← Category.assoc, ha, Category.assoc]
      _ = W.ι ≫ pullback.snd q q ≫ q := by rw [pullback.condition]
      _ = b ≫ s ≫ q := by rw [← Category.assoc, ← hb, Category.assoc]
      _ = b := by rw [hs, Category.comp_id]
  have hfac : (W.ι ≫ pullback.fst q q) ≫ pullback.diagonal q = W.ι := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]; rw [← ha, ← hb, hab]
  exact ⟨(W.ι ≫ pullback.fst q q) ⟨z, h₁, h₂⟩,
    congrArg (fun f : W.toScheme ⟶ pullback q q => f ⟨z, h₁, h₂⟩) hfac⟩

private lemma finite_sections_of_isOpenImmersion_diagonal {T P : Scheme.{u}} (q : P ⟶ T)
    [IsOpenImmersion (pullback.diagonal q)]
    [TopologicalSpace.NoetherianSpace ↥(pullback q q)] :
    Set.Finite {s : T ⟶ P | s ≫ q = 𝟙 T} := by
  classical
  let C : Set ↥(pullback q q) := (Set.range (pullback.diagonal q))ᶜ
  have hC : IsClosed C := (IsOpenImmersion.isOpen_range (pullback.diagonal q)).isClosed_compl
  have : QuasiSober C := hC.isClosedEmbedding_subtypeVal.quasiSober
  have : Finite (genericPoints C) :=
    (genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  let sec := {s : T ⟶ P // s ≫ q = 𝟙 T}
  let code : sec → Set (genericPoints C) := fun s =>
    {η | pullback.fst q q η.1.1 ∈ Set.range s.1}
  have hinj : Function.Injective code := by
    intro s t hst
    have : IsOpenImmersion s.1 := isOpenImmersion_of_section q s.1 s.2
    have : IsOpenImmersion t.1 := isOpenImmersion_of_section q t.1 t.2
    let W : (pullback q q).Opens :=
      (pullback.fst q q ⁻¹ᵁ s.1.opensRange) ⊓ (pullback.snd q q ⁻¹ᵁ t.1.opensRange)
    have hW : (W : Set ↥(pullback q q)) ⊆ Set.range (pullback.diagonal q) := by
      intro z hz; by_contra hn
      have hopen : IsOpen (Subtype.val ⁻¹' (W : Set ↥(pullback q q)) : Set C) :=
        W.isOpen.preimage continuous_subtype_val
      have hdense : Dense (genericPoints C) := by rw [dense_iff_closure_eq, genericPoints.closure]
      obtain ⟨η, hηW, hη⟩ := hdense.inter_open_nonempty _ hopen ⟨⟨z, hn⟩, hz⟩
      have hηt : pullback.fst q q η.1 ∈ Set.range t.1 := by
        change (⟨η, hη⟩ : genericPoints C) ∈ code t
        rw [← hst]
        exact hηW.1
      exact η.2 (mem_range_diagonal_of_projections_mem_section q t.1 t.2 η.1 hηt hηW.2)
    let l : T ⟶ pullback q q := pullback.lift s.1 t.1 (s.2.trans t.2.symm)
    have hl : Set.range l ⊆ Set.range (pullback.diagonal q) := by
      rintro _ ⟨y, rfl⟩
      exact hW ⟨⟨y, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩,
        ⟨y, by rw [← Scheme.Hom.comp_apply, pullback.lift_snd]⟩⟩
    have h : l ≫ pullback.fst q q = l ≫ pullback.snd q q := by
      rw [← IsOpenImmersion.lift_fac (pullback.diagonal q) l hl]
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
    exact Subtype.ext ((pullback.lift_fst ..).symm.trans (h.trans (pullback.lift_snd ..)))
  exact Finite.of_injective code hinj

/-- There are finitely many morphisms over a Noetherian base from a Noetherian scheme to a
quasi-compact unramified scheme. -/
@[stacks 0AKI]
public theorem finite_morphisms_over_of_unramified {S X Y : Scheme.{u}}
    (π : X ⟶ S) (g : Y ⟶ S) [IsNoetherian S] [IsNoetherian Y]
    [QuasiCompact π] [Unramified π] :
    Set.Finite {f : Y ⟶ X | f ≫ π = g} := by
  classical
  let q := pullback.snd π g
  have : Unramified q := unramified_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π g) (inferInstance : Unramified π)
  have : LocallyOfFiniteType q := locallyOfFiniteType_of_unramified q
  have : QuasiCompact q := inferInstanceAs (QuasiCompact (pullback.snd π g))
  have : IsLocallyNoetherian (pullback π g) := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace ↥(pullback π g) := QuasiCompact.compactSpace_of_compactSpace q
  have : CompactSpace ↥(pullback q q) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst q q)
  have : IsNoetherian (pullback q q) := AlgebraicGeometry.IsNoetherian.mk
  let F : {f : Y ⟶ X // f ≫ π = g} → {s : Y ⟶ pullback π g // s ≫ q = 𝟙 Y} :=
    fun f => ⟨pullback.lift f.1 (𝟙 Y) (by simpa using f.2), pullback.lift_snd ..⟩
  have : Finite {s : Y ⟶ pullback π g // s ≫ q = 𝟙 Y} :=
    finite_sections_of_isOpenImmersion_diagonal q
  exact Finite.of_injective F (by
    intro f h e
    apply Subtype.ext
    have he := congrArg (fun s => s.1 ≫ pullback.fst π g) e
    simpa only [F, pullback.lift_fst] using he)

end AlgebraicGeometry.Unramified

end
