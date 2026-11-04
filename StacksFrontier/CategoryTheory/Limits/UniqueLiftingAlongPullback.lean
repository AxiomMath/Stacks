module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Unique lifting of morphisms along a base change

Let `w : W ⟶ Z` be a morphism and let `p : X ⟶ Z`, `q : Y ⟶ Z` be two objects over `Z`. We say
that morphisms from `p` to `q` *lift uniquely along `w`* when base change along `w` is bijective
on morphisms over `Z`: for all cartesian squares exhibiting `X'` and `Y'` as the base changes of
`X` and `Y` along `w`, every morphism `X' ⟶ Y'` over `W` is the base change of a unique morphism
`X ⟶ Y` over `Z`.

This is the shape of the topological invariance of the étale site (Stacks 0BTY): for `w` a
universal homeomorphism of schemes and `q` étale, morphisms from any `p` to `q` lift uniquely
along `w`. The point of the abstraction is that the property is invariant under replacing `X`
and `Y` by isomorphic objects over `Z`, and transports along a functor which is fully faithful,
or only faithful and full on morphisms over `Z`, and preserves pullbacks.

## Main definitions

* `CategoryTheory.Limits.UniqueLiftingAlong`: unique lifting of morphisms along `w`.

## Main results

* `CategoryTheory.Limits.UniqueLiftingAlong.of_pullback`: it suffices to check the chosen
  pullbacks.
* `CategoryTheory.Limits.UniqueLiftingAlong.of_iso`: invariance under isomorphisms over `Z`.
* `CategoryTheory.Limits.UniqueLiftingAlong.map`: transport along a fully faithful functor
  preserving pullbacks.
* `CategoryTheory.Limits.UniqueLiftingAlong.of_map`: descent along a faithful functor preserving
  pullbacks which is full on morphisms over the target.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Morphisms from `p : X ⟶ Z` to `q : Y ⟶ Z` *lift uniquely along* `w : W ⟶ Z` when, for all
cartesian squares exhibiting `X'` and `Y'` as base changes of `X` and `Y` along `w`, every
morphism `X' ⟶ Y'` over `W` is the base change of a unique morphism `X ⟶ Y` over `Z`. -/
def UniqueLiftingAlong {W Z X Y : C} (w : W ⟶ Z) (p : X ⟶ Z) (q : Y ⟶ Z) : Prop :=
  ∀ ⦃X' Y' : C⦄ (a : X' ⟶ X) (p' : X' ⟶ W) (b : Y' ⟶ Y) (q' : Y' ⟶ W),
    IsPullback a p' p w → IsPullback b q' q w → ∀ φ : X' ⟶ Y', φ ≫ q' = p' →
      ∃! ψ : X ⟶ Y, ψ ≫ q = p ∧ a ≫ ψ = φ ≫ b

namespace UniqueLiftingAlong

variable {W Z X Y : C} {w : W ⟶ Z} {p : X ⟶ Z} {q : Y ⟶ Z}

/-- Transport of the lifting condition along isomorphisms from two squares to chosen pullbacks. -/
private theorem lifting_cond_of_isos {A B V A' B' PA PB : C} (εA : A' ≅ PA) (εB : B' ≅ PB)
    {a : A' ⟶ A} {f : PA ⟶ A} {p' : A' ⟶ V} {g : PA ⟶ V} {b : B' ⟶ B} {fB : PB ⟶ B}
    {q' : B' ⟶ V} {gB : PB ⟶ V} (ha : εA.hom ≫ f = a) (hp : εA.hom ≫ g = p')
    (hb : εB.hom ≫ fB = b) (hq : εB.hom ≫ gB = q') {φ : A' ⟶ B'} (hφ : φ ≫ q' = p') :
    (εA.inv ≫ φ ≫ εB.hom) ≫ gB = g ∧
      ∀ χ : A ⟶ B, a ≫ χ = φ ≫ b ↔ f ≫ χ = (εA.inv ≫ φ ≫ εB.hom) ≫ fB := by
  subst ha hp hb hq
  refine ⟨?_, fun χ ↦ ?_⟩
  · rw [Category.assoc, Category.assoc, hφ, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, Category.assoc, Category.assoc, Iso.eq_inv_comp]

/-- Unique lifting along `w` may be checked on the chosen pullbacks. -/
theorem of_pullback [HasPullback p w] [HasPullback q w]
    (h : ∀ φ : pullback p w ⟶ pullback q w, φ ≫ pullback.snd q w = pullback.snd p w →
      ∃! ψ : X ⟶ Y, ψ ≫ q = p ∧ pullback.fst p w ≫ ψ = φ ≫ pullback.fst q w) :
    UniqueLiftingAlong w p q := by
  intro X' Y' a p' b q' hX hY φ hφ
  let εX := hX.isoPullback
  let εY := hY.isoPullback
  have hεXf : εX.hom ≫ pullback.fst p w = a := hX.isoPullback_hom_fst
  have hεXs : εX.hom ≫ pullback.snd p w = p' := hX.isoPullback_hom_snd
  have hεYf : εY.hom ≫ pullback.fst q w = b := hY.isoPullback_hom_fst
  have hεYs : εY.hom ≫ pullback.snd q w = q' := hY.isoPullback_hom_snd
  obtain ⟨hcond, key⟩ := lifting_cond_of_isos εX εY hεXf hεXs hεYf hεYs hφ
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, huniq⟩ := h _ hcond
  exact ⟨ψ, ⟨hψ₁, (key ψ).2 hψ₂⟩, fun χ hχ ↦ huniq χ ⟨hχ.1, (key χ).1 hχ.2⟩⟩

/-- Unique lifting along `w` is invariant under replacing the two objects over `Z` by
isomorphic ones. -/
theorem of_iso (h : UniqueLiftingAlong w p q) {X₁ Y₁ : C} (eX : X₁ ≅ X) (eY : Y₁ ≅ Y) :
    UniqueLiftingAlong w (eX.hom ≫ p) (eY.hom ≫ q) := by
  intro X' Y' a p' b q' hX hY φ hφ
  have sqX : IsPullback eX.hom (eX.hom ≫ p) p (𝟙 Z) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have sqY : IsPullback eY.hom (eY.hom ≫ q) q (𝟙 Z) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hX' : IsPullback (a ≫ eX.hom) p' p w := by
    simpa using hX.paste_horiz sqX
  have hY' : IsPullback (b ≫ eY.hom) q' q w := by
    simpa using hY.paste_horiz sqY
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, huniq⟩ := h _ _ _ _ hX' hY' φ hφ
  refine ⟨eX.hom ≫ ψ ≫ eY.inv, ⟨by simp [hψ₁], ?_⟩, fun χ hχ ↦ ?_⟩
  · rw [← Category.assoc a, ← Category.assoc (a ≫ eX.hom), hψ₂]
    simp
  · have h₁ : (eX.inv ≫ χ ≫ eY.hom) ≫ q = p := by
      rw [Category.assoc, Category.assoc, hχ.1, Iso.inv_hom_id_assoc]
    have h₂ : (a ≫ eX.hom) ≫ eX.inv ≫ χ ≫ eY.hom = φ ≫ b ≫ eY.hom := by
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hχ.2, Category.assoc]
    rw [← huniq _ ⟨h₁, h₂⟩]
    simp

/-- Unique lifting along `w` is invariant under replacing the two objects over `Z` by
isomorphic ones, with the new structure morphisms named. -/
theorem of_iso_of_eq (h : UniqueLiftingAlong w p q) {X₁ Y₁ : C} (eX : X₁ ≅ X) (eY : Y₁ ≅ Y)
    {p₁ : X₁ ⟶ Z} {q₁ : Y₁ ⟶ Z} (hp : eX.hom ≫ p = p₁) (hq : eY.hom ≫ q = q₁) :
    UniqueLiftingAlong w p₁ q₁ := by
  subst hp hq
  exact h.of_iso eX eY

/-- Unique lifting along `w` transports along a fully faithful functor which preserves the
relevant pullbacks. -/
theorem map [HasPullback p w] [HasPullback q w] (F : C ⥤ D) [F.Full] [F.Faithful]
    [PreservesLimit (cospan p w) F] [PreservesLimit (cospan q w) F]
    (h : UniqueLiftingAlong w p q) :
    UniqueLiftingAlong (F.map w) (F.map p) (F.map q) := by
  intro X' Y' a p' b q' hX hY φ hφ
  have PX : IsPullback (F.map (pullback.fst p w)) (F.map (pullback.snd p w)) (F.map p)
      (F.map w) := (IsPullback.of_hasPullback p w).map F
  have PY : IsPullback (F.map (pullback.fst q w)) (F.map (pullback.snd q w)) (F.map q)
      (F.map w) := (IsPullback.of_hasPullback q w).map F
  let εX := hX.isoIsPullback _ _ PX
  let εY := hY.isoIsPullback _ _ PY
  have hεXf : εX.hom ≫ F.map (pullback.fst p w) = a := hX.isoIsPullback_hom_fst _ _ PX
  have hεXs : εX.hom ≫ F.map (pullback.snd p w) = p' := hX.isoIsPullback_hom_snd _ _ PX
  have hεYf : εY.hom ≫ F.map (pullback.fst q w) = b := hY.isoIsPullback_hom_fst _ _ PY
  have hεYs : εY.hom ≫ F.map (pullback.snd q w) = q' := hY.isoIsPullback_hom_snd _ _ PY
  let φ'' := F.preimage (εX.inv ≫ φ ≫ εY.hom)
  have hφ''map : F.map φ'' = εX.inv ≫ φ ≫ εY.hom := F.map_preimage _
  obtain ⟨hcond', key'⟩ := lifting_cond_of_isos εX εY hεXf hεXs hεYf hεYs hφ
  rw [← hφ''map] at hcond' key'
  have hcond : φ'' ≫ pullback.snd q w = pullback.snd p w := F.map_injective (by simpa using hcond')
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, huniq⟩ :=
    h _ _ _ _ (IsPullback.of_hasPullback p w) (IsPullback.of_hasPullback q w) φ'' hcond
  have key : ∀ χ : X ⟶ Y, (a ≫ F.map χ = φ ≫ b ↔
      pullback.fst p w ≫ χ = φ'' ≫ pullback.fst q w) := fun χ ↦
    (key' (F.map χ)).trans <| by rw [← F.map_comp, ← F.map_comp, F.map_injective.eq_iff]
  refine ⟨F.map ψ, ⟨by rw [← F.map_comp, hψ₁], (key ψ).2 hψ₂⟩, fun χ hχ ↦ ?_⟩
  have hχ₁ : F.preimage χ ≫ q = p := F.map_injective (by rw [F.map_comp, F.map_preimage, hχ.1])
  have hχ₂ : pullback.fst p w ≫ F.preimage χ = φ'' ≫ pullback.fst q w :=
    (key _).1 (by rw [F.map_preimage]; exact hχ.2)
  rw [← huniq _ ⟨hχ₁, hχ₂⟩, F.map_preimage]

/-- Unique lifting along `w` descends along a faithful functor which preserves the relevant
pullbacks and is full on morphisms over `Z`. -/
theorem of_map (F : C ⥤ D) [F.Faithful]
    (hfull : ∀ ψ : F.obj X ⟶ F.obj Y, ψ ≫ F.map q = F.map p → ∃ m : X ⟶ Y, F.map m = ψ)
    (hpres : ∀ ⦃X' Y' : C⦄ (a : X' ⟶ X) (p' : X' ⟶ W) (b : Y' ⟶ Y) (q' : Y' ⟶ W),
      IsPullback a p' p w → IsPullback b q' q w →
        IsPullback (F.map a) (F.map p') (F.map p) (F.map w) ∧
          IsPullback (F.map b) (F.map q') (F.map q) (F.map w))
    (h : UniqueLiftingAlong (F.map w) (F.map p) (F.map q)) :
    UniqueLiftingAlong w p q := by
  intro X' Y' a p' b q' hX hY φ hφ
  obtain ⟨hFX, hFY⟩ := hpres a p' b q' hX hY
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, huniq⟩ :=
    h _ _ _ _ hFX hFY (F.map φ) (by rw [← F.map_comp, hφ])
  obtain ⟨m, rfl⟩ := hfull ψ hψ₁
  exact ⟨m, ⟨F.map_injective (by rw [F.map_comp, hψ₁]),
    F.map_injective (by rw [F.map_comp, F.map_comp, hψ₂])⟩,
    fun χ hχ ↦ F.map_injective (huniq _ ⟨by rw [← F.map_comp, hχ.1],
      by rw [← F.map_comp, ← F.map_comp, hχ.2]⟩)⟩

end UniqueLiftingAlong

end CategoryTheory.Limits

end
