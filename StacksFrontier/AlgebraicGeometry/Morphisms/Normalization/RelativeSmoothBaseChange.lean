module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Functorial

/-!
# Relative normalization commutes with smooth base change, for an arbitrary cartesian square

Mathlib proves that the relative normalization commutes with smooth base change in the shape
`AlgebraicGeometry.Scheme.Hom.normalizationPullback`, a comparison morphism out of the
normalization of the *chosen* pullback `pullback.snd g w`. A consumer which is handed a
cartesian square `IsPullback a p g w` — for instance a chart of an algebraic space, where the
fibre product is represented by whichever object of the site happens to represent it — cannot
use that shape directly, because its `p` is only isomorphic to `pullback.snd g w`.

This file transports the statement to an arbitrary cartesian square. For a quasi-compact and
quasi-separated `g : X ⟶ Y`, a smooth `w : W ⟶ Y` and a cartesian square with `p : XW ⟶ W`
quasi-compact and quasi-separated, the canonical morphism
`AlgebraicGeometry.Scheme.Hom.normalizationMap` of Tag 035J fits into a cartesian square

```
XW^ν ---> X^ν
 |          |
 v          v
 W -------> Y
```

So the normalization of `W` in `XW` is the fibre product of the normalization of `Y` in `X`
with `W`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalizationMap_id`: the canonical morphism of Tag 035J
  attached to the identity square is the identity.
* `AlgebraicGeometry.Scheme.Hom.isIso_normalizationMap`: the canonical morphism attached to a
  square whose two horizontal legs are isomorphisms is an isomorphism.
* `AlgebraicGeometry.isPullback_normalizationMap_of_smooth`: the cartesian square above. This
  is Mathlib's `IsIso (g.normalizationPullback w)` read on an arbitrary cartesian square.

## Implementation notes

Both auxiliary lemmas are instances of the uniqueness clause
`AlgebraicGeometry.Scheme.Hom.normalizationMap_unique` of Tag 035J: a morphism of relative
normalizations making the two evident squares commute *is* the canonical one. That is also how
the main result identifies Mathlib's comparison morphism, composed with the first projection,
with the canonical morphism of the chosen cartesian square; the arbitrary square is then
compared with the chosen one by the isomorphism of their sources, which the second auxiliary
lemma turns into an isomorphism of normalizations.

The smooth base change statement of Tag 03GV is the Mathlib instance
`IsIso (g.normalizationPullback w)`; this file restates it on an arbitrary cartesian square.

## References

* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
* [Stacks Project, Tag 035J](https://stacks.math.columbia.edu/tag/035J)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {Y₁ Y₂ X₁ X₂ : Scheme.{u}}

/-- The canonical morphism of relative normalizations attached to the identity square is the
identity. -/
theorem normalizationMap_id (f : Y₁ ⟶ X₁) [QuasiCompact f] [QuasiSeparated f] :
    normalizationMap f f (𝟙 Y₁) (𝟙 X₁) (by simp) = 𝟙 f.normalization :=
  (normalizationMap_unique f f (𝟙 Y₁) (𝟙 X₁) (by simp) (𝟙 _) (by simp) (by simp)).symm

/-- Canonical morphisms of relative normalizations attached to mutually inverse squares compose to
the identity. -/
private theorem normalizationMap_comp_normalizationMap_eq_id (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
    [QuasiCompact f₁] [QuasiSeparated f₁] [QuasiCompact f₂] [QuasiSeparated f₂]
    {gY : Y₂ ⟶ Y₁} {gX : X₂ ⟶ X₁} {gY' : Y₁ ⟶ Y₂} {gX' : X₁ ⟶ X₂}
    (sq : gY ≫ f₁ = f₂ ≫ gX) (sq' : gY' ≫ f₂ = f₁ ≫ gX')
    (hY : gY ≫ gY' = 𝟙 Y₂) (hX : gX ≫ gX' = 𝟙 X₂) :
    normalizationMap f₁ f₂ gY gX sq ≫ normalizationMap f₂ f₁ gY' gX' sq' = 𝟙 f₂.normalization := by
  rw [normalizationMap_unique f₂ f₂ (𝟙 Y₂) (𝟙 X₂) (by simp)
    (normalizationMap f₁ f₂ gY gX sq ≫ normalizationMap f₂ f₁ gY' gX' sq')
    (by rw [← Category.assoc, toNormalization_normalizationMap, Category.assoc,
      toNormalization_normalizationMap, ← Category.assoc, hY, Category.id_comp])
    (by rw [Category.assoc, normalizationMap_fromNormalization, ← Category.assoc,
      normalizationMap_fromNormalization, Category.assoc, hX, Category.comp_id]),
    normalizationMap_id]

/-- The canonical morphism of relative normalizations attached to a square whose two horizontal
legs are isomorphisms is an isomorphism. -/
theorem isIso_normalizationMap (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
    [QuasiCompact f₁] [QuasiSeparated f₁] [QuasiCompact f₂] [QuasiSeparated f₂]
    (gY : Y₂ ⟶ Y₁) (gX : X₂ ⟶ X₁) [IsIso gY] [IsIso gX] (sq : gY ≫ f₁ = f₂ ≫ gX) :
    IsIso (normalizationMap f₁ f₂ gY gX sq) := by
  have sq' : inv gY ≫ f₂ = f₁ ≫ inv gX := by
    rw [← cancel_epi gY, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
      ← Category.assoc, sq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact ⟨normalizationMap f₂ f₁ (inv gY) (inv gX) sq',
    normalizationMap_comp_normalizationMap_eq_id f₁ f₂ sq sq' (IsIso.hom_inv_id _)
      (IsIso.hom_inv_id _),
    normalizationMap_comp_normalizationMap_eq_id f₂ f₁ sq' sq (IsIso.inv_hom_id _)
      (IsIso.inv_hom_id _)⟩

end Scheme.Hom

open Scheme.Hom

variable {X Y W XW : Scheme.{u}}

/-- Mathlib's smooth base change comparison, composed with the projection to the normalization
of the base, is the canonical morphism of Tag 035J attached to the chosen cartesian square. -/
theorem normalizationPullback_comp_fst (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (w : W ⟶ Y) :
    g.normalizationPullback w ≫ pullback.fst g.fromNormalization w =
      normalizationMap g (pullback.snd g w) (pullback.fst g w) w pullback.condition :=
  normalizationMap_unique g (pullback.snd g w) (pullback.fst g w) w pullback.condition _
    (toNormalization_normalizationPullback_fst g w)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc,
      normalizationPullback_snd])

/-- **The relative normalization commutes with smooth base change**, on an arbitrary cartesian
square: for a cartesian square with `g` quasi-compact and quasi-separated, `w` smooth and
`p` quasi-compact and quasi-separated, the normalization of `W` in `XW` is the fibre product of
the normalization of `Y` in `X` with `W`, the comparison being the canonical morphism of
Tag 035J.

This is Mathlib's `IsIso (g.normalizationPullback w)`, which is the statement for the chosen
pullback, transported along the isomorphism of the source of the square with that pullback. -/
theorem isPullback_normalizationMap_of_smooth (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (w : W ⟶ Y) [Smooth w] {a : XW ⟶ X} {p : XW ⟶ W}
    [QuasiCompact p] [QuasiSeparated p] (sq : IsPullback a p g w) :
    IsPullback (normalizationMap g p a w sq.w) p.fromNormalization g.fromNormalization w := by
  -- the comparison of the arbitrary square with the chosen pullback
  have hsnd : sq.isoPullback.inv ≫ p = pullback.snd g w ≫ 𝟙 W := by
    rw [Category.comp_id, Iso.inv_comp_eq, sq.isoPullback_hom_snd]
  have hfst : sq.isoPullback.inv ≫ a = pullback.fst g w := by
    rw [Iso.inv_comp_eq, sq.isoPullback_hom_fst]
  set m := normalizationMap p (pullback.snd g w) sq.isoPullback.inv (𝟙 W) hsnd with hm
  have hmiso : IsIso m := isIso_normalizationMap p (pullback.snd g w) _ _ hsnd
  -- the chosen pullback square, with the normalization of the chosen pullback in the corner
  have hchosen : IsPullback
      (g.normalizationPullback w ≫ pullback.fst g.fromNormalization w)
      (pullback.snd g w).fromNormalization g.fromNormalization w := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (g.normalizationPullback w)) ?_ ?_
    · rw [Category.assoc, pullback.condition, ← Category.assoc, normalizationPullback_snd]
    · rfl
    · exact normalizationPullback_snd g w
  -- the two legs of that square, factored through `m`
  have hleg₁ : g.normalizationPullback w ≫ pullback.fst g.fromNormalization w =
      m ≫ normalizationMap g p a w sq.w := by
    rw [normalizationPullback_comp_fst]
    refine (normalizationMap_unique g (pullback.snd g w) (pullback.fst g w) w
      pullback.condition _ ?_ ?_).symm
    · rw [← Category.assoc, hm, toNormalization_normalizationMap, Category.assoc,
        toNormalization_normalizationMap, ← Category.assoc, hfst]
    · rw [Category.assoc, normalizationMap_fromNormalization, ← Category.assoc, hm,
        normalizationMap_fromNormalization, Category.comp_id]
  have hleg₂ : (pullback.snd g w).fromNormalization = m ≫ p.fromNormalization := by
    rw [hm, normalizationMap_fromNormalization, Category.comp_id]
  rw [hleg₁, hleg₂] at hchosen
  refine IsPullback.of_iso_pullback ⟨normalizationMap_fromNormalization g p a w sq.w⟩
    ((asIso m).symm ≪≫ hchosen.isoPullback) ?_ ?_
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hchosen.isoPullback_hom_fst,
      ← Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.id_comp]
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hchosen.isoPullback_hom_snd,
      ← Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry

end
