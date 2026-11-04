module

public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal

/-!
# Transitivity of universal first-order thickenings

Let `Z --i--→ Y --p--→ X` be morphisms of schemes, let `Z ⊂ Z'` be a universal first-order
thickening of `Z` over `X` and let `Y ⊂ Y'` be one of `Y` over `X`. The canonical morphism of
[Stacks Project, Tag 04F7] applied to the square
```
Z --i≫p--→ X
|           |
i           𝟙
↓           ↓
Y --p----→ X
```
is a morphism `h : Z' ⟶ Y'`, and the fibre product `Y ×_{Y'} Z'` — the base change of the
thickening `Y ⊂ Y'` along `h` — is a universal first-order thickening of `Z` over `Y`. This is
part (1) of [Stacks Project, Tag 06AE].

Everything is stated for *given* universal first-order thickenings of `i ≫ p` and of `p`, rather
than for the chosen ones of [Stacks Project, Tag 04F3], so no hypothesis that `i` or `p` is
formally unramified is needed; the statements specialize to the chosen ones at
`Stacks.Thickenings.universalFirstOrderThickening`.

## Main definitions

* `Stacks.Thickenings.transitivityMap` is the morphism `Z' ⟶ Y'`.
* `Stacks.Thickenings.relativeAmbient`, `Stacks.Thickenings.relativeInclusion` and
  `Stacks.Thickenings.relativeToBase` are the fibre product `Y ×_{Y'} Z'`, the inclusion of `Z`
  into it, and its structure morphism to `Y`.
* `Stacks.Thickenings.relativeThickening` packages them as a
  `Stacks.Thickenings.UniversalFirstOrderThickening` of `i`.

## Main results

* `Stacks.Thickenings.IsFirstOrderThickening.of_comp_mono`: a factorization of a first-order
  thickening through a monomorphism has first-order-thickening first factor.
* `Stacks.Thickenings.isUniversal_relative` is part (1) of [Stacks Project, Tag 06AE]: the fibre
  product `Y ×_{Y'} Z'` is a universal first-order thickening of `Z` over `Y`.

## References

* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE)
* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-! ### First-order thickenings and factorizations -/

/-- **A factorization of a first-order thickening through a monomorphism.** If `a ≫ b` is a
first-order thickening and `b` is a monomorphism, then `a` is a first-order thickening. -/
theorem IsFirstOrderThickening.of_comp_mono {Z P Z' : Scheme.{u}} (a : Z ⟶ P) (b : P ⟶ Z')
    [Mono b] (h : IsFirstOrderThickening (a ≫ b)) : IsFirstOrderThickening a :=
  isFirstOrderThickening_of_isPullback
    (IsPullback.of_vert_isIso_mono (fst := a) (snd := 𝟙 Z) (f := b) (g := a ≫ b)
      (CommSq.mk (Category.id_comp (a ≫ b)).symm)) h

/-! ### The canonical morphism of thickenings over a common base -/

variable {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ X)

/-- The commutative square over `X` relating `i ≫ p` to `p`, with vertical maps `i` and `𝟙 X`. -/
theorem transitivity_comm : (i ≫ p) ≫ 𝟙 X = i ≫ p := Category.comp_id _

/-- **The morphism `Z' ⟶ Y'` of part (1) of [Stacks Project, Tag 06AE].** For a universal
first-order thickening `Z ⊂ Z'` of `Z` over `X` and one `Y ⊂ Y'` of `Y` over `X`, this is the
canonical morphism of [Stacks Project, Tag 04F7] for the square over `X` with vertical maps `i`
and `𝟙 X`. -/
@[stacks 06AE "part (1): the morphism Z' ⟶ Y'"]
noncomputable def transitivityMap (tZ : UniversalFirstOrderThickening (i ≫ p))
    (tY : UniversalFirstOrderThickening p) : tZ.ambient ⟶ tY.ambient :=
  universalFirstOrderThickeningMap tZ tY i (𝟙 X) (transitivity_comm i p)

/-- `Stacks.Thickenings.transitivityMap` restricts to `i` on the closed subschemes. -/
theorem inclusion_comp_transitivityMap (tZ : UniversalFirstOrderThickening (i ≫ p))
    (tY : UniversalFirstOrderThickening p) :
    i ≫ tY.inclusion = tZ.inclusion ≫ transitivityMap i p tZ tY :=
  (universalFirstOrderThickeningMap_inclusion tZ tY i (𝟙 X) (transitivity_comm i p)).symm

/-- `Stacks.Thickenings.transitivityMap` is a morphism over `X`. -/
theorem transitivityMap_comp_toBase (tZ : UniversalFirstOrderThickening (i ≫ p))
    (tY : UniversalFirstOrderThickening p) :
    transitivityMap i p tZ tY ≫ tY.toBase = tZ.toBase := by
  rw [transitivityMap,
    universalFirstOrderThickeningMap_toBase tZ tY i (𝟙 X) (transitivity_comm i p),
    Category.comp_id]

/-! ### The relative thickening `Y ×_{Y'} Z'` -/

variable (tZ : UniversalFirstOrderThickening (i ≫ p)) (tY : UniversalFirstOrderThickening p)

/-- The fibre product `Y ×_{Y'} Z'`, the ambient scheme of the universal first-order thickening
of `Z` over `Y` produced by part (1) of [Stacks Project, Tag 06AE]. -/
noncomputable abbrev relativeAmbient : Scheme.{u} :=
  pullback tY.inclusion (transitivityMap i p tZ tY)

/-- The inclusion of `Z` into `Y ×_{Y'} Z'`, induced by `i : Z ⟶ Y` and the inclusion of `Z`
into `Z'`. -/
noncomputable def relativeInclusion : Z ⟶ relativeAmbient i p tZ tY :=
  pullback.lift i tZ.inclusion (inclusion_comp_transitivityMap i p tZ tY)

/-- The structure morphism `Y ×_{Y'} Z' ⟶ Y`, the first projection. -/
noncomputable abbrev relativeToBase : relativeAmbient i p tZ tY ⟶ Y :=
  pullback.fst tY.inclusion (transitivityMap i p tZ tY)

/-- The inclusion of `Z` into `Y ×_{Y'} Z'` followed by the structure morphism is `i`. -/
theorem relativeInclusion_comp_fst :
    relativeInclusion i p tZ tY ≫ relativeToBase i p tZ tY = i :=
  pullback.lift_fst _ _ _

/-- The inclusion of `Z` into `Y ×_{Y'} Z'` followed by the projection to `Z'` is the inclusion
of `Z` into `Z'`. -/
theorem relativeInclusion_comp_snd :
    relativeInclusion i p tZ tY ≫ pullback.snd tY.inclusion (transitivityMap i p tZ tY) =
      tZ.inclusion :=
  pullback.lift_snd _ _ _

/-- The second projection `Y ×_{Y'} Z' ⟶ Z'` is a first-order thickening. -/
theorem isFirstOrderThickening_relative_snd :
    IsFirstOrderThickening (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) :=
  isFirstOrderThickening_of_isPullback
    (IsPullback.of_hasPullback tY.inclusion (transitivityMap i p tZ tY)).flip
    tY.isUniversal.isFirstOrderThickening

/-- The second projection `Y ×_{Y'} Z' ⟶ Z'` carries the structure morphism of `Z'` over `X`
back to the structure morphism of the fibre product over `Y` followed by `p`. -/
theorem snd_comp_toBase :
    pullback.snd tY.inclusion (transitivityMap i p tZ tY) ≫ tZ.toBase =
      relativeToBase i p tZ tY ≫ p := by
  rw [← transitivityMap_comp_toBase i p tZ tY, ← Category.assoc, ← pullback.condition,
    Category.assoc, tY.isUniversal.inclusion_toBase]

/-- **Part (1) of [Stacks Project, Tag 06AE].** Let `Z --i--→ Y --p--→ X` be morphisms of
schemes, let `Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` and `Y ⊂ Y'` one of
`Y` over `X`. Then the fibre product `Y ×_{Y'} Z'` along the morphism
`Stacks.Thickenings.transitivityMap` is a universal first-order thickening of `Z` over `Y`. -/
@[stacks 06AE "part (1): Y ×_{Y'} Z' is the universal first-order thickening of Z over Y"]
theorem isUniversal_relative :
    IsUniversalFirstOrderThickening i (relativeInclusion i p tZ tY)
      (relativeToBase i p tZ tY) := by
  have : IsClosedImmersion (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) :=
    (isFirstOrderThickening_relative_snd i p tZ tY).1
  refine ⟨?_, relativeInclusion_comp_fst i p tZ tY, ?_⟩
  · refine IsFirstOrderThickening.of_comp_mono _
      (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) ?_
    rw [relativeInclusion_comp_snd i p tZ tY]
    exact tZ.isUniversal.isFirstOrderThickening
  · intro T T' jT hjT aT bT hcomm
    obtain ⟨c, ⟨hc₁, hc₂⟩, hcu⟩ :=
      tZ.isUniversal.existsUnique_lift jT hjT aT (bT ≫ p) (by rw [← Category.assoc, hcomm,
        Category.assoc])
    have hcompat : bT ≫ tY.inclusion = c ≫ transitivityMap i p tZ tY := by
      refine (tY.isUniversal.existsUnique_lift jT hjT (aT ≫ i) (bT ≫ p)
        (by rw [← Category.assoc, hcomm])).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [← Category.assoc, hcomm]
      · rw [Category.assoc, tY.isUniversal.inclusion_toBase]
      · rw [← Category.assoc, hc₁, Category.assoc,
          ← inclusion_comp_transitivityMap i p tZ tY, Category.assoc]
      · rw [Category.assoc, transitivityMap_comp_toBase i p tZ tY, hc₂]
    refine ⟨pullback.lift bT c hcompat, ⟨?_, pullback.lift_fst _ _ _⟩, ?_⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, Category.assoc,
          relativeInclusion_comp_fst i p tZ tY, hcomm]
      · rw [Category.assoc, pullback.lift_snd, Category.assoc,
          relativeInclusion_comp_snd i p tZ tY, hc₁]
    · intro a'' ⟨ha''₁, ha''₂⟩
      refine pullback.hom_ext (by rw [pullback.lift_fst]; exact ha''₂) ?_
      rw [pullback.lift_snd]
      refine hcu _ ⟨?_, ?_⟩
      · rw [← Category.assoc, ha''₁, Category.assoc, relativeInclusion_comp_snd i p tZ tY]
      · rw [Category.assoc, snd_comp_toBase i p tZ tY, ← Category.assoc, ha''₂]

/-- The inclusion of `Z` into `Y ×_{Y'} Z'` is a closed immersion. -/
instance isClosedImmersion_relativeInclusion :
    IsClosedImmersion (relativeInclusion i p tZ tY) :=
  (isUniversal_relative i p tZ tY).isFirstOrderThickening.1

/-- The universal first-order thickening of `Z` over `Y` given by part (1) of
[Stacks Project, Tag 06AE], packaged as a
`Stacks.Thickenings.UniversalFirstOrderThickening`. -/
noncomputable def relativeThickening : UniversalFirstOrderThickening i where
  ambient := relativeAmbient i p tZ tY
  inclusion := relativeInclusion i p tZ tY
  toBase := relativeToBase i p tZ tY
  isUniversal := isUniversal_relative i p tZ tY

end Stacks.Thickenings

end
