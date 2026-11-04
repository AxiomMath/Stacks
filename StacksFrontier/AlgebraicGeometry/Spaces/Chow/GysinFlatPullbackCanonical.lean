module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackContained
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackNonContained

/-!
# Stacks 0ER6: the Gysin homomorphism and flat pullback

In Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B`, let `(ℒ, s, i : D → X)` be as in Definition 0ER1 and form the diagram of
Remark 0ER3

```
D' --i'--> X'
|          |
g          f
|          |
v          v
D  --i-->  X
```

with `ℒ' = f^*ℒ`, `s' = f^*s` and `D' = Z(s') = X' ×_X D`.  **Stacks 0ER6**: for every
`(k + 1)`-cycle `α` on `X`,

`(i')^* f^* α = g^* i^* α`   in `CH_{k+r}(D')`.

The letter `D` is the dimension situation of Stacks 0EDT, so the vanishing locus is called `E`
below, and `E' = Z(f^*s)`.

## The objects

* `i^*` and `(i')^*` are the Gysin maps on cycles of Stacks 0ER1,
  `AlgebraicGeometry.Space.gysinCycleMap` at the constructed component rules
  `AlgebraicGeometry.Space.sectionGysinRule` of `(ℒ, s)` and of `(f^*ℒ, f^*s)`
  (`f^*ℒ = AlgebraicGeometry.Space.pullbackSheaf`, the inverse image of Stacks 03LU, and
  `f^*s = AlgebraicGeometry.Space.pullbackGlobalSection`); these are the maps Stacks 0ERA descends
  to Chow groups.
* `E' = Z(f^*s)` is the vanishing locus of the pulled-back section, which is the inverse image
  `f^{-1}(E)` (`AlgebraicGeometry.Space.pullbackVanishingLocus_eq_preimage`, from
  `AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage`); `g : E' ⟶ E` is the projection
  (`AlgebraicGeometry.Space.pullbackVanishingLocusProjection`) and the square is cartesian
  (`AlgebraicGeometry.Space.isPullback_pullbackVanishingLocusProjection`).  Flatness of `g` and its
  relative dimension `r` are derived by base change, Stacks 0EPD
  (`AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection`).
* `f^*`, `g^*` are the flat pullbacks of cycles of Stacks 0EP8,
  `AlgebraicGeometry.Space.flatPullbackMap`.
* `CH_{k+r}(E')` is `AlgebraicGeometry.Space.chowGroupCanonical`, the Chow group of Stacks 0EQ6
  with `div(f_j)` read at the canonical embeddings of Stacks 0ENK.

## The proof

The source's.  Both sides are pushed forward to `X'` along `i'`; there `i'_*(i')^*` is the cap
product of Stacks 0EQJ at the Gysin rule of `(f^*ℒ, f^*s)`
(`AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap`), and
`i'_* g^* = f^* i_*` by Stacks 0EPD.  The difference is the commutator of `f^*` with the cap
product, which by Remark 0EQ8 is the locally finite sum over the integral closed subspaces
`W ⊆ X` occurring in `α` of `α_W` times the defect at `W`
(`isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_firstChernCapCycleMap_sub`; this
and the other unqualified names below are in `AlgebraicGeometry.Space`).

* `W ⊄ D`: the defect vanishes as a cycle
  (`AlgebraicGeometry.Space.flatChernDefect_gysinChernRule_eq_zero_of_not_le`) -- Stacks 0EQQ for
  `h : f^{-1}(W) ⟶ W` applied to `s|_W`, with the divisors of the restricted sections being the
  cycles `[E ∩ W]_k` and `[E' ∩ W'_j]_{k+r}` of clause (1)(a) of Stacks 0ER1.
* `W ⊆ D`: the defect is rationally equivalent to zero inside `f^{-1}(W) ⊆ E'`
  (`isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_gysin_of_le`)
  -- Stacks 0EQR at one integral closed subspace, the Gysin rule differing from the canonical
  cap product by principal divisors.

All carriers lie in `|E'|`, so the rational equivalence on `X'` descends to `E'` (the descent
lemma `isRationallyEquivalentToZeroCanonical_of_…_closedPushforward` of the module
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical`).
Nothing is assumed.

## Main results

* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap`: **Stacks 0ER6.**
* `AlgebraicGeometry.Space.sectionGysinChowGroupMap_flatPullbackChowMapCanonical`: the same
  identity read through the maps on Chow groups of Stacks 0ERA and Stacks 0EQB.

## References

* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

/-- **Stacks 0ER6.**  In Situation 0EDT let `f : X' ⟶ X` be a morphism over `B` of good algebraic
spaces which is flat of relative dimension `r`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1
(`ℒ` invertible, `s ∈ Γ(X, ℒ)`, `E = Z(s)`), and form the diagram of Remark 0ER3: `ℒ' = f^*ℒ`,
`s' = f^*s`, `E' = Z(s') = X' ×_X E` with `i' : E' → X'` and the projection `g : E' ⟶ E`, which is
flat of relative dimension `r`.  Then for every `(k + 1)`-cycle `α` on `X`

`(i')^* f^* α = g^* i^* α`   in `CH_{k+r}(E')`.

Here `i^*`, `(i')^*` are the Gysin maps on cycles of Stacks 0ER1 at their constructed component
rules, `f^*`, `g^*` the flat pullbacks of cycles of Stacks 0EP8, and `CH_{k+r}(E')` the Chow
group of Stacks 0EQ6 (`div(f_j)` at the canonical embeddings of Stacks 0ENK). -/
@[stacks 0ER6 "(i')^* f^* α = g^* i^* α in CH_{k+r}(D') for f : X' → X flat of relative dimension \
r between good spaces over B, (L, s, i : D → X) as in 0ER1 and D' = Z(f^*s) = X' ×_X D as in 0ER3 \
(g : D' → D flat of relative dimension r by base change); the Gysin maps of 0ER1 at their \
constructed rules (sectionGysinRule), the flat pullbacks of cycles of 0EP8, CH = \
chowGroupCanonical of 0EQ6. Unconditional: the case W ⊄ D is 0EQQ for f^{-1}(W) → W (an identity \
of cycles), the case W ⊆ D is 0EQR at one integral closed subspace, reassembled by 0EQ8"]
theorem chowClassCanonical_gysinCycleMap_flatPullbackMap (α : CycleGroup D p (k + 1)) :
    chowClassCanonical.{u + 1} D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) (k + (r : ℤ))
        (gysinCycleMap D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
          (isGood_vanishingLocus D p' hp' _ _) (k + (r : ℤ))
          (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s) (k + (r : ℤ))
            (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL))
          (flatPullbackMap D p' hp' p hp f.hom hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
            (by ring) α)) =
      chowClassCanonical.{u + 1} D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) (k + (r : ℤ))
        (flatPullbackMap D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L s)
          (pullbackVanishingLocusProjection D p hp p' hp' f L s hL)
          (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase) r
          (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
            hfbase r hflat hr hL).1
          (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
            hfbase r hflat hr hL).2 k (k + (r : ℤ)) rfl
          (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
            (sectionGysinRule D p hp L s k hL) α)) :=
  chowClassCanonical_gysinCycleMap_flatPullbackMap_of_defect D p hp p' hp' f hfbase r hflat hr L s
    hL k (fun W hW hWE => flatChernDefect_gysinChernRule_eq_zero_of_not_le D p hp p' hp' f hfbase
      r hflat hr L s hL k W hW hWE)
    (fun W hW hWE a => isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_gysin_of_le
      D p hp p' hp' f hfbase r hflat hr L s hL k W hW hWE a) α

/-- **Stacks 0ER6, on Chow groups.**  The identity of Stacks 0ER6 read through the Gysin
homomorphisms `i^* : CH_{k+1}(X) ⟶ CH_k(E)` and `(i')^* : CH_{k+r+1}(X') ⟶ CH_{k+r}(E')` of
Stacks 0ERA and the flat pullbacks on Chow groups of Stacks 0EQB:
`(i')^*(f^*[α]) = g^*(i^*[α])`. -/
theorem sectionGysinChowGroupMap_flatPullbackChowMapCanonical (α : CycleGroup D p (k + 1)) :
    sectionGysinChowGroupMap D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)
        (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) (k + (r : ℤ))
        (flatPullbackChowMapCanonical.{u + 1} D p' hp' p hp f.hom hfbase r hflat hr (k + 1)
          (k + (r : ℤ) + 1) (by ring) (chowClassCanonical.{u + 1} D p hp (k + 1) α)) =
      flatPullbackChowMapCanonical.{u + 1} D
        ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s)
        (pullbackVanishingLocusProjection D p hp p' hp' f L s hL)
        (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase) r
        (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
          hfbase r hflat hr hL).1
        (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
          hfbase r hflat hr hL).2 k (k + (r : ℤ)) rfl
        (sectionGysinChowGroupMap D p hp L s hL k (chowClassCanonical.{u + 1} D p hp (k + 1) α)) :=
  chowClassCanonical_gysinCycleMap_flatPullbackMap D p hp p' hp' f hfbase r hflat hr L s hL k α

end AlgebraicGeometry.Space

end
