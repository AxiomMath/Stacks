module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# Flat pullback as an element of `A^{-r}(X ⟶ Y)` (Stacks 0B78)

Let `(S, δ)` be as in Situation 02QL and let `f : X ⟶ Y` be a flat morphism of relative
dimension `r` between schemes locally of finite type over `S`. The rule which assigns to a
morphism `g : Y' ⟶ Y` locally of finite type the flat pullback

  `(f')^* : CH_k(Y') ⟶ CH_{k+r}(X')`,  `X' = X ×_Y Y'`,

along the base change `f' : X' ⟶ Y'` of `f` is a bivariant class of degree `-r`, that is, an
element of the group `A^{-r}(X ⟶ Y)` of Stacks 0B76.

## Main definitions

* `Stacks.Chow.flatPullbackBivariantChowClass` — **Stacks 0B78**: the class
  `f^* ∈ A^{-r}(X ⟶ Y)`, a term of `Stacks.Chow.BivariantChowClass`, whose three conditions are
  stated with the genuine proper pushforward, flat pullback and Gysin map `i^*` of the source.

## Main results

* `Stacks.Chow.flatPullbackBivariantChowClass_cap` — its cap operation on `CH_k(Y')` is flat
  pullback along `f'`, read in degree `k - (-r) = k + r`.
* `Stacks.Chow.flatPullbackBivariantChowClass_cap_heq` — the same, with the degree transport
  removed.
* `Stacks.Chow.equivBivariantClass_flatPullbackBivariantChowClass` — under the bridge
  `Stacks.Chow.BivariantChowClass.equivBivariantClass` it is the class
  `Stacks.Chow.flatPullbackBivariantClassOfInvertible` at the Gysin system of the first Chern
  class of an invertible module.

## Implementation notes

The three conditions of Stacks 0B76 are those of
`Stacks.Chow.flatPullbackBivariantClassOfInvertible`: proper pushforward is Stacks 02RG, flat
pullback is Stacks 02RD, and the Gysin map is Stacks 0B71 with the identification of Remark 0B6Y;
flat pullback descends to Chow groups by Stacks 02S1 and the base change of `f` is flat of relative
dimension `r` by Stacks 02NK. The class here is that one transported along
`Stacks.Chow.BivariantChowClass.equivBivariantClass`, whose cap operations correspond identically.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section FlatPullbackChowClass

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (r : ℕ) (hfr : AlgebraicGeometry.RelativeDimension f r)

/-- **Stacks 0B78.** For `f : X ⟶ Y` flat of relative dimension `r` between schemes locally of
finite type over `S`, the rule which assigns to `g : Y' ⟶ Y` the flat pullback
`(f')^* : CH_k(Y') ⟶ CH_{k+r}(X ×_Y Y')` along the base change of `f` is a bivariant class of
degree `-r`, the class `f^* ∈ A^{-r}(X ⟶ Y)`. -/
@[stacks 0B78 "the flat-pullback rule as an element of A^{-r}(X → Y), the group of Stacks 0B76 \
whose three conditions use the genuine proper pushforward, flat pullback and Gysin map; its cap \
operation is flat pullback along the base change of f (flatPullbackBivariantChowClass_cap)"]
def flatPullbackBivariantChowClass : BivariantChowClass C sX sY f hf (-(r : ℤ)) :=
  BivariantChowClass.equivBivariantClass.symm
    (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr)

/-- **Stacks 0B78.** The cap operation of `f^* ∈ A^{-r}(X ⟶ Y)` on `CH_k(Y')` is flat pullback
along the base change `f' : X ×_Y Y' ⟶ Y'` of `f`, read in degree `k - (-r) = k + r`. -/
theorem flatPullbackBivariantChowClass_cap {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (flatPullbackBivariantChowClass C sX sY f hf r hfr).cap g k α =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) (by ring : k + (r : ℤ) = k - -(r : ℤ))
        (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
          (relativeDimension_pullback_snd f g r hfr) k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α) :=
  rfl

/-- The cap operation of `f^* ∈ A^{-r}(X ⟶ Y)` is flat pullback along the base change of `f`,
with the transport from degree `k + r` to degree `k - (-r)` removed. -/
theorem flatPullbackBivariantChowClass_cap_heq {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (flatPullbackBivariantChowClass C sX sY f hf r hfr).cap g k α ≍
      flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
        (relativeDimension_pullback_snd f g r hfr) k
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α :=
  flatPullbackBivariantCap_heq C sX sY f hf r hfr (flatPullbackDescends C) g k α

/-- Under the bridge `Stacks.Chow.BivariantChowClass.equivBivariantClass`, the class `f^*` is
`Stacks.Chow.flatPullbackBivariantClassOfInvertible`. -/
@[simp]
theorem equivBivariantClass_flatPullbackBivariantChowClass :
    BivariantChowClass.equivBivariantClass (flatPullbackBivariantChowClass C sX sY f hf r hfr) =
      flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr :=
  rfl

end FlatPullbackChowClass

end Stacks.Chow

end
