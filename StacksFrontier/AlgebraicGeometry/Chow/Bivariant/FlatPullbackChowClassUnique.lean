module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackChowClass

/-!
# The flat-pullback rule is a unique bivariant class (Stacks 0B78)

Let `(S, δ)` be as in Situation 02QL and let `f : X ⟶ Y` be a flat morphism of relative
dimension `r` between schemes locally of finite type over `S`. Stacks 0B78 asserts that the rule
which assigns to a morphism `g : Y' ⟶ Y` locally of finite type the flat pullback

  `(f')^* : CH_k(Y') ⟶ CH_{k+r}(X')`,  `X' = X ×_Y Y'`,

along the base change `f' : X' ⟶ Y'` of `f` is a bivariant class of degree `-r`: it satisfies the
three conditions of Stacks 0B76, so that it is an element of `A^{-r}(X ⟶ Y)`.

This file states the lemma as a proposition about the rule. A bivariant class is determined by
its cap operations, so "the rule is a bivariant class" is the assertion that exactly one element
of `A^{-r}(X ⟶ Y)` caps by it.

## Main results

* `Stacks.Chow.existsUnique_bivariantChowClass_cap_eq_flatPullbackChow` — **Stacks 0B78**: there
  is exactly one `c ∈ A^{-r}(X ⟶ Y)` (a term of `Stacks.Chow.BivariantChowClass`, whose three
  conditions use the genuine proper pushforward, flat pullback and Gysin map) whose cap
  operation on `CH_k(Y')` is `(f')^*`, read in degree `k - (-r)`.
* `Stacks.Chow.exists_bivariantChowClass_cap_heq_flatPullbackChow` — **Stacks 0B78**, the same
  existence with the degree transport removed: the cap operation is `(f')^*` landing in
  `CH_{k+r}(X')` exactly as the source writes it.
* `Stacks.Chow.existsUnique_bivariantClass_isBivariantFlatPullback` — **Stacks 0B78** for the
  bivariant classes of `Stacks.Chow.BivariantClass` at the Gysin system of the first Chern class
  of an invertible module: exactly one of them satisfies the characterization
  `Stacks.Chow.IsBivariantFlatPullback`.

## Implementation notes

Nothing is assumed. The class is `Stacks.Chow.flatPullbackBivariantChowClass`, transported from
`Stacks.Chow.flatPullbackBivariantClassOfInvertible`, whose three conditions are discharged by
Stacks 02RG (`Stacks.Chow.properPushforwardFlatPullbackBaseChange`), Stacks 02RD
(`Stacks.Chow.flatPullbackChow_comm_of_comp_eq`) and Stacks 0B71 with the identification of
Remark 0B6Y (`Stacks.Chow.gysinSystemOfInvertible_flatPullbackNaturalityAtZeroSchemeComparison`).
Flat pullback descends to Chow groups by Stacks 02S1
(`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`), and the base change of `f`
is flat of relative dimension `r` by Stacks 02NK. Uniqueness is
`Stacks.Chow.BivariantChowClass.ext`.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (r : ℕ) (hfr : AlgebraicGeometry.RelativeDimension f r)

/-- **Stacks 0B78.** Let `f : X ⟶ Y` be flat of relative dimension `r` between schemes locally of
finite type over `S`. The rule which assigns to `g : Y' ⟶ Y` the flat pullback
`(f')^* : CH_k(Y') ⟶ CH_{k+r}(X')` along the base change `f' : X' = X ×_Y Y' ⟶ Y'` of `f` is a
bivariant class of degree `-r`: there is exactly one `c ∈ A^{-r}(X ⟶ Y)` whose cap operation is
that rule, read in degree `k - (-r) = k + r`. -/
@[stacks 0B78 "the flat-pullback rule is a bivariant class of degree -r, with nothing assumed: \
exactly one element of A^{-r}(X → Y), the group of Stacks 0B76 whose three conditions use the \
genuine proper pushforward, flat pullback and Gysin map, caps by (f')^*"]
theorem existsUnique_bivariantChowClass_cap_eq_flatPullbackChow :
    ∃! c : BivariantChowClass C sX sY f hf (-(r : ℤ)),
      ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ sY) k),
        c.cap g k α =
          chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) (by ring : k + (r : ℤ) = k - -(r : ℤ))
            (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
              (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
              (relativeDimension_pullback_snd f g r hfr) k
              (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α) := by
  refine ⟨flatPullbackBivariantChowClass C sX sY f hf r hfr,
    fun g _ k α ↦ flatPullbackBivariantChowClass_cap C sX sY f hf r hfr g k α, ?_⟩
  intro d hd
  ext T g _ k α
  rw [hd g k α, flatPullbackBivariantChowClass_cap]

/-- **Stacks 0B78**, with the degree transport removed. For `f : X ⟶ Y` flat of relative
dimension `r`, there is a bivariant class `c ∈ A^{-r}(X ⟶ Y)` whose cap operation on `CH_k(Y')`
is the flat pullback `(f')^* : CH_k(Y') ⟶ CH_{k+r}(X')` along the base change of `f`, landing in
degree `k + r` exactly as in the source. The two degrees `k + r` and `k - (-r)` are equal integers
that are not the same term, so the identity is a heterogeneous equality. -/
@[stacks 0B78 "the flat-pullback rule (f')^* : CH_k(Y') → CH_{k+r}(X') is the cap operation of \
an element of A^{-r}(X → Y), with nothing assumed, read in degree k + r as the source writes it"]
theorem exists_bivariantChowClass_cap_heq_flatPullbackChow :
    ∃ c : BivariantChowClass C sX sY f hf (-(r : ℤ)),
      ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ sY) k),
        c.cap g k α ≍
          flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
            (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
            (relativeDimension_pullback_snd f g r hfr) k
            (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α :=
  ⟨flatPullbackBivariantChowClass C sX sY f hf r hfr,
    fun g _ k α ↦ flatPullbackBivariantChowClass_cap_heq C sX sY f hf r hfr g k α⟩

/-- **Stacks 0B78** for `Stacks.Chow.BivariantClass` at the Gysin system of the first Chern
class of an invertible module: exactly one bivariant class of degree `-r` for `f` caps by flat
pullback along the base change of `f`, in the sense of `Stacks.Chow.IsBivariantFlatPullback`. -/
@[stacks 0B78 "exactly one bivariant class of degree -r, at the Gysin system of the first Chern \
class, satisfies the characterization Stacks.Chow.IsBivariantFlatPullback, with nothing assumed"]
theorem existsUnique_bivariantClass_isBivariantFlatPullback :
    ∃! c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (-(r : ℤ)),
      IsBivariantFlatPullback C (gysinSystemOfInvertible C) sX sY f hf r hfr
        (flatPullbackDescends C) c :=
  ⟨flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr,
    isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr,
    fun _ hd ↦ eq_of_isBivariantFlatPullback C (gysinSystemOfInvertible C) sX sY f hf r hfr
      (flatPullbackDescends C) hd
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr)⟩

end Stacks.Chow

end
