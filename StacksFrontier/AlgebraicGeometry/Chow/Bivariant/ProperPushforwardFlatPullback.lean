module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardClass
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeUnconditional

/-!
# The flat-pullback axiom of a proper pushforward of a bivariant Chow class

Let `f : X ⟶ Y` be proper, `g : Y ⟶ Z` locally of finite type, and let `c ∈ A^p(X ⟶ Z)` be a
bivariant class for the composite. Stacks 0EPK asserts that the rule

  `α ↦ f'_*(c ∩ α)`,

where `f' : T ×_Z X ⟶ T ×_Z Y` is the base change of `f` along a test scheme `t : T ⟶ Z`, is a
bivariant class `f_* ∘ c ∈ A^p(Y ⟶ Z)`. The rule itself, its uniqueness, its additivity and the
proper-pushforward axiom of Stacks 0B76 for it are in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward`. This file adds the
**flat-pullback axiom**, which is the part of the source proof carried by Stacks 02RG.

## Main results

* `Stacks.Chow.bivariantProperPushforwardCap_flat_naturality_of_factors` — **the
  flat-pullback axiom of
  Stacks 0B76 for the rule of Stacks 0EPK**, in the shape the field of
  `Stacks.Chow.BivariantClass` asks for.

## Implementation notes

### Why this is a separate module

The axiom needs Stacks 02RG on Chow groups, and
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChange` imports
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing`, which imports
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward`. Stating the axiom beside the
rule would therefore be an import cycle; it is stated here, downstream of both.

### How the axiom is proved

Two steps, in the cartesian square of
`Stacks.Chow.isPullback_bivariantPushforwardBaseChange_baseChange`:

  `T' ×_Z X --> T ×_Z X`
  `|  f'_{T'}      |  f'_T`
  `T' ×_Z Y --> T ×_Z Y`

whose horizontal legs are the base-change maps of the test schemes, the right-hand vertical leg
is proper and the bottom one is flat of relative dimension `r`.

1. The flat axiom of `c` itself, for the base-change map `T' ×_Z X ⟶ T ×_Z X` of the test schemes
   along `f ≫ g`, commutes cap-with-`c` past flat pullback. Its relative-dimension side condition
   is *not* assumed: `AlgebraicGeometry.RelativeDimension.of_isPullback`, which is Stacks 02NK,
   transports the relative dimension of `h` to that base change.
2. Stacks 02RG in the square above then commutes the flat pullback past the proper pushforward
   along the base change of `f`. This is
   `Stacks.Chow.flatPullbackChow_properChowPushforward_unconditional`, which holds for an
   arbitrary class and an arbitrary cartesian square with every side condition discharged, so
   nothing is carried beyond properness of the right leg and flatness of the bottom one — both of
   which the square supplies.

The degrees are `(k + r) - p` on the left and `(k - p) + r` on the right, the same integer written
two ways, which is why the conclusion is an `HEq` and why the first step is transported with
`Stacks.Chow.heq_map_index`.

### Where the Gysin axiom is

The third axiom of Stacks 0B76 for this rule, the **Gysin** axiom, is
`Stacks.Chow.bivariantProperPushforwardCap_gysin_naturality_of_isNatural` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin`, which together with this
file and `Stacks.Chow.bivariantProperPushforwardCap_proper_naturality` completes the three and
assembles the class, `Stacks.Chow.bivariantProperPushforwardOfNaturality`. It cannot be stated
here: it needs
the identification of the base change of a zero scheme along `f ≫ g`, and that module is
downstream of this one.

Stacks 02TA for the base change of `f` does not need the integral-component hypothesis
`Stacks.Chow.GysinCompatibleWithPushforward`:
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible` of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible` takes no such argument
(despite its suffix; the conditional form is the separate
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward`), and the Gysin axiom is
proved from it through
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward`. What that axiom does carry
is two cases of Stacks 02TA for the *Gysin system*, which are properties of that axiomatised datum
rather than statements of the Stacks Project; both are theorems for the canonical Gysin system,
and the full statement of Stacks 0EPK is
`Stacks.Chow.existsUnique_canonicalBivariantProperPushforward`.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (hpp : ProperPushforwardDescends C) (p : ℤ)
  (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) p)

/-- **Stacks 0EPK.** The flat-pullback axiom of Stacks 0B76 for the rule of Stacks 0EPK: the cap
operation `α ↦ f'_*(c ∩ α)` commutes with flat pullback of fixed relative dimension along a
morphism of test schemes.

The degrees are `(k + r) - p` on the left and `(k - p) + r` on the right, the same integer written
two ways, which is why the conclusion is an `HEq`. -/
@[stacks 0EPK "the flat-pullback axiom of the pushed-forward class"]
theorem bivariantProperPushforwardCap_flat_naturality_of_factors {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (hr' : letI : LocallyOfFiniteType h' :=
        MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
      AlgebraicGeometry.RelativeDimension h' r)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sZ) (t ≫ sZ) h
      (by simp [Category.assoc]) r hr k)
    (hfac' : letI : LocallyOfFiniteType h' :=
          MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
        letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
      FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst g (h ≫ t) ≫ sY)
        (pullback.fst g t ≫ sY) h' (by rw [← Category.assoc, hfst]) r hr' (k - p))
    (α : chowGroup C (t ≫ sZ) k) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c (h ≫ t) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) r hr k
          hfac α) ≍
      flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
        (bivariantProperPushforwardCap C G sX sY sZ f g hf hg hpp p c t k α) := by
  let : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  let : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  -- The base-change map of the test schemes along `f ≫ g`, and its cartesian squares.
  set hX : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t :=
    bivariantBaseChangeMap (f ≫ g) t h with hXdef
  have hXfst : hX ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t) := by
    rw [hXdef, pullbackMap_fst, Category.comp_id]
  have hXsq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) hX h (pullback.snd (f ≫ g) t) :=
    isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hXft : LocallyOfFiniteType hX :=
    MorphismProperty.of_isPullback hXsq (P := @LocallyOfFiniteType) inferInstance
  have hXfl : Flat hX := MorphismProperty.of_isPullback hXsq (P := @Flat) inferInstance
  -- Stacks 02NK: the base change of `h` along `f ≫ g` again has relative dimension `r`.
  have hXr : AlgebraicGeometry.RelativeDimension hX r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hXsq hr
  -- The square in which Stacks 02RG is invoked.
  have hsquare : IsPullback hX (bivariantPushforwardBaseChange f g (h ≫ t))
      (bivariantPushforwardBaseChange f g t) h' :=
    isPullback_bivariantPushforwardBaseChange_baseChange f g t h h' sq hfst
  have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
  -- Step 1: the flat axiom of `c` itself, along the base-change map of the test schemes.
  have hc := c.flat_naturality t h r hr hX hXsq hXfst k hXr hfac
    (flatPullbackDescends C _ _ hX (by rw [← Category.assoc, hXfst]) r hXr (k - p)) α
  rw [bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply]
  refine HEq.trans (heq_map_index hidx hc
    (fun n x => properChowPushforward C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
      (pullback.fst g (h ≫ t) ≫ sY) (bivariantPushforwardBaseChange f g (h ≫ t))
      (bivariantPushforwardBaseChange_comp_structure hf g (h ≫ t)) n (hpp _ _ _ _ _) x))
    (heq_of_eq ?_)
  -- Step 2: Stacks 02RG, with no side condition assumed, in that square.
  exact (flatPullbackChow_properChowPushforward_unconditional C
    (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst g t ≫ sY)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst g (h ≫ t) ≫ sY)
    (bivariantPushforwardBaseChange f g t) h' hX (bivariantPushforwardBaseChange f g (h ≫ t))
    hsquare (bivariantPushforwardBaseChange_comp_structure hf g t)
    (by rw [← Category.assoc, hfst]) (by rw [← Category.assoc, hXfst]) r hr' (k - p)
    (c.cap t k α)).symm

end Stacks.Chow

end
