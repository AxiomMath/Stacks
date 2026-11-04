module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningFunctorial

/-!
# The conormal sequence of a pair of formally unramified morphisms of algebraic spaces

Let `S` be a scheme and let

```
  Z --i--→ X
   \       |
    j      g
     \     ↓
      `--→ Y
```

be a commutative triangle of algebraic spaces over `S` with `i` and `j` formally unramified.
Stacks 06BE attaches to it a canonical exact sequence of `𝒪_Z`-modules

```
  𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0,
```

whose first arrow is the map of conormal modules of Stacks 060A and whose second arrow is the
canonical first arrow of Stacks 060F.  This file proves its right-hand end; the whole sequence
is `AlgebraicGeometry.Space.exists_conormalPairSequence_exact` in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceUnramifiedPairExact.lean`.

## The two arrows are the canonical ones, and nothing is quantified over

* the first arrow is `AlgebraicGeometry.Space.universalThickeningConormalMap`, the map
  `f^*𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` which Stacks 060A deduces from the canonical morphism `(f, f')` of
  universal first-order thickenings, at the square of the triangle — the one whose upper edge is
  `i`, whose lower edge is `j` and whose right edge is `g`;
* the second arrow is `AlgebraicGeometry.Space.thickeningConormalFirstMap`, the canonical first
  arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of Stacks 060F.

No statement below quantifies over a pair of morphisms forming a sequence: both arrows are
those two declarations, applied to the data of the triangle.

## How the situation is presented

As in `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningFunctorial.lean` (Stacks 060A)
and `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallyUnramified.lean`
(Stacks 060F), a universal first-order thickening presents its smaller space as a
`CategoryTheory.Subfunctor` of its ambient algebraic space, so the data are

* `hZ`, a universal first-order thickening `Z ⊂ Z'` of `Z` over `X` with structure morphism
  `p : Z' ⟶ X`, which is the datum of the conormal module `𝒞_{Z/X} = 𝒞_{Z/Z'}` of
  Stacks 0607 (2);
* `hW`, a universal first-order thickening `W ⊂ W'` of `W` over `Y` with structure morphism
  `q : W' ⟶ Y`, which is the datum of `𝒞_{Z/Y} = 𝒞_{W/W'}`;
* `f : Z ⟶ W`, the identification of the two smaller spaces, along which the left-hand term of
  the sequence is read as `f^*𝒞_{Z/Y}`, exactly as Stacks 060A reads its conormal map;
* `hsq`, commutativity of the triangle: `i ≫ g = f ≫ j`, with `i = Z.ι ≫ p.hom` and
  `j = W.ι ≫ q.hom`.

Of these, the statement below uses only `hZ`, together with `g`.

Formal unramifiedness of `i` is `hZ`: by Stacks 0606 it is equivalent to the existence of the
universal first-order thickening of `Z` over `X`, one is given, and Stacks 0609
(`AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`) returns it
from `hZ`.  Stacks 0606 is not available in this library — see the *What is not proved here*
section of `StacksFrontier/AlgebraicGeometry/Spaces/UniversalFirstOrderThickening.lean` — which is
why the thickening and not the formal unramifiedness is the hypothesis; the same choice is made
by Stacks 060A, 060E and 060F here.  Formal unramifiedness of `j` is assumed at `Z` as `hj`,
which is where it does its work: the right-hand end of the sequence needs it.

## Main results

* `AlgebraicGeometry.Space.epi_thickeningConormalFirstMap`: **Stacks 06BE, the `⟶ 0`** — the
  second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` is an epimorphism.  This is proved.  The sequence of
  Stacks 060F continues the second arrow by `i^*Ω_{X/Y} ⟶ Ω_{Z/Y}` and is exact at
  `i^*Ω_{X/Y}`; formal unramifiedness of `j` makes `Ω_{Z/Y}` a zero object by Stacks 04G9, so
  that exactness says precisely that the second arrow is an epimorphism.

## What is carried, and why

`he`, `hzero` and `h05ZA` are the hypotheses of the tagged statements this file composes, in the
shape those statements carry them, so discharging them there discharges them here with no
reformulation.

* `he : IsIso (thickeningSheafOfDifferentialsMap …)` — the isomorphism of Stacks 060E.  This is
  proved: `AlgebraicGeometry.Space.isIso_thickeningSheafOfDifferentialsMap` discharges it,
  granting the étale localization of Stacks 04CU and 060D as its own `hetale` hypothesis.  It
  is the identical carry of Stacks 060F.
* `hzero` and `h05ZA` — the composite of the two arrows of the sequence of Stacks 05ZA for
  `Z ⊂ Z'` over `Y` being zero, and exactness of that sequence at its middle term.  These are
  the two clauses that `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean`
  leaves open for Stacks 05ZA, and they are the identical carry of
  `AlgebraicGeometry.Space.thickeningConormalSequence_exact` (Stacks 060F), which is what
  consumes them here.
A fourth hypothesis, `hchart : SheafOfDifferentialsChartComparison …`, was carried here — the
chart comparison of Stacks 04CU and 04CS, the input of Stacks 04G9 that this library does not
prove — and it is **gone**.  Only the forward implication of Stacks 04G9 is used here, to make
`Ω_{Z/Y}` a zero object out of formal unramifiedness of `j`, and that implication consumes only
the `mpr` half of the comparison, which is now proved:
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified` is Stacks 04G9
forward with no hypothesis at all, and it is what the proof below calls.

## References

* [Stacks Project, Tag 06BE](https://stacks.math.columbia.edu/tag/06BE)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A), the first arrow.
* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F), the second arrow and
  the sequence `𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0` whose exactness gives the `⟶ 0`.
* [Stacks Project, Tag 067V](https://stacks.math.columbia.edu/tag/067V), the case of schemes,
  to which the source reduces this tag by étale localization.
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L), the statement for two
  immersions, to which Stacks 067V reduces.
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D) and
  [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  the source's reduction uses.
* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9), the vanishing of
  `Ω_{Z/Y}` for a formally unramified `j`.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606) and
  [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' W' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {W : Subfunctor W'.obj}
    {p : Z' ⟶ X} {q : W' ⟶ Y}

/-! ### Exactness at the right term -/

/-- **Stacks 06BE, the `⟶ 0` at the right-hand end of the sequence.**  The second arrow
`𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of the sequence — the canonical first arrow
`AlgebraicGeometry.Space.thickeningConormalFirstMap` of Stacks 060F — is an epimorphism.

This is proved, and formal unramifiedness of `j` is what proves it.  The sequence of
Stacks 060F continues that arrow by `i^*Ω_{X/Y} ⟶ Ω_{Z/Y}` and is exact at `i^*Ω_{X/Y}`, by
`AlgebraicGeometry.Space.thickeningConormalSequence_exact`; formal unramifiedness of
`j = ι ≫ p ≫ g` makes `Ω_{Z/Y}` a zero object by the forward implication of Stacks 04G9,
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`, so the third
arrow of that sequence is the zero morphism and exactness at `i^*Ω_{X/Y}` says exactly that the
second arrow is an epimorphism, by `CategoryTheory.ShortComplex.exact_iff_epi`.

The hypotheses `he`, `hzero` and `h05ZA` are the carries of Stacks 060F, passed straight
through; the module docstring says what each is and what discharges it.  Nothing of Stacks 04G9
is carried: the implication used is the one that needs no chart comparison. -/
theorem epi_thickeningConormalFirstMap (g : X ⟶ Y)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g))
    (hzero : conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (p ≫ g) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (p ≫ g) = 0)
    (h05ZA : (ShortComplex.mk _ _ hzero).Exact)
    (hj : FormallyUnramified (universalThickeningInclusion B S hS hZ ≫ p ≫ g).hom) :
    Epi (thickeningConormalFirstMap B S hS hZ g he) := by
  obtain ⟨hc, hex⟩ := thickeningConormalSequence_exact B S hS hZ g he hzero h05ZA
  have hΩ : IsZero (sheafOfDifferentials B S hS
      (universalThickeningInclusion B S hS hZ ≫ p ≫ g)) :=
    isZero_sheafOfDifferentials_of_formallyUnramified B S hS _ hj
  exact (ShortComplex.exact_iff_epi _ (hΩ.eq_of_tgt _ _)).mp hex

end AlgebraicGeometry.Space

end
