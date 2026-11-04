module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
import StacksCore.Tactic.StacksAttribute

/-!
# The right-hand end of the differential sequence of a formally unramified morphism

Let `h : Z ⟶ X` be a formally unramified morphism of schemes over `p : X ⟶ S`.
[Stacks, Tag 04FC] asserts that there is a canonical exact sequence

`𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0`

of `𝒪_Z`-modules, whose first arrow is induced by the universal derivation `d_{Z'/S}` on the
universal first-order thickening `Z'` of `Z` over `X`. This file proves the right-hand end: the
canonical map `h^*Ω_{X/S} ⟶ Ω_{Z/S}` of [Stacks, Tag 01UV] is an epimorphism, so the sequence
does end in zero.

## Main results

* `Stacks.ConormalSequenceRight.epi_relativeDifferentialsMap_of_isZero_relativeDifferentials`:
  the canonical map `h^*Ω_{X/S} ⟶ Ω_{Z/S}` is an epimorphism as soon as `Ω_{Z/X}` is a zero
  object.
* `Stacks.ConormalSequenceRight.epi_relativeDifferentialsMap_of_formallyUnramified`: the same
  for a formally unramified `h`, which is the hypothesis [Stacks, Tag 04FC] states it under.
  This is the assertion labelled *exactness at the right term*.

## Route

The source proves this through the universal first-order thickening: `h` factors as a closed
immersion `i : Z ⟶ Z'` followed by `h' : Z' ⟶ X`, the map `h^*Ω_{X/S} ⟶ i^*Ω_{Z'/S}` is an
isomorphism by [Stacks, Tag 04FB] — the morphism that tag is about is
`AlgebraicGeometry.Scheme.Hom.thickeningRelativeDifferentialsMap` — and `i^*Ω_{Z'/S} ⟶ Ω_{Z/S}`
is an epimorphism by [Stacks, Tag 01UZ],
`Stacks.ConormalSequenceRight.differentialsMapOver_epi`.

That route is not taken here, and nothing below depends on [Stacks, Tag 04FB]. The proof is the
shorter one, and it uses no thickening at all. The fundamental exact
sequence of the composable pair `Z ⟶ X ⟶ S`, which is [Stacks, Tag 01UX] in the form
`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_exact`, reads

`h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ Ω_{Z/X} ⟶ 0`

and is exact at `Ω_{Z/S}`. A formally unramified morphism has `Ω_{Z/X} = 0`, by
`AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified`
([Stacks, Tag 02G4]), so the second map of that sequence is the zero morphism; exactness of a
short complex whose right-hand map vanishes is epimorphy of its left-hand map, which is
`CategoryTheory.ShortComplex.exact_iff_epi`.

Only vanishing of `Ω_{Z/X}` is used, so the statement is proved at that hypothesis before being
specialized to the one [Stacks, Tag 04FC] states. Neither the universal first-order thickening
nor the conormal sheaf is mentioned by either statement, which is why the sequence's first arrow
plays no part.

## Vocabulary

`Ω_{X/S}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials p`, and the second arrow
`h^*Ω_{X/S} ⟶ Ω_{Z/S}` of the sequence is the canonical map of [Stacks, Tag 01UV],
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap`. The two arguments beyond `h`, `p` and
`h ≫ p` are the base morphism of the commutative square and the proof that it commutes, and by
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_eq_of_comm` the map depends on neither,
so the choice `(𝟙 S, by simp)` made below is not a restriction.

## What is not done here

[Stacks, Tag 04FC] carries three assertions and this file discharges the last two of them.

* **The first arrow is not constructed here**, and neither is exactness at the middle term.
  Both are in `StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.FormallyUnramifiedConormal`,
  as `Stacks.ConormalSequenceRight.universalConormalDifferential` and
  `Stacks.ConormalSequenceRight.universalConormalShortComplex_exact`. That module does take the
  route through the universal first-order thickening described above: the first arrow
  `𝒞_{Z/Z'} ⟶ i^*Ω_{Z'/S}` of [Stacks, Tag 01UZ] for the closed immersion `i : Z ⟶ Z'`, which
  is `Stacks.ConormalSequenceRight.conormalDifferential`, with its target moved onto
  `h^*Ω_{X/S}` by [Stacks, Tag 04FB].
* **The epimorphism is not identified with a cokernel or with local surjectivity.** Epimorphy
  is inherited from [Stacks, Tag 01UX], which gives it by left-cancellation; no local preimage
  of a section of `Ω_{Z/S}` is produced.

## References

* [Stacks Project, Tag 04FC](https://stacks.math.columbia.edu/tag/04FC)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX), the fundamental exact
  sequence of a composable pair, which is the whole input.
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ConormalSequenceRight

variable {Z X S : Scheme.{u}}

/-- **The canonical map `h^*Ω_{X/S} ⟶ Ω_{Z/S}` is an epimorphism** whenever the sheaf of
relative differentials `Ω_{Z/X}` of `h : Z ⟶ X` is a zero object.

The fundamental exact sequence `h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ Ω_{Z/X} ⟶ 0` of [Stacks, Tag 01UX] is
exact at `Ω_{Z/S}`, and its right-hand map is zero because its target is, so its left-hand map
is an epimorphism. -/
theorem epi_relativeDifferentialsMap_of_isZero_relativeDifferentials (h : Z ⟶ X) (p : X ⟶ S)
    (hz : IsZero (Scheme.Hom.relativeDifferentials h)) :
    Epi (Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp)) := by
  obtain ⟨hzero, hexact⟩ := Scheme.Hom.toRelativeDifferentials_exact h p
  exact (ShortComplex.exact_iff_epi _ (hz.eq_zero_of_tgt _)).mp hexact

/-- **[Stacks, Tag 04FC], exactness at the right term.** For a formally unramified morphism
`h : Z ⟶ X` of schemes over `S`, the canonical map `h^*Ω_{X/S} ⟶ Ω_{Z/S}` of
[Stacks, Tag 01UV] is an epimorphism, so the differential sequence of `h` ends in zero.

A formally unramified morphism has `Ω_{Z/X} = 0` by [Stacks, Tag 02G4], so this is
`epi_relativeDifferentialsMap_of_isZero_relativeDifferentials`. -/
@[stacks 04FC "exactness at the right term", instance]
theorem epi_relativeDifferentialsMap_of_formallyUnramified (h : Z ⟶ X) [FormallyUnramified h]
    (p : X ⟶ S) :
    Epi (Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp)) :=
  epi_relativeDifferentialsMap_of_isZero_relativeDifferentials h p
    (Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified h)

/-! ### The second arrow of the sequence

[Stacks, Tag 04FC] does not construct the second arrow of its sequence: it is the canonical map
of [Stacks, Tag 01UV] for the commutative square whose base morphism is the identity, exactly as
in [Stacks, Tag 01UZ]. The registration below records that declaration under this label, which
is the move `StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic` already makes for the
second arrow of [Stacks, Tag 01UZ]. -/

add_to_stacks 04FC "the second arrow"
  AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap

/-! ### Faithfulness

One `example` per discharged label, stating the assertion over library names. The statement
of [Stacks, Tag 04FC] writes the second arrow as the canonical map of Tag 01UV and the sheaves of
differentials as the modules of differentials of Tag 08RM of the structure maps of Tag 01SA; the
library names are `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` and
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, as recorded in
`StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic`. -/

/-- `04FC "the second arrow"`: the second arrow of the sequence is the canonical map of
[Stacks, Tag 01UV] for the square over the identity of `S`. -/
example (h : Z ⟶ X) (p : X ⟶ S) :
    (Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials p) ⟶
      Scheme.Hom.relativeDifferentials (h ≫ p) :=
  Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp)

/-- `04FC "exactness at the right term"`: for a formally unramified `h`, the canonical map from
the pulled-back relative differentials of `X` to the relative differentials of `Z` is an
epimorphism. -/
example (h : Z ⟶ X) [FormallyUnramified h] (p : X ⟶ S) :
    Epi (Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp)) :=
  epi_relativeDifferentialsMap_of_formallyUnramified h p

end Stacks.ConormalSequenceRight

end
