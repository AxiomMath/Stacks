module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Blowup squares

A *blowup square* is the cartesian square whose lower-right corner is a scheme `X`, whose
lower-left corner is a finitely presented closed subscheme `Z ⊆ X`, whose upper-right corner is
the blowup of `X` in `Z`, and whose upper-left corner is the exceptional divisor, that is the
scheme-theoretic inverse image of `Z` in the blowup.

All four corners and all four arrows are determined by the base `X` together with the
quasi-coherent ideal sheaf cutting out `Z`, so `AlgebraicGeometry.BlowUpSquare` records only
that data, plus the finite presentation of the closed immersion of the centre. The square is
cartesian for free: the upper-left corner is an inverse-image closed subscheme, and such a
subscheme is canonically the fibre product of the two morphisms it sits over.

## Main definitions

* `AlgebraicGeometry.BlowUpSquare` is the data determining a blowup square.
* `AlgebraicGeometry.BlowUpSquare.center`, `AlgebraicGeometry.BlowUpSquare.blownUp` and
  `AlgebraicGeometry.BlowUpSquare.exceptionalDivisor` are the three corners other than the base.
* `AlgebraicGeometry.BlowUpSquare.centerInclusion`,
  `AlgebraicGeometry.BlowUpSquare.blowUpMorphism`,
  `AlgebraicGeometry.BlowUpSquare.exceptionalInclusion` and
  `AlgebraicGeometry.BlowUpSquare.exceptionalProjection` are the four arrows.

## Main results

* `AlgebraicGeometry.BlowUpSquare.isPullback` is the displayed square of the source: it commutes
  and it is cartesian.

## Implementation notes

The blowup and the exceptional divisor are `AlgebraicGeometry.blowUp` and
`AlgebraicGeometry.exceptionalDivisor`, the relative `Proj` of the Rees algebra of the centre
and the inverse image of the centre in it. The isomorphism
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` identifies that inverse image with the fibre
product, so it both supplies the fourth arrow —
`AlgebraicGeometry.BlowUpSquare.exceptionalProjection` is the second projection of the fibre
product read through it — and proves
`AlgebraicGeometry.BlowUpSquare.isPullback`.

## References

* [Stacks Project, Tag 0EV5](https://stacks.math.columbia.edu/tag/0EV5)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 0EV5 "cartesian square" Scheme.IdealSheafData.comapIso

/-- The data fixed by a blowup square: a closed centre of finite presentation in its base
scheme. The other corners and all the arrows are canonically determined. -/
@[stacks 0EV5]
public structure BlowUpSquare where
  /-- The base scheme, the lower-right corner of the square. -/
  base : Scheme.{u}
  /-- The quasi-coherent ideal sheaf cutting out the centre of the blowup. -/
  centerIdeal : base.IdealSheafData
  /-- The centre is a closed subscheme of finite presentation. -/
  centerFinitePresentation : FinitePresentation centerIdeal.subschemeι

namespace BlowUpSquare

variable (s : BlowUpSquare.{u})

/-- The closed centre of a blowup square, the lower-left corner. -/
public abbrev center : Scheme.{u} := s.centerIdeal.subscheme

/-- The blowup of the base in its centre, the upper-right corner. -/
public abbrev blownUp : Scheme.{u} := blowUp s.centerIdeal

/-- The exceptional divisor, the scheme-theoretic inverse image of the centre in the blowup and
the upper-left corner. -/
@[ega "IV 19.4.1" "Y' = f^{-1}(Y)",
  sga "5 VII 9.6" "partial",
  sga "6 0 6.Lemma3",
  sga "6 VII 3.1",
  sga "6 VII 3.7"]
public abbrev exceptionalDivisor : Scheme.{u} := AlgebraicGeometry.exceptionalDivisor s.centerIdeal

/-- The closed immersion of the centre into the base. -/
public abbrev centerInclusion : s.center ⟶ s.base := s.centerIdeal.subschemeι

/-- The blowup morphism, from the blowup to the base. -/
public abbrev blowUpMorphism : s.blownUp ⟶ s.base := blowUpToBase s.centerIdeal

/-- The closed immersion of the exceptional divisor into the blowup. -/
@[sga "6 0 6.Lemma3", sga "6 VII 3.7", sga "7 XVIII 4.1" "the arrow i"]
public abbrev exceptionalInclusion : s.exceptionalDivisor ⟶ s.blownUp :=
  (exceptionalIdeal s.centerIdeal).subschemeι

/-- The morphism from the exceptional divisor to the centre: the exceptional divisor is the
fibre product of the blowup morphism and the inclusion of the centre, and this is the second
projection. -/
@[sga "5 VII 9.6" "The left vertical map g", sga "6 0 6.Lemma3", sga "6 VII 3.7"]
public def exceptionalProjection : s.exceptionalDivisor ⟶ s.center :=
  (s.centerIdeal.comapIso s.blowUpMorphism).hom ≫
    pullback.snd s.blowUpMorphism s.centerInclusion

/-- **Stacks Project, Tag 0EV5.** The blowup square

```
E ⟶ X'
↓    ↓ b
Z ⟶ X
```

commutes and is cartesian: the exceptional divisor `E` is the inverse image `b⁻¹(Z)` of the
centre, hence the fibre product of the blowup morphism `b` and the inclusion of the centre.
Commutativity alone is `AlgebraicGeometry.BlowUpSquare.isPullback.w`. -/
@[stacks 0EV5 "the blow up square", sga "6 0 6.Lemma3" "partial", sga "6 VII 3.7" "more general"]
public theorem isPullback :
    IsPullback s.exceptionalInclusion s.exceptionalProjection s.blowUpMorphism
      s.centerInclusion := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (s.centerIdeal.comapIso s.blowUpMorphism)
    (Scheme.IdealSheafData.comapIso_hom_fst _ _) rfl
  show _ = ((s.centerIdeal.comapIso s.blowUpMorphism).hom ≫
    pullback.snd s.blowUpMorphism s.centerInclusion) ≫ s.centerInclusion
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

end BlowUpSquare

end AlgebraicGeometry

end
