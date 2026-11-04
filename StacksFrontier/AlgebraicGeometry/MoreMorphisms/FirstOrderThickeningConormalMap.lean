module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# The conormal-sheaf map of a morphism of first-order thickenings

A morphism of thickenings `(X ⊂ X') → (S ⊂ S')` is a commutative square, that is a morphism
`Arrow.mk i ⟶ Arrow.mk j` of the arrows `i : X ⟶ X'` and `j : S ⟶ S'`.  When both arrows are
first-order thickenings this file names the canonical map `f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of conormal
sheaves it induces, which is the map of [Stacks Project, Tag 01R4] for the two closed immersions
read off the square.

This is the map whose being an isomorphism is condition (2) of [Stacks Project, Tag 063Y], and
this file proves that condition from condition (1) of the same tag.  Condition (1) asks that `f'`
be flat and that `X = S ×_{S'} X'`; the second of those two says the square is cartesian, and the
two together are exactly the hypotheses of the two clauses of [Stacks Project, Tag 0473] for the
square of immersions underlying the morphism of thickenings.  Cartesianness alone already makes
the map a surjection, and with flatness of `f'` it is invertible.

Since sheaves of modules form a balanced category, the content beyond surjectivity is
injectivity; that is recorded separately, so that a cartesian square with no flatness hypothesis
still reduces condition (2) to a monomorphism assertion.

## Main definitions

* `Stacks.Thickenings.firstOrderThickeningConormalSheafMap`: the canonical map
  `f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of a morphism of first-order thickenings.

## Main results

* `Stacks.Thickenings.firstOrderThickeningConormalSheafMap_eq`: it is
  `Stacks.Immersion.immersionConormalSheafMap` of the square, so the affine characterization
  `Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap` applies to it verbatim.
* `Stacks.Thickenings.isIso_firstOrderThickeningConormalSheafMap`: **(1) ⟹ (2) of
  [Stacks Project, Tag 063Y] for schemes.**  For a cartesian square with `f'` flat the map is an
  isomorphism.
* `Stacks.Thickenings.epi_firstOrderThickeningConormalSheafMap`: for a **cartesian** square the
  map is an epimorphism, with no flatness hypothesis at all.
* `Stacks.Thickenings.isIso_firstOrderThickeningConormalSheafMap_iff_mono`: for a cartesian
  square, condition (2) holds exactly when the map is a monomorphism.

## Implementation notes

The closed-immersion instances are carried by the first-order thickening hypotheses rather than
by instance search, so they are introduced by `letI` in the statement, as in
`Stacks.Thickenings.conormalMap`: the type of the conormal sheaf of an immersion depends on the
instance.  The map itself, the affine characterization that pins it down, and both clauses of
[Stacks Project, Tag 0473] are reused from the library; what is added is their reading for a
morphism of first-order thickenings, where the hypotheses are the clauses of condition (1) of
[Stacks Project, Tag 063Y], and the balanced-category reduction.

The flatness hypothesis is `Flat φ.right`, flatness of `f'`.  The tag's standing hypothesis that
`f` be flat is not carried, because it follows: see the docstring of
`Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`.

## Partial coverage

The converse implication (2) ⟹ (1) of [Stacks Project, Tag 063Y] is **not** proved here; it is
`Stacks.Thickenings.flat_and_isPullback_of_isIso_firstOrderThickeningConormalSheafMap` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalConverse`, which also
assembles the equivalence the tag asserts out of that and
`Stacks.Thickenings.isIso_firstOrderThickeningConormalSheafMap` below.

The algebraic-space statement [Stacks Project, Tag 06BH], which the source proves by passing to
étale scheme charts and quoting [Stacks Project, Tag 063Y], is **not** proved, and the scheme
equivalence is not yet wired into it.  The obstruction is on the algebraic-space side: no
declaration derives `Epi` or `IsIso` of `AlgebraicGeometry.Space.idealSheafMap` from
cartesianness of the square, which is [Stacks Project, Tag 04CQ], and
`AlgebraicGeometry.Space.modulePullback` has a sectionwise description only along an étale
morphism while the morphism in question is flat.  What that reduction leaves is recorded by
`AlgebraicGeometry.Space.epi_conormalMap_of_epi_idealSheafMap`,
`AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_idealSheafMap` and
`AlgebraicGeometry.Space.isIso_conormalMap_iff_mono_of_epi_idealSheafMap`.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

open Stacks.Immersion

variable {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}

/-- **The canonical map of conormal sheaves of a morphism of first-order thickenings.** For
first-order thickenings `i : X ⟶ X'` and `j : S ⟶ S'` and a commutative square
`φ : Arrow.mk i ⟶ Arrow.mk j`, with components `f = φ.left : X ⟶ S` and `f' = φ.right : X' ⟶ S'`,
this is the map `f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4]. -/
def firstOrderThickeningConormalSheafMap (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    letI := hi.1
    letI := hj.1
    (modulePullback φ.left.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i :=
  letI := hi.1
  letI := hj.1
  immersionConormalSheafMap i j φ.left φ.right (toShHom_square (Arrow.w φ).symm)

/-- The conormal-sheaf map of a morphism of first-order thickenings is the conormal-sheaf map of
the underlying square of immersions, so its affine characterization
`Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap` applies to it. -/
theorem firstOrderThickeningConormalSheafMap_eq (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    letI := hi.1
    letI := hj.1
    firstOrderThickeningConormalSheafMap hi hj φ =
      immersionConormalSheafMap i j φ.left φ.right (toShHom_square (Arrow.w φ).symm) :=
  rfl

/-! ### The surjectivity clause of Tag 063Y -/

/-- **The surjectivity half of condition (2) of [Stacks Project, Tag 063Y], for schemes.** For a
morphism of first-order thickenings whose square is cartesian, so that `X = S ×_{S'} X'`, the
canonical map `f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` is an epimorphism.

No flatness is used: cartesianness alone gives surjectivity, by
`Stacks.Immersion.epi_immersionConormalSheafMap`, which is the surjectivity clause of
[Stacks Project, Tag 0473] for a cartesian square of immersions.  The cartesian hypothesis is
the second half of condition (1) of the tag, so this is the half of (1) ⟹ (2) that the flatness
hypotheses are not needed for. -/
@[stacks 063Y "(1) ⟹ (2) for schemes, surjectivity"]
theorem epi_firstOrderThickeningConormalSheafMap (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j)
    (sq : IsPullback i φ.left φ.right j) :
    letI := hi.1
    letI := hj.1
    Epi (firstOrderThickeningConormalSheafMap hi hj φ) :=
  let := hi.1
  let := hj.1
  epi_immersionConormalSheafMap i j φ.left φ.right sq

/-- **Over a cartesian square, condition (2) of [Stacks Project, Tag 063Y] is injectivity.**
For a morphism of first-order thickenings whose square is cartesian, the canonical map
`f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` is an isomorphism exactly when it is a monomorphism.

Surjectivity is automatic by `Stacks.Thickenings.epi_firstOrderThickeningConormalSheafMap`, and
sheaves of modules on a ringed space form a balanced category, so an epimorphism that is also a
monomorphism is invertible.  This locates the remaining content of (1) ⟹ (2) — the content the
flatness of `f` and `f'` is for — in injectivity alone. -/
theorem isIso_firstOrderThickeningConormalSheafMap_iff_mono (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j)
    (sq : IsPullback i φ.left φ.right j) :
    letI := hi.1
    letI := hj.1
    IsIso (firstOrderThickeningConormalSheafMap hi hj φ) ↔
      Mono (firstOrderThickeningConormalSheafMap hi hj φ) := by
  let := hi.1
  let := hj.1
  have := epi_firstOrderThickeningConormalSheafMap hi hj φ sq
  exact ⟨fun _ => inferInstance, fun _ => isIso_of_mono_of_epi _⟩

/-! ### Condition (2) of Tag 063Y -/

/-- **[Stacks Project, Tag 063Y], (1) ⟹ (2), for schemes.**  Let `(f, f') : (X ⊂ X') → (S ⊂ S')`
be a morphism of first-order thickenings of schemes, with `f = φ.left` and `f' = φ.right`.  If
`f'` is flat and `X = S ×_{S'} X'`, then the canonical map `f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` is an
isomorphism.

The two hypotheses are exactly the two halves of condition (1) of the tag: `Flat φ.right` is
flatness of `f'`, and `sq` is the base-change identity `X = S ×_{S'} X'`.  The conclusion is
condition (2).  The standing hypothesis of the tag that `f` be flat is not needed, because it is
a consequence of the other two.

This is `Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`, the flat base-change clause
of [Stacks Project, Tag 0473], applied to the square of immersions underlying the morphism of
thickenings. -/
@[stacks 063Y "(1) ⟹ (2) for schemes"]
theorem isIso_firstOrderThickeningConormalSheafMap (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) [Flat φ.right]
    (sq : IsPullback i φ.left φ.right j) :
    letI := hi.1
    letI := hj.1
    IsIso (firstOrderThickeningConormalSheafMap hi hj φ) :=
  let := hi.1
  let := hj.1
  isIso_immersionConormalSheafMap_of_flat i j φ.left φ.right sq

end Stacks.Thickenings

end
