module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases

/-!
# The two-periodic complex of two mutually annihilating endomorphisms

A `(2, 1)`-periodic complex of [Stacks, Tag 02MW] is a pair of endomorphisms `φ, ψ` of an object
`M` with `φ ≫ ψ = 0` and `ψ ≫ φ = 0`, read as the complex

`… ⟶ M --φ--> M --ψ--> M --φ--> M ⟶ …`.

In Lean such a complex is a `ZMod 2`-indexed cochain complex, and this file builds that cochain
complex from the pair and identifies its two homology objects with the homology objects of the two
short complexes `ShortComplex.mk φ ψ` and `ShortComplex.mk ψ φ`, the spelling in which
[Stacks, Tag 02MX] part (2) produces a periodic complex.

`AlgebraicGeometry.twoPeriodicComplex` does the same for modules over a ring; the construction
here is for an arbitrary category with zero morphisms, as needed for a periodic complex of
`𝒪_X`-modules.

## Main definitions

* `CategoryTheory.twoPeriodicObjectComplex` — the `ZMod 2`-indexed cochain complex of a pair of
  mutually annihilating endomorphisms.

## Main results

* `CategoryTheory.twoPeriodicObjectComplex_d_zero_one` and
  `CategoryTheory.twoPeriodicObjectComplex_d_one_zero` — the two differentials.
* `CategoryTheory.twoPeriodicObjectComplexHomologyIsoZero` and
  `CategoryTheory.twoPeriodicObjectComplexHomologyIsoOne` — the identification of the two
  homology objects. Degree `0` carries `Ker φ / Im ψ`, the homology of `ShortComplex.mk ψ φ`,
  because the differential *into* degree `0` is `ψ`.

## Implementation notes

The short complex `K.sc' i j k` is `ShortComplex.mk (K.d i j) (K.d j k)`, and the two
differentials of the complex below are the two branches of one `if`, so `K.sc' 1 0 1` and
`ShortComplex.mk ψ φ` are the same term: the two homology identifications are
`HomologicalComplex.homologyIsoSc'` with nothing composed onto it. They are nevertheless given
their own `def`s rather than inlined at the point of use, so that the `ZMod 2` index conditions
are discharged once.

## References

* [Stacks Project, Tag 02MW](https://stacks.math.columbia.edu/tag/02MW)
* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] {M : A} (φ ψ : M ⟶ M)
  (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0)

include hφψ hψφ

/-- The `ZMod 2`-indexed cochain complex of two mutually annihilating endomorphisms of `M`: the
differential out of degree `0` is `φ` and the differential out of degree `1` is `ψ`. -/
def twoPeriodicObjectComplex : CochainComplex A (ZMod 2) where
  X _ := M
  d i j := if (ComplexShape.up (ZMod 2)).Rel i j then (if i = 0 then φ else ψ) else 0
  shape i j hij := by
    change ¬i + 1 = j at hij
    simp [hij]
  d_comp_d' i j k hij hjk := by
    change i + 1 = j at hij
    change j + 1 = k at hjk
    subst hij
    subst hjk
    fin_cases i
    · change φ ≫ ψ = 0
      exact hφψ
    · change ψ ≫ φ = 0
      exact hψφ

/-- Every object of the two-periodic complex is `M`. -/
@[simp]
theorem twoPeriodicObjectComplex_X (i : ZMod 2) :
    (twoPeriodicObjectComplex φ ψ hφψ hψφ).X i = M :=
  rfl

/-- The differential of the two-periodic complex from degree `0` to degree `1` is `φ`. -/
@[simp]
theorem twoPeriodicObjectComplex_d_zero_one :
    (twoPeriodicObjectComplex φ ψ hφψ hψφ).d 0 1 = φ :=
  rfl

/-- The differential of the two-periodic complex from degree `1` to degree `0` is `ψ`. -/
@[simp]
theorem twoPeriodicObjectComplex_d_one_zero :
    (twoPeriodicObjectComplex φ ψ hφψ hψφ).d 1 0 = ψ :=
  rfl

variable [CategoryWithHomology A]

/-- The homology of the two-periodic complex in degree `0` is `Ker φ / Im ψ`, the homology of
`ShortComplex.mk ψ φ`: the differential into degree `0` is `ψ` and the one out of it is `φ`. -/
def twoPeriodicObjectComplexHomologyIsoZero :
    (twoPeriodicObjectComplex φ ψ hφψ hψφ).homology 0 ≅ (ShortComplex.mk ψ φ hψφ).homology :=
  (twoPeriodicObjectComplex φ ψ hφψ hψφ).homologyIsoSc' 1 0 1 (by simp) (by simp)

/-- The homology of the two-periodic complex in degree `1` is `Ker ψ / Im φ`, the homology of
`ShortComplex.mk φ ψ`. -/
def twoPeriodicObjectComplexHomologyIsoOne :
    (twoPeriodicObjectComplex φ ψ hφψ hψφ).homology 1 ≅ (ShortComplex.mk φ ψ hφψ).homology :=
  (twoPeriodicObjectComplex φ ψ hφψ hψφ).homologyIsoSc' 0 1 0 (by simp)
    (by simp [show (1 + 1 : ZMod 2) = 0 from by decide])

end CategoryTheory

end
