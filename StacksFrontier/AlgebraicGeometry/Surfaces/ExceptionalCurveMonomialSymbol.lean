module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodGradedPieceComparison
public import StacksFrontier.AlgebraicGeometry.Surfaces.MonomialSymbolOneStep
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodOfExceptional
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodResidueMap

/-!
# The symbol of the formal neighbourhood of an exceptional curve of the first kind

Let `X` be a Noetherian scheme and `E ⊂ X` an exceptional curve of the first kind, cut out by an
ideal sheaf `D` and presented as the projective line by `e : 𝐏¹_k ≅ E`. Write
`A = lim H⁰(Eₙ, 𝒪ₙ)` for the ring of compatible global functions on the thickenings and `Iₙ` for
the kernel of `A ⟶ H⁰(Eₙ, 𝒪ₙ)`. This file builds the *symbol*, or leading form,

`σₙ : A ⟶ k[T₀, T₁]ₙ`,

which carries a function vanishing to order `≥ n` on `E` to a binary form of degree `n`, and
proves every axiom of `AlgebraicGeometry.SemistableReduction.OneStepSymbol` for it except the
one-step multiplicativity.

## The construction

The graded piece `Iₙ₊₁ / Iₙ₊₂` is already compared with `H⁰(𝐏¹_k, 𝒪(n + 1))` by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedPieceComparison`,
with additivity, semilinearity over the residue map, injectivity and surjectivity all proved. The
one thing standing between that comparison and a symbol system was the *target*: the comparison
lands in `AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceTwistSections k (n + 1)`, the
sections of a twist, whereas a symbol has to be valued in `MvPolynomial (Fin 2) k`.

That identification is `Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear` at `n = 1`, which
is bijective by `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSectionLinear`, and the two
spellings of the projective line agree with no cast: `Stacks.AlgebraicGeometry.ProjPolyChart`
`.polyGrading k 1` is `MvPolynomial.homogeneousSubmodule (Fin 2) k`, so
`Stacks.ProjectiveSpace.Cohomology.twistSectionsModule k 1 d` and `gradedPieceTwistSections k d`
are the same module. The resulting `k`-linear isomorphism is
`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceFormEquiv`.

An earlier note on this chain, in the module docstring of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean`, said that the
bridge had first to be compared with
`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceTwistSectionsBasis`, which is transported
along the abstract isomorphism `Stacks.ProjectiveSpace.Cohomology.homogeneousIsoTwistSections`
rather than along `degreeSectionLinear`, and that "until those two identifications are compared,
the one-step law in the sections does not yield `symbol_mul`". No such comparison is needed. The
symbol is defined through `degreeSectionLinear` itself, and the basis plays no part in it: the
only place the monomials are wanted is `exists_symbol_one_eq_X`, which asks for two elements of
`I₁` whose degree-one symbols are `T₀` and `T₁`, and those are produced by the surjectivity of
`gradedPieceComparison` applied to the two forms directly. Nothing in this file mentions
`gradedPieceTwistSectionsBasis` or `homogeneousIsoTwistSections`.

## What remains

The symbol built here satisfies twelve of the thirteen fields of
`AlgebraicGeometry.SemistableReduction.OneStepSymbol`. The thirteenth, `symbol_mul_one`, is the
*one-step law*

`σ_{d+1}(a b) = σ_d(a) σ₁(b)`  for `a ∈ I_d`, `b ∈ I₁`,

and it is carried here as a hypothesis,
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.OneStepLaw`. It is the
only input of [Stacks, Tag 0C2K] that is not proved in this development: by
`AlgebraicGeometry.SemistableReduction.OneStepSymbol.toMonomialSymbol` the general bidegree
follows from it, and by
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialSymbolOfExceptional`
all five geometric inputs of the tag follow from the resulting monomial symbol system. So
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofOneStepLaw` builds the whole
bundle from the hypotheses of Tag 0C2K together with that single equation.

Two things are known about what that equation still costs. Its bidegree-`(0, 1)` case is *not*
part of the gap: for `d = 0` the law is `σ₁(a b) = σ₀(a) σ₁(b)`, which is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.formalNeighborhoodSymbol_smul`, proved unconditionally above from the semilinearity of the
graded-piece comparison over the residue map. And no property of the inverse limit
`A = lim H⁰(Eₙ, 𝒪ₙ)` is needed for the rest: by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.oneStepLaw_of_gradedPieceOneStepLaw` the law follows from `GradedPieceOneStepLaw`, the same
equation about two sections of a single thickening, using only that the projections out of `A`
are ring homomorphisms compatible with restriction. So the whole residue of the tag is the
cross-degree multiplicativity of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedPieceComparison`
in the bidegrees `(d, 1)` with `d ≥ 1`, and that is a statement about sections of the
thickenings, which is the form the proved sheaf-level halves are stated in.

The structure is not satisfied vacuously. A symbol system with `σ ≡ 0` is impossible: the
`symbol_one` field asks for `σ₀(1) = 1`, and `MvPolynomial (Fin 2) k` over a field is nontrivial.
Here `σ₀(1) = C 1 = 1` holds because the residue map is a ring homomorphism, and `σ₁` takes the
values `T₀` and `T₁`, so the symbol built here is visibly nonzero in every degree where `Iₙ`
properly contains `Iₙ₊₁`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceFormEquiv` — the degree-`d` binary forms
  are `H⁰(𝐏¹_k, 𝒪(d))`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.formalNeighborhoodSymbol` — the symbol.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.OneStepLaw` — the one
  remaining equation.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedPieceForm` and
  `GradedPieceOneStepLaw` — the same equation with the inverse limit removed, about two sections
  of a single thickening.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.oneStepLaw_of_gradedPieceOneStepLaw` — the reduction of the one-step law to it.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.oneStepSymbol` and
  `monomialSymbol` — the symbol systems it yields.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofOneStepLaw` and
  `ofGradedPieceOneStepLaw` — the five geometric inputs of [Stacks, Tag 0C2K] from either form
  of the one-step law.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.SemistableReduction
open Stacks.ProjectiveSpace.Cohomology Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **The degree-`d` binary forms are the sections of `𝒪(d)` on `𝐏¹_k`.**

This is `Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear` on the projective line, made an
isomorphism by `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSectionLinear`. The two
spellings of the projective line agree with no cast, because
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1` is the total-degree grading of
`k[T₀, T₁]`. -/
public def gradedPieceFormEquiv (k : Type u) [Field k] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k d ≃ₗ[k] gradedPieceTwistSections k d :=
  LinearEquiv.ofBijective (degreeSectionLinear k 1 d) (bijective_degreeSectionLinear 1 d)

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

namespace IsExceptionalCurveOfFirstKind

variable [IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e)

/-- **The symbol of the formal neighbourhood, valued in the degree-`n` forms.** In degree `0` it
is the residue map to `k`, read as a constant; in degree `n + 1` it is the degreewise comparison
of the graded piece with `H⁰(𝐏¹_k, 𝒪(n + 1))`, read back as a form along
`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceFormEquiv`.

Off `Iₙ` the value is unconstrained, which is why every clause about it is guarded by membership
in `Iₙ`: the comparison itself is only additive on the kernel of the thickening restriction. -/
public def formalNeighborhoodSymbolForm (n : ℕ) (a : formalNeighborhoodRing D) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k n :=
  match n with
  | 0 => ⟨MvPolynomial.C (formalNeighborhoodResidue D k e a),
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)⟩
  | m + 1 => (gradedPieceFormEquiv k (m + 1)).symm
      (hE.gradedPieceComparison m (formalNeighborhoodProjection D (m + 1) a))

/-- **The symbol, or leading form, of a compatible function on the thickenings of an exceptional
curve of the first kind**, as a binary polynomial. This is the `symbol` field of a monomial
symbol system on the projection-kernel filtration. -/
public def formalNeighborhoodSymbol (n : ℕ) (a : formalNeighborhoodRing D) :
    MvPolynomial (Fin 2) k :=
  hE.formalNeighborhoodSymbolForm n a

/-- In degree `0` the symbol is the residue in `k`, read as a constant. -/
public theorem formalNeighborhoodSymbol_zero (a : formalNeighborhoodRing D) :
    hE.formalNeighborhoodSymbol 0 a = MvPolynomial.C (formalNeighborhoodResidue D k e a) := rfl

/-- In degree `n + 1` the symbol is the degreewise comparison of the graded piece, read back as a
form. -/
public theorem formalNeighborhoodSymbol_succ (m : ℕ) (a : formalNeighborhoodRing D) :
    hE.formalNeighborhoodSymbol (m + 1) a =
      (((gradedPieceFormEquiv k (m + 1)).symm
        (hE.gradedPieceComparison m (formalNeighborhoodProjection D (m + 1) a)) :
          MvPolynomial.homogeneousSubmodule (Fin 2) k (m + 1)) : MvPolynomial (Fin 2) k) := rfl

/-- **The symbol of an element is a binary form of the corresponding degree**, with no hypothesis
at all: the symbol is defined as the coercion of an element of the homogeneous submodule. -/
public theorem formalNeighborhoodSymbol_mem (n : ℕ) (a : formalNeighborhoodRing D) :
    hE.formalNeighborhoodSymbol n a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k n :=
  (hE.formalNeighborhoodSymbolForm n a).2

/-- **The symbol is additive on `Iₙ`.** -/
public theorem formalNeighborhoodSymbol_add (n : ℕ) {a b : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D n) (hb : b ∈ formalNeighborhoodFiltration D n) :
    hE.formalNeighborhoodSymbol n (a + b) =
      hE.formalNeighborhoodSymbol n a + hE.formalNeighborhoodSymbol n b := by
  cases n with
  | zero =>
    simp [hE.formalNeighborhoodSymbol_zero]
  | succ m =>
    rw [hE.formalNeighborhoodSymbol_succ, hE.formalNeighborhoodSymbol_succ,
      hE.formalNeighborhoodSymbol_succ, map_add (formalNeighborhoodProjection D (m + 1)),
      hE.gradedPieceComparison_add m (thickeningRestriction_projection_eq_zero D m ha)
        (thickeningRestriction_projection_eq_zero D m hb), map_add, Submodule.coe_add]

/-- **The symbol of an element of `Iₙ` vanishes exactly when the element lies in `Iₙ₊₁`.** -/
public theorem formalNeighborhoodSymbol_eq_zero_iff (n : ℕ) {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D n) :
    hE.formalNeighborhoodSymbol n a = 0 ↔ a ∈ formalNeighborhoodFiltration D (n + 1) := by
  cases n with
  | zero =>
    rw [hE.formalNeighborhoodSymbol_zero, MvPolynomial.C_eq_zero, ← RingHom.mem_ker,
      ker_formalNeighborhoodResidue]
  | succ m =>
    rw [hE.formalNeighborhoodSymbol_succ, Submodule.coe_eq_zero, LinearEquiv.map_eq_zero_iff,
      hE.gradedPieceComparison_eq_zero_iff m (thickeningRestriction_projection_eq_zero D m ha)]
    exact (mem_formalNeighborhoodFiltration_succ_iff D (m + 1) a).symm

/-- **The symbol is semilinear over its degree-zero part**: multiplying by an arbitrary
compatible function multiplies the symbol by that function's residue. -/
public theorem formalNeighborhoodSymbol_smul (n : ℕ) (c : formalNeighborhoodRing D)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D n) :
    hE.formalNeighborhoodSymbol n (c * a) =
      hE.formalNeighborhoodSymbol 0 c * hE.formalNeighborhoodSymbol n a := by
  cases n with
  | zero =>
    simp [hE.formalNeighborhoodSymbol_zero]
  | succ m =>
    rw [hE.formalNeighborhoodSymbol_succ, hE.formalNeighborhoodSymbol_succ,
      hE.formalNeighborhoodSymbol_zero, map_mul (formalNeighborhoodProjection D (m + 1)),
      hE.gradedPieceComparison_smul m c (thickeningRestriction_projection_eq_zero D m ha),
      map_smul, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul]

/-- **The degree-zero symbol of `1` is `1`.** This is what rules out the zero symbol. -/
public theorem formalNeighborhoodSymbol_zero_one :
    hE.formalNeighborhoodSymbol 0 (1 : formalNeighborhoodRing D) = 1 := by
  rw [hE.formalNeighborhoodSymbol_zero, map_one, MvPolynomial.C_1]

/-- **Every constant is a degree-zero symbol**: the residue map `A ⟶ k` is onto. -/
public theorem exists_formalNeighborhoodSymbol_zero_eq_C (c : k) :
    ∃ a : formalNeighborhoodRing D, hE.formalNeighborhoodSymbol 0 a = MvPolynomial.C c := by
  obtain ⟨a, ha⟩ := surjective_formalNeighborhoodResidue D k
    (hE.surjective_formalNeighborhoodProjection 0) e c
  exact ⟨a, by rw [hE.formalNeighborhoodSymbol_zero, ha]⟩

/-- **Every binary form of degree one is the degree-one symbol of an element of `I₁`.** The
comparison of the graded piece `I₁ / I₂` with `H⁰(𝐏¹_k, 𝒪(1))` is onto, and the projections out
of `A` are onto for an exceptional curve of the first kind. -/
public theorem exists_mem_one_formalNeighborhoodSymbol_eq
    (v : MvPolynomial.homogeneousSubmodule (Fin 2) k 1) :
    ∃ x, x ∈ formalNeighborhoodFiltration D 1 ∧
      hE.formalNeighborhoodSymbol 1 x = (v : MvPolynomial (Fin 2) k) := by
  obtain ⟨z, hz, hzv⟩ := hE.gradedPieceComparison_surjective 0 (gradedPieceFormEquiv k 1 v)
  obtain ⟨x, hx, hxz⟩ := exists_projection_eq_of_thickeningRestriction_eq_zero D 0
    hE.surjective_thickeningRestriction hz
  refine ⟨x, hx, ?_⟩
  rw [hE.formalNeighborhoodSymbol_succ, hxz, hzv, LinearEquiv.symm_apply_apply]

/-- **Both coordinates are degree-one symbols**: `I₁ ⟶ H⁰(𝐏¹_k, 𝒪(1))` is onto. -/
public theorem exists_formalNeighborhoodSymbol_one_eq_X :
    ∃ x y : formalNeighborhoodRing D, x ∈ formalNeighborhoodFiltration D 1 ∧
      y ∈ formalNeighborhoodFiltration D 1 ∧
      hE.formalNeighborhoodSymbol 1 x = MvPolynomial.X 0 ∧
      hE.formalNeighborhoodSymbol 1 y = MvPolynomial.X 1 := by
  have key (i : Fin 2) : ∃ x ∈ formalNeighborhoodFiltration D 1,
      hE.formalNeighborhoodSymbol 1 x = MvPolynomial.X i :=
    hE.exists_mem_one_formalNeighborhoodSymbol_eq
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X _ _⟩
  obtain ⟨x, hx, hxs⟩ := key 0
  obtain ⟨y, hy, hys⟩ := key 1
  exact ⟨x, y, hx, hy, hxs, hys⟩

/-- **The one-step law**, the single remaining input of [Stacks, Tag 0C2K]: the symbol is
multiplicative in the bidegree `(d, 1)`.

Everything else a monomial symbol system asks for is proved for
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.formalNeighborhoodSymbol` in this file, and the general bidegree follows from this one by
`AlgebraicGeometry.SemistableReduction.OneStepSymbol.toMonomialSymbol`. The sheaf-level halves of
it are proved — `Stacks.Divisors.idealTensorMul_comp_unit_comp_thickeningKernelMap` on the curve
and `Stacks.AlgebraicGeometry.TwistTensor.mulSection_degreeSection` on `𝐏¹_k` — and what is
missing is the passage from those to global sections, for which the unit of `i^* ⊣ i_*` has to be
surjective over an affine open. -/
public def OneStepLaw : Prop :=
  ∀ (d : ℕ) {a b : formalNeighborhoodRing D},
    a ∈ formalNeighborhoodFiltration D d → b ∈ formalNeighborhoodFiltration D 1 →
    hE.formalNeighborhoodSymbol (d + 1) (a * b) =
      hE.formalNeighborhoodSymbol d a * hE.formalNeighborhoodSymbol 1 b

/-- **The comparison of the graded piece, read back as a binary form of degree `m + 1`.**

This is the symbol of a *single section of one thickening*, before the inverse limit is taken:
the symbol of a compatible function is this applied to one of its components, by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.formalNeighborhoodSymbol_succ_eq_gradedPieceForm`. -/
public def gradedPieceForm (m : ℕ) (z : Γ(thickening D (m + 1), ⊤)) : MvPolynomial (Fin 2) k :=
  ((gradedPieceFormEquiv k (m + 1)).symm (hE.gradedPieceComparison m z) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k (m + 1))

/-- The symbol in degree `m + 1` is the graded-piece form of the `(m + 1)`-st component. -/
public theorem formalNeighborhoodSymbol_succ_eq_gradedPieceForm (m : ℕ)
    (a : formalNeighborhoodRing D) :
    hE.formalNeighborhoodSymbol (m + 1) a =
      hE.gradedPieceForm m (formalNeighborhoodProjection D (m + 1) a) := rfl

/-- **The one-step law with the inverse limit removed**: the cross-degree multiplicativity of the
graded-piece comparison, stated for two sections of a *single* thickening.

`x` and `y` are global functions on `Eₘ₊₂`, restricting to `u` on `Eₘ₊₁` and to `v` on `E₁`, with
`u` vanishing on `Eₘ` and `v` vanishing on `E₀`; the assertion is that the degree-`(m + 2)` form
of their product is the product of the degree-`(m + 1)` form of `u` and the degree-`1` form of
`v`.

Nothing about the ring `A = lim H⁰(Eₙ, 𝒪ₙ)` appears here, and that is the point of the statement:
by `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.oneStepLaw_of_gradedPieceOneStepLaw` it implies the one-step law, so no property of the inverse
limit is needed for that law beyond the projections being ring homomorphisms compatible with
restriction. It is also the shape the proved sheaf-level halves produce — those are statements
about sections over an open of the thickenings, not about compatible systems. -/
public def GradedPieceOneStepLaw : Prop :=
  ∀ (m : ℕ) (h1 : 1 ≤ m + 2) (x y : Γ(thickening D (m + 2), ⊤))
      (u : Γ(thickening D (m + 1), ⊤)) (v : Γ(thickening D 1, ⊤)),
    thickeningRestriction D (m + 1) x = u →
    thickeningRestrictionLE D h1 y = v →
    thickeningRestriction D m u = 0 →
    thickeningRestriction D 0 v = 0 →
    hE.gradedPieceForm (m + 1) (x * y) =
      hE.gradedPieceForm m u * hE.gradedPieceForm 0 v

/-- **The one-step law follows from the graded-piece one-step law.**

The degree-zero case needs no hypothesis at all: it is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.formalNeighborhoodSymbol_smul`, the semilinearity of the symbol over its degree-zero part,
which is already proved unconditionally. So the hypothesis is consumed only in the bidegrees
`(d, 1)` with `d ≥ 1`, where both factors have positive degree, and the whole remaining content
of [Stacks, Tag 0C2K] is the cross-degree multiplicativity of the graded-piece comparison on one
thickening. -/
public theorem oneStepLaw_of_gradedPieceOneStepLaw (hmul : hE.GradedPieceOneStepLaw) :
    hE.OneStepLaw := by
  intro d a b ha hb
  cases d with
  | zero => exact hE.formalNeighborhoodSymbol_smul 1 a hb
  | succ m =>
    refine Eq.trans (hE.formalNeighborhoodSymbol_succ_eq_gradedPieceForm (m + 1) (a * b)) ?_
    refine Eq.trans (congrArg (hE.gradedPieceForm (m + 1))
      (map_mul (formalNeighborhoodProjection D (m + 2)) a b)) ?_
    exact hmul m (by omega) (formalNeighborhoodProjection D (m + 2) a)
      (formalNeighborhoodProjection D (m + 2) b)
      (formalNeighborhoodProjection D (m + 1) a) (formalNeighborhoodProjection D 1 b)
      (thickeningRestriction_formalNeighborhoodProjection D (m + 1) a)
      (thickeningRestrictionLE_formalNeighborhoodProjection D _ b)
      (thickeningRestriction_projection_eq_zero D m ha)
      (thickeningRestriction_projection_eq_zero D 0 hb)

/-- **The one-step symbol system of an exceptional curve of the first kind, given the one-step
law.** Twelve of the thirteen fields are the theorems of this file; the thirteenth is the
hypothesis. -/
public def oneStepSymbol (hmul : hE.OneStepLaw) : OneStepSymbol (formalNeighborhoodRing D) k where
  ideal := formalNeighborhoodFiltration D
  symbol := hE.formalNeighborhoodSymbol
  ideal_zero := formalNeighborhoodFiltration_zero D
  ideal_succ_le := formalNeighborhoodFiltration_succ_le D
  mul_le := formalNeighborhoodFiltration_mul_le D
  symbol_mem := fun n _ _ => hE.formalNeighborhoodSymbol_mem n _
  symbol_add := hE.formalNeighborhoodSymbol_add
  symbol_eq_zero_iff := hE.formalNeighborhoodSymbol_eq_zero_iff
  symbol_smul := hE.formalNeighborhoodSymbol_smul
  symbol_mul_one := hmul
  symbol_one := hE.formalNeighborhoodSymbol_zero_one
  surjective_symbol_zero := hE.exists_formalNeighborhoodSymbol_zero_eq_C
  exists_symbol_one_eq_X := hE.exists_formalNeighborhoodSymbol_one_eq_X

/-- **The monomial symbol system of an exceptional curve of the first kind, given the one-step
law.** The multiplicativity of the symbol across an arbitrary pair of degrees is supplied by
`AlgebraicGeometry.SemistableReduction.OneStepSymbol.toMonomialSymbol`, which needs no input
beyond the one-step law and the degree-zero law. -/
public def monomialSymbol (hmul : hE.OneStepLaw) : MonomialSymbol (formalNeighborhoodRing D) k :=
  (hE.oneStepSymbol hmul).toMonomialSymbol

/-- The filtration of the monomial symbol system is the filtration of the formal neighbourhood. -/
@[simp]
public theorem monomialSymbol_ideal (hmul : hE.OneStepLaw) :
    (hE.monomialSymbol hmul).ideal = formalNeighborhoodFiltration D := rfl

/-- The symbol of the monomial symbol system is the symbol of the formal neighbourhood. -/
@[simp]
public theorem monomialSymbol_symbol (hmul : hE.OneStepLaw) :
    (hE.monomialSymbol hmul).symbol = hE.formalNeighborhoodSymbol := rfl

end IsExceptionalCurveOfFirstKind

namespace ExceptionalMonomialData

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from the one-step law alone.**

Every hypothesis here is a hypothesis of the tag: `X` Noetherian is not even needed for the
bundle, `hE` is the exceptional curve of the first kind, and the effective-Cartier instance is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.isEffectiveCartierDivisor`,
part of the definition of such a curve. The one thing carried is `hmul`, the one-step
multiplicativity of the symbol built in this file. -/
public def ofOneStepLaw [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (hmul : hE.OneStepLaw) :
    ExceptionalMonomialData D :=
  ofMonomialSymbolOfExceptional (D := D) k hE (hE.monomialSymbol hmul) rfl

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from the graded-piece one-step law.**

The same bundle as
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofOneStepLaw`, carrying instead
the statement with the inverse limit removed. This is the single sheaf-level equation the tag is
still waiting on: a statement about two sections of one thickening, in one bidegree. -/
public def ofGradedPieceOneStepLaw [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (hmul : hE.GradedPieceOneStepLaw) :
    ExceptionalMonomialData D :=
  ofOneStepLaw (D := D) hE (hE.oneStepLaw_of_gradedPieceOneStepLaw hmul)

end ExceptionalMonomialData

end AlgebraicGeometry.Scheme.IdealSheafData

end
