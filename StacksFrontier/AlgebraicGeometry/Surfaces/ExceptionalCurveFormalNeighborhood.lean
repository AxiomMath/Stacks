module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodReduction
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbol

/-!
# The formal neighbourhood of an exceptional curve of the first kind

Let `X` be a Noetherian scheme and let `E ⊂ X` be an exceptional curve of the first kind, cut
out by an ideal sheaf `D` and presented as the projective line by an isomorphism
`e : 𝐏¹_k ≅ E`. Write `E_n` for the `n`-th infinitesimal thickening of `E` and
`A = lim H⁰(E_n, 𝒪_n)` for the ring of compatible global functions on them,
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing`. **Stacks 0C2K** asserts that
`A` is a complete local Noetherian regular local ring of dimension `2`, and that the kernel of
`A ⟶ H⁰(E_n, 𝒪_n)` is the `n`-th power of its maximal ideal.

This file states those four conclusions for an exceptional curve of the first kind.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` — the five geometric inputs.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.monomialFiltration` — the
  monomial filtration they build.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isNoetherianCompleteLocalRing_formalNeighborhoodRing`,
  `isRegularLocalRing_formalNeighborhoodRing`, `ringKrullDim_formalNeighborhoodRing_eq_two` and
  `ker_formalNeighborhoodProjection_eq_maximalIdeal_pow_of_isExceptionalCurveOfFirstKind` — the
  four conclusions of **Stacks 0C2K**.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- Two elements of the ring of compatible functions on the thickenings of `D`, together with
five statements about them and the projection-kernel filtration: the filtration is
multiplicative, the two elements lie in the first step, each step is spanned modulo the next by
the monomials in them, those monomials are independent over the residue quotient, and the
residue quotient is a field. -/
public structure ExceptionalMonomialData where
  /-- The first of the two chosen elements, a lift of a coordinate on `𝐏¹_k`. -/
  gen₁ : formalNeighborhoodRing D
  /-- The second of the two chosen elements. -/
  gen₂ : formalNeighborhoodRing D
  /-- The filtration is multiplicative: a function vanishing to order `≥ m` times one vanishing
  to order `≥ n` vanishes to order `≥ m + n`. -/
  mul_le : ∀ m n, formalNeighborhoodFiltration D m * formalNeighborhoodFiltration D n ≤
    formalNeighborhoodFiltration D (m + n)
  /-- Both chosen elements vanish on `E`. -/
  span_le_ideal_one : Ideal.span {gen₁, gen₂} ≤ formalNeighborhoodFiltration D 1
  /-- Modulo the next step, each step of the filtration is spanned by the monomials of that
  degree in the two chosen elements. -/
  le_span_pow_sup : ∀ n, formalNeighborhoodFiltration D n ≤
    Ideal.span {gen₁, gen₂} ^ n ⊔ formalNeighborhoodFiltration D (n + 1)
  /-- The degree-`d` monomials are independent over the residue quotient: this is the monomial
  basis of `H⁰(𝐏¹_k, 𝒪(d))`. -/
  monomials_indep : ∀ (d : ℕ) (c : ℕ → formalNeighborhoodRing D),
    (∑ j ∈ Finset.range (d + 1), c j * genMonomial gen₁ gen₂ d j) ∈
      formalNeighborhoodFiltration D (d + 1) →
    ∀ j ≤ d, c j ∈ formalNeighborhoodFiltration D 1
  /-- The residue quotient is a field: this is `H⁰(𝐏¹_k, 𝒪) = k`. -/
  quotient_isField : IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1)

namespace ExceptionalMonomialData

variable {D}

/-- The monomial filtration on the ring of compatible functions built from the five inputs. -/
public def monomialFiltration (M : ExceptionalMonomialData D) :
    MonomialFiltration (formalNeighborhoodRing D) :=
  formalNeighborhoodMonomialFiltration D M.gen₁ M.gen₂ M.mul_le M.span_le_ideal_one
    M.le_span_pow_sup M.monomials_indep M.quotient_isField

/-- The ideals of `M.monomialFiltration` are the steps of the filtration of `D` by order of
vanishing along `E`. -/
@[simp]
public theorem monomialFiltration_ideal (M : ExceptionalMonomialData D) :
    M.monomialFiltration.ideal = formalNeighborhoodFiltration D :=
  rfl

/-- The `ExceptionalMonomialData D` on two elements `x`, `y` of the ring of compatible functions
that vanish on `E`, span each step of the filtration modulo the next by their monomials, and
whose monomials of each degree are independent over the residue quotient, where `E` is an
exceptional curve of the first kind and the thickening restrictions are surjective. -/
public def ofMonomialInputs (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m))
    (x y : formalNeighborhoodRing D)
    (hgen : Ideal.span {x, y} ≤ formalNeighborhoodFiltration D 1)
    (hspanPow : ∀ n, formalNeighborhoodFiltration D n ≤
      Ideal.span {x, y} ^ n ⊔ formalNeighborhoodFiltration D (n + 1))
    (hindep : ∀ (d : ℕ) (c : ℕ → formalNeighborhoodRing D),
      (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
        formalNeighborhoodFiltration D (d + 1) →
      ∀ j ≤ d, c j ∈ formalNeighborhoodFiltration D 1) :
    ExceptionalMonomialData D where
  gen₁ := x
  gen₂ := y
  mul_le := formalNeighborhoodFiltration_mul_le D
  span_le_ideal_one := hgen
  le_span_pow_sup := hspanPow
  monomials_indep := hindep
  quotient_isField := isField_quotient_of_isExceptionalCurveOfFirstKind D k hE hsurj

/-- The `ExceptionalMonomialData D` on the two generators of a monomial symbol `S` on the ring
of compatible functions whose filtration is `formalNeighborhoodFiltration D`, where `E` is an
exceptional curve of the first kind and the thickening restrictions are surjective. -/
public def ofMonomialSymbol (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m))
    (S : MonomialSymbol (formalNeighborhoodRing D) k)
    (hS : S.ideal = formalNeighborhoodFiltration D) :
    ExceptionalMonomialData D :=
  ofMonomialInputs (D := D) k hE hsurj S.gen₁ S.gen₂
    (span_gen_le_formalNeighborhoodFiltration_one D S hS)
    (formalNeighborhoodFiltration_le_span_gen_pow_sup D S hS)
    (gen_monomials_indep_formalNeighborhoodFiltration D S hS)

end ExceptionalMonomialData

variable (k : Type u) [Field k] {e : projectiveLineProj k ≅ D.subscheme}

/-- For an exceptional curve of the first kind on a Noetherian scheme, given the five inputs
`M : ExceptionalMonomialData D`, the ring of compatible global functions on the infinitesimal
thickenings is a Noetherian complete local ring. -/
@[stacks 0C2K
  "the complete Noetherian local clause, granting the five geometric inputs as \
`ExceptionalMonomialData`"]
public theorem isNoetherianCompleteLocalRing_formalNeighborhoodRing [IsNoetherian X]
    (_hE : IsExceptionalCurveOfFirstKind D k e) (M : ExceptionalMonomialData D) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) :=
  formalNeighborhoodRing_isNoetherianCompleteLocalRing D M.monomialFiltration

/-- For an exceptional curve of the first kind on a Noetherian scheme, given the five inputs
`M : ExceptionalMonomialData D`, the ring of compatible global functions on the infinitesimal
thickenings is a regular local ring. -/
@[stacks 0C2K
  "the regularity clause, granting the five geometric inputs as `ExceptionalMonomialData`"]
public theorem isRegularLocalRing_formalNeighborhoodRing [IsNoetherian X]
    (_hE : IsExceptionalCurveOfFirstKind D k e) (M : ExceptionalMonomialData D) :
    IsRegularLocalRing (formalNeighborhoodRing D) :=
  formalNeighborhoodRing_isRegularLocalRing D M.monomialFiltration

/-- For an exceptional curve of the first kind on a Noetherian scheme, given the five inputs
`M : ExceptionalMonomialData D`, the ring of compatible global functions on the infinitesimal
thickenings has Krull dimension `2`. -/
@[stacks 0C2K
  "the dimension clause, granting the five geometric inputs as `ExceptionalMonomialData`"]
public theorem ringKrullDim_formalNeighborhoodRing_eq_two [IsNoetherian X]
    (_hE : IsExceptionalCurveOfFirstKind D k e) (M : ExceptionalMonomialData D) :
    ringKrullDim (formalNeighborhoodRing D) = 2 :=
  formalNeighborhoodRing_ringKrullDim D M.monomialFiltration

/-- For an exceptional curve of the first kind on a Noetherian scheme, given the five inputs
`M : ExceptionalMonomialData D`, the kernel of the projection from the ring of compatible global
functions to the `(n + 1)`-st thickening is the `(n + 1)`-st power of its maximal ideal. -/
@[stacks 0C2K
  "the projection-kernel clause, granting the five geometric inputs as \
`ExceptionalMonomialData`"]
public theorem ker_formalNeighborhoodProjection_eq_maximalIdeal_pow_of_isExceptionalCurveOfFirstKind
    [IsNoetherian X] (_hE : IsExceptionalCurveOfFirstKind D k e)
    (M : ExceptionalMonomialData D) (n : ℕ) :
    letI : IsLocalRing (formalNeighborhoodRing D) := M.monomialFiltration.isLocalRing
    RingHom.ker (formalNeighborhoodProjection D n) =
      IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ (n + 1) :=
  ker_formalNeighborhoodProjection_eq_maximalIdeal_pow D M.monomialFiltration
    (M.monomialFiltration_ideal) n

end AlgebraicGeometry.Scheme.IdealSheafData

end
