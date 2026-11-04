module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe v u



/-!
# Projective resolutions of complexes

Let `C` be an abelian category. A *projective resolution* of a cochain complex
`K` of `C` is a cochain complex `P` together with a map `α : P ⟶ K` such that
`P` is bounded above, each term `P.X n` is a projective object of `C`, and `α`
is a quasi-isomorphism. This file defines that predicate.

The other half of the definition, a projective resolution of an *object*
`A : C` — a complex `P` with `P.X n = 0` for `n > 0` and projective terms, whose
map `P.X 0 ⟶ A` induces an isomorphism `Coker(d⁻¹) ≅ A` and which has vanishing
cohomology in negative degrees — is `CategoryTheory.ProjectiveResolution A`
(stated there with homological indexing, i.e. as a chain complex indexed by `ℕ`).
The two halves agree: for `R : CategoryTheory.ProjectiveResolution A` the map
`R.π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj A` satisfies
the predicate defined here, since `R.cochainComplex` is strictly `≤ 0` with
projective terms and `R.π'` is a quasi-isomorphism; this is a witness that the
predicate is not vacuous.

Faithfulness of the statement below.
1. Every hypothesis is used: the three fields are exactly the three conditions
   of the source, and none is implied by the others (a bounded above complex of
   projectives need not receive a quasi-isomorphism to `K`; a quasi-isomorphism
   from a bounded above complex need not have projective terms; a
   quasi-isomorphism from a complex of projectives need not be bounded above).
2. The base is the source's: `C` is an arbitrary abelian category, projectivity
   is `CategoryTheory.Projective` in `C`, cohomology is that of `C`, and no
   extra hypothesis (`EnoughProjectives`, boundedness of `K`) is assumed.
3. The map is pinned: the definition is a predicate on a *given* morphism
   `α : P ⟶ K`, so "let `α : P ⟶ K` be a projective resolution" is expressed
   directly, and existence of a resolution of `K` is the statement
   `∃ P (α : P ⟶ K), CochainComplex.IsProjectiveResolution α`.
4. Not degenerate: `R.π'` for `R : CategoryTheory.ProjectiveResolution A` is a
   witness, as explained above.

## Main definitions

* `CochainComplex.IsProjectiveResolution`: the predicate on a morphism of
  cochain complexes `α : P ⟶ K` saying that `α` exhibits `P` as a projective
  resolution of `K`.

## Implementation notes

The source phrases boundedness as `P.X n = 0` for `n ≫ 0`; this is recorded as
`∃ n : ℤ, P.IsStrictlyLE n`, which is Mathlib's spelling of the same condition
(`CochainComplex.isStrictlyLE_iff`). The class extends `QuasiIso α`, so the
Mathlib API for quasi-isomorphisms applies to a projective resolution without
further unfolding, and a resolution `P` is `K`-projective by
`CochainComplex.isKProjective_of_projective`.

## References

* [Stacks, Tag 0644]
-/

open CategoryTheory Limits



namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism of cochain complexes `α : P ⟶ K` in an abelian category is a
*projective resolution* of `K` if `P` is bounded above, all the terms of `P` are
projective objects, and `α` is a quasi-isomorphism. -/
@[stacks 0644 "The case of a complex; for an object it is `ProjectiveResolution`.",
  sga "4½ Etat_0 3.1.8" "projective case"]
public class IsProjectiveResolution {P K : CochainComplex C ℤ} (α : P ⟶ K) : Prop
    extends QuasiIso α where
  /-- The complex `P` is bounded above. -/
  exists_isStrictlyLE : ∃ n : ℤ, P.IsStrictlyLE n
  /-- Each term of the complex `P` is a projective object. -/
  projective (n : ℤ) : Projective (P.X n)

end CochainComplex
