module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

universe u



/-!
# Global dimension of a ring

A ring `R` has *finite global dimension* if there is an integer `n` such that every `R`-module `M`
admits a resolution `0 → P_n → ⋯ → P_1 → P_0 → M → 0` by projective `R`-modules, and the *global
dimension* of `R` is then the least such `n`. This file defines that invariant,
`ringGlobalDimension R`, as the supremum of the projective dimensions of all `R`-modules, an
element of `WithBot ℕ∞`. The supremum *is* the least such bound: it is `≤ n` exactly when every
`R`-module has projective dimension `≤ n`, and `R` has finite global dimension in the sense above
exactly when `ringGlobalDimension R ≠ ⊤`.

## Main definitions

* `ringGlobalDimension`: the global dimension of a ring `R`, the supremum over all `R`-modules of
  their projective dimension.

## Implementation notes

The source phrases the definition as the minimum of the set of uniform bounds `n`, together with
the separate predicate "has finite global dimension" asserting that some bound exists. A supremum
carries both: `iSup_le_iff` and `CategoryTheory.projectiveDimension_le_iff` give
`ringGlobalDimension R ≤ n ↔ ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M n`, so the value is
the least uniform bound, and since every element of `WithBot ℕ∞` other than `⊤` is `≤ n` for some
`n : ℕ`, they give `ringGlobalDimension R ≠ ⊤ ↔ ∃ n, ∀ M, HasProjectiveDimensionLE M n`, which is
the source's "finite global dimension". No separate predicate is therefore introduced. That the
bound `HasProjectiveDimensionLE M n` is the source's *resolution* of length `≤ n` — projective
dimension being measured in Mathlib by the vanishing of `Ext^i(M, -)` for `i > n` — is the content
of Tags 00O5 and 0CXC, not of this definition; see also Tag 00O4 for the per-module invariant.

Because the definition is only a name for a supremum, it is an `abbrev`: Mathlib's `iSup` API
(`le_iSup`, `iSup_le`, `iSup_le_iff`, `iSup_eq_bot`) applies to it verbatim, so a reader never
unfolds it, and the mathematics about it — that finite modules, or even the cyclic modules `R/I`,
already compute it (Tag 065T), and that a regular local ring has global dimension its dimension
(Tag 00O7) — belongs to those tags. The codomain is `WithBot ℕ∞`, matching both
`CategoryTheory.projectiveDimension` and `ringKrullDim`; as for `ringKrullDim`, the value is `⊥`
exactly for the zero ring, all of whose modules are zero, where reading the source literally would
give `0`. The two conventions agree on every inequality `≤ n`, hence on finite global dimension
and on the resolutions that exist.

The modules are taken in the universe of `R` itself. Nothing is lost: `Small.{u} R` then holds
automatically, so `ModuleCat.{u} R` has enough projectives without a hypothesis, and by Tag 065T a
bound over the cyclic modules `R/I`, which live in `Type u`, is a bound over all `R`-modules in
any universe in which `R` is small. This is the same universe convention as Tag 00O7, whose
conclusion `∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M d` is the statement
`ringGlobalDimension R ≤ d`.

The source's rings are commutative, but neither the notion nor Mathlib's API for projective
dimension uses commutativity, so only `[Ring R]` is assumed, as in Tag 0CXE. Since `ModuleCat R`
is the category of *left* `R`-modules, this is the left global dimension; the two sides agree for
the source's commutative rings, and more generally for left and right Noetherian rings, but not
for every ring.

Faithfulness to the source. (1) No hypothesis is idle: the only datum is `Ring R`, the source's
ring, and it occurs in the value through `ModuleCat R`; no finiteness, Noetherian or projectivity
hypothesis is added, and `Ring` is the weakest form of the one the source uses. (2) The scalars
and the base are the source's: the supremum ranges over the `R`-modules for that same `R` and the
projective dimensions are those of `ModuleCat R`, with no localization, quotient or completion of
`R` substituted. (3) The source names no canonical map, and the number is pinned rather than
merely asserted to exist: it is the supremum, hence the least `n` bounding every module's
projective dimension, and the source's predicate "has finite global dimension" is pinned to
`ringGlobalDimension R ≠ ⊤`. (4) The instantiation is not degenerate and the invariant is not
constant: `ringGlobalDimension k = 0` for a field `k`, every module over `k` being free and `k`
itself nonzero; `ringGlobalDimension ℤ = 1`, from `0 → ℤ → ℤ → ℤ/2ℤ → 0` and the fact that
submodules of free `ℤ`-modules are free; a regular local ring of dimension `d` has global
dimension `d` (Tag 00O7); and `ringGlobalDimension (k[x]/(x²)) = ⊤`, the residue field `k` having
infinite projective dimension there.

## References

* [Stacks Project, Tag 00O6](https://stacks.math.columbia.edu/tag/00O6)
-/

@[expose] public section



open CategoryTheory in
/-- The **global dimension** of a ring `R`: the supremum of the projective dimensions of all
`R`-modules, an element of `WithBot ℕ∞`. It is `≤ n` exactly when every `R`-module admits a
resolution of length `≤ n` by projective modules (00O5, 0CXC), so it is the source's minimal such
`n`, and `R` has *finite global dimension* exactly when `ringGlobalDimension R ≠ ⊤`. It is `⊥`
for the zero ring. -/
@[stacks 00O6 "The global dimension is the supremum `⨆ M, projectiveDimension M` over the
`R`-modules in `R`'s own universe; `R` has finite global dimension iff this is `≠ ⊤`. See the
module docstring."]
public noncomputable abbrev ringGlobalDimension (R : Type u) [Ring R] : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{u} R, projectiveDimension M

end
