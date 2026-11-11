module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
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

universe u v



/-!
# Projective dimension of a module

Let `R` be a ring and let `M` be an `R`-module. Then `M` has *finite projective dimension* if
there is an exact sequence `0 → P_d → ⋯ → P_1 → P_0 → M → 0` with every `P_i` a projective
`R`-module, and the *projective dimension* of `M` is the least length `d` of such a resolution.
This file names that invariant `Module.projectiveDimension R M`, with values in `WithBot ℕ∞`, in
its Ext-theoretic form: the value is `≤ d` as soon as a resolution of length `d` exists, for any
`R`, and conversely, when `R` is small in `M`'s universe — so that `ModuleCat.{v} R` has enough
projectives (`ModuleCat.enoughProjectives`) — the bound `≤ d` produces such a resolution and the
value is `⊤` exactly when `M` admits no finite one, so that `M` has finite projective dimension
if and only if `Module.projectiveDimension R M ≠ ⊤`
(`CategoryTheory.projectiveDimension_ne_top_iff`).

## Main definitions

* `Module.projectiveDimension`: the projective dimension of an `R`-module `M`, an element of
  `WithBot ℕ∞`, measured by the vanishing of `Ext^i(M, -)` in high degrees.

## Implementation notes

Mathlib measures projective dimension by vanishing of `Ext`: for an object `X` of an abelian
category, `CategoryTheory.projectiveDimension X` is the least `n` with `Ext^i(X, -) = 0` for all
`i > n`. That is the shape the definition takes here, applied to the object `ModuleCat.of R M` of
`ModuleCat R`; the equivalence of this measure with the source's minimal length of a finite
projective resolution is the content of tags 00O5 and 0CXC, not of the definition. Because the
notion is therefore only a name for an existing one, it is an `abbrev`, and Mathlib's whole API
for `projectiveDimension` — invariance under linear equivalence, the behaviour along short exact
sequences, localization, and the local-global principle over a Noetherian ring — applies to it
verbatim, with `rw` and instance search seeing through the name. What the name adds is that the
source, and every tag around it, speaks of a bare module `M` with `[Module R M]` rather than of
an object of `ModuleCat R`.

For the zero module the conventions differ. The source's definition gives it projective
dimension `0`, the sequence `0 → 0 → 0` being a resolution of length `0` by projectives, and the
remark following the definition confirms this: projective dimension `0` holds exactly for the
projective modules, the zero module among them. Mathlib's value there is `⊥`
(`CategoryTheory.projectiveDimension_eq_bot_iff`), and accordingly
`Module.projectiveDimension R M = 0 ↔ Projective M ∧ M` nontrivial
(`CategoryTheory.projectiveDimension_eq_zero_iff`). The two conventions agree on every inequality
`pd M ≤ d` with `d : ℕ`, since `⊥ ≤ d`, so they agree on finite projective dimension and on the
resolutions that exist. They differ on an equality `pd M = d`: for `M = 0` the source's `pd M = 0`
is `pd M = ⊥` here, not `pd M = 0`. A source statement that assumes `pd M = d` is therefore
formalized faithfully with the hypothesis `pd M ≤ d` wherever the conclusion is monotone in `d`,
as for 00O5 (`pd_syzygy_projective_of_le`); an equality hypothesis would exclude the zero module.

The source's rings are commutative, but neither the notion nor Mathlib's API for it uses
commutativity, so only `[Ring R]` is assumed. The definition needs no smallness hypothesis to
elaborate, exactly as `CategoryTheory.projectiveDimension` does not: Ext-vanishing makes sense in
any abelian category, and `ModuleCat.{v} R` is abelian for every `R : Type u`. Smallness enters
with the identification of that measure with the source's resolution length, and it enters
through `ModuleCat.enoughProjectives`, an instance only under `[Small.{v} R]`: otherwise the free
module on a set indexed by `M` lands in `Type max u v`, `ModuleCat.{v} R` need contain no
projective object surjecting onto `M`, and Ext-vanishing yields no resolution. Every statement
relating the two therefore carries `[Small.{v} R]` — 00O5, 0CXC and 00O8 here, and in Mathlib
`ModuleCat.projectiveDimension_eq_of_linearEquiv`,
`ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule`,
`ModuleCat.projectiveDimension_eq_iSup_localizedModule_maximal` and
`ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum`. In particular the first of these
assumes `R` small in *both* universes, so it transports `M` between two universes in which `R` is
small rather than out of one in which it is not; it is not a licence to drop the hypothesis.
`ModuleCat.projectiveDimension_eq_zero_of_projective` is the one lemma of that API that needs no
smallness.

Faithfulness to the source. (1) No hypothesis is idle: the data are exactly `Ring R` and
`Module R M`, the data of the source's `R`-module `M`, and both occur in the value through
`ModuleCat.of R M`; there is no finiteness, Noetherian or projectivity hypothesis added, and
`Ring` rather than `CommRing` is the weakest form of the one the source uses. (2) The scalars and
base are the source's: the resolutions are by projective `R`-modules for the same ring `R`, and
the `Ext` groups are those of `ModuleCat R`, with no localization, completion or quotient of `R`
silently substituted. (3) The source names no canonical map here, and the number itself is
pinned rather than merely asserted to exist: it is the infimum of the `n` with `Ext^i(M, -) = 0`
for `i > n`, which for `R` small in `M`'s universe is by 0CXC the minimal length of a finite
projective resolution; the source's own predicate "has finite projective dimension" is pinned to
`≠ ⊤` by `CategoryTheory.projectiveDimension_ne_top_iff`, which reduces it to the existence of a
bound, together with 0CXC turning that bound into a resolution. (4) The instantiation is not
degenerate, and the invariant is not constant: `Module.projectiveDimension R R = 0` for `R`
nonzero, `R` being then a projective module and nonzero over itself;
`Module.projectiveDimension ℤ (ZMod 2) = 1`, from `0 → ℤ → ℤ → ZMod 2 → 0`; and for
`R = k[x]/(x²)` over a field `k` the module `R/(x)` has
`Module.projectiveDimension R (R/(x)) = ⊤`, which is the source's own example of a module of
infinite projective dimension (More on Algebra, Example 0A5Q).

## References

* [Stacks Project, Tag 00O4](https://stacks.math.columbia.edu/tag/00O4)
-/

@[expose] public section



/-- The **projective dimension** of an `R`-module `M`: the least `d` with `Ext^i(M, -) = 0` for
all `i > d`. For `R` small in `M`'s universe this is the source's invariant, the least `d` for
which there is an exact sequence `0 → P_d → ⋯ → P_0 → M → 0` with all `P_i` projective (00O5,
0CXC), and `M` then has *finite projective dimension* in the sense of the source exactly when
this is `≠ ⊤` (`CategoryTheory.projectiveDimension_ne_top_iff`). It is `⊥` for the zero module,
whose projective dimension in the source is `0`. -/
@[stacks 00O4, ega "0 17.2.1" "dim.proj definition"]
public noncomputable abbrev Module.projectiveDimension (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension (ModuleCat.of R M)

end
