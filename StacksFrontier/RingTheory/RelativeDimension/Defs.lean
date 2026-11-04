module

public import StacksFrontier.Topology.Dimension.Krull
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
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section



/-!
# Relative dimension of a ring map at a prime

Let `R → S` be a ring map and let `𝔮` be a prime of `S`, lying over the prime
`𝔭 = R ∩ 𝔮` of `R`. The fibre of `Spec S → Spec R` over `𝔭` is `Spec (S ⊗_R κ(𝔭))`, and it
contains a point corresponding to `𝔮`. The *relative dimension of `S/R` at `𝔮`*, written
`dim_𝔮(S/R)`, is the dimension of that fibre at that point, in the sense of the dimension of a
topological space at a point (Stacks 0055 (4)). The *relative dimension of `S/R`* is
`dim(S/R) = sup_𝔮 dim_𝔮(S/R)`, the supremum over all primes `𝔮` of `S`.

Both dimensions are valued in `WithBot ℕ∞ = {-∞} ∪ ℤ≥0 ∪ {+∞}`, the value type of
`topologicalKrullDim`. A fibre through `𝔮` is nonempty, containing `𝔮`, so `dim_𝔮(S/R) ≠ -∞`
always, whereas `dim(S/R) = -∞` exactly when `S` is the zero ring.

## Main definitions

* `Algebra.relativeDimensionAt`: the relative dimension `dim_𝔮(S/R)` of `S/R` at a prime `𝔮`
  of `S`.
* `Algebra.relativeDimension`: the relative dimension `dim(S/R)` of `S/R`, the supremum of
  `dim_𝔮(S/R)` over all primes `𝔮` of `S`.

## Implementation notes

The fibre is taken as the subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S` rather than as
the space `Spec (S ⊗_R κ(𝔭))`: the two are homeomorphic by
`PrimeSpectrum.preimageHomeomorphFiber`, and the dimension of a space at a point is a
homeomorphism invariant, so the value is the source's; the gain is that the subspace carries
the source's "point corresponding to `𝔮`" as `𝔮` itself, so no point has to be transported
along the homeomorphism and `dim_𝔮(S/R)` is a function of `𝔮` alone. It is also the form the
fibre takes in Mathlib's quasi-finiteness API
(`Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton`), against which the remark following
the source's definition — that `R → S` is quasi-finite at `𝔮` if and only if
`dim_𝔮(S/R) = 0` — is to be read.

The prime `𝔭` is not an argument: it is `𝔮.under R`, here written as
`PrimeSpectrum.comap (algebraMap R S) 𝔮` so that membership of `𝔮` in its own fibre holds by
`rfl`. The dimension at a point is `topologicalKrullDimAt`, this project's form of Stacks
0055 (4), an infimum over open neighbourhoods that `topologicalKrullDimAt_isLeast` shows to be
the minimum the source asks for.

The source assumes `R → S` of finite type. Neither definition uses that hypothesis, so neither
carries it; finite type is assumed instead by the lemmas about relative dimension, where it is
what makes the fibres of finite type over `κ(𝔭)` and the dimensions finite.

Faithfulness. (1) No datum is inert: `R`, `S` and the algebra structure enter through the fibre
of `comap (algebraMap R S)`, and `𝔮` both selects the fibre and is the point at which the
dimension is taken; the supremum in `relativeDimension` ranges over all primes of `S`, as the
source's does. (2) The scalars and base are the source's: the fibre is the one over
`𝔭 = R ∩ 𝔮` for the given `R`-algebra structure on `S`, not over a localization or a quotient
of `R`. (3) The point of the fibre is pinned, not merely asserted to exist: it is `𝔮` viewed in
`comap (algebraMap R S) ⁻¹' {comap (algebraMap R S) 𝔮}`, which corresponds to the source's
`q̄ ∈ Spec (S ⊗_R κ(𝔭))` under `PrimeSpectrum.preimageHomeomorphFiber`. (4) The definitions are
not degenerate: for `R = k` a field and `S = k[x, y]` each fibre is `Spec S` itself, which is
irreducible of dimension `2`, so `dim_𝔮(S/R) = 2` for every prime 𝔮 and `dim(S/R) = 2`; for
`R = ℤ` and `S = ℤ[x]` the fibre over `(5)` is `Spec 𝔽₅[x]`, so `dim_𝔮(S/R) = 1` for every 𝔮
over `(5)`, closed point or not, the dimension at a point being a minimum over neighbourhoods,
and `dim(S/R) = 1`; and for `S = ℤ[x]/(x² - 2)`, quasi-finite over `ℤ`, every fibre is finite
and discrete, so `dim(S/R) = 0`.

## References

* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)

## Tags

relative dimension, fibre, dimension at a point
-/

@[expose] public section

namespace Algebra

/-- The **relative dimension of `S/R` at a prime `𝔮` of `S`**, `dim_𝔮(S/R)`: the dimension of
the fibre of `Spec S → Spec R` through `𝔮` at the point `𝔮`. The fibre is the subspace
`comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, where `𝔭 = R ∩ 𝔮`, which is homeomorphic to
`Spec (S ⊗_R κ(𝔭))` by `PrimeSpectrum.preimageHomeomorphFiber`. -/
@[stacks 00QD "The fibre `Spec (S ⊗_R κ(𝔭))` is the homeomorphic subspace
`comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, in which the source's point `q̄` is `𝔮` itself,
and `𝔭 = R ∩ 𝔮` is not an argument; `dim_q̄` is `topologicalKrullDimAt`. The source's finite
type hypothesis is unused by the definition and is left to the lemmas. See the module
docstring.", ega "IV 17.10.1" "affine case"]
public noncomputable def relativeDimensionAt (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔮 : Ideal S) [𝔮.IsPrime] : WithBot ℕ∞ :=
  topologicalKrullDimAt
    ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        {PrimeSpectrum.comap (algebraMap R S) ⟨𝔮, ‹_›⟩}) ⟨⟨𝔮, ‹_›⟩, rfl⟩

/-- The **relative dimension of `S/R`**, `dim(S/R)`: the supremum of the relative dimensions
`dim_𝔮(S/R)` over all primes `𝔮` of `S`. It is `-∞` exactly when `S` is the zero ring. -/
@[stacks 00QD "The supremum of `Algebra.relativeDimensionAt R 𝔮` over all primes `𝔮` of `S`,
indexed by `Spec S`. See the module docstring."]
public noncomputable def relativeDimension (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : WithBot ℕ∞ :=
  ⨆ 𝔮 : PrimeSpectrum S, relativeDimensionAt R 𝔮.asIdeal

end Algebra

end
