module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

/-!
# Global and local complete intersections over a field

Let `k` be a field. A `k`-algebra `S` is a *global complete intersection* over `k` if either `S` is
the zero ring or there are `n, c ≥ 0` and an isomorphism of `k`-algebras
`S ≅ k[x_1, …, x_n]/(f_1, …, f_c)` with `dim S = n - c`, and a *local complete intersection* over
`k` if there is a family `(g_i)` of elements of `S` with `Spec S = ⋃_i D(g_i)` each of whose
localizations `S_{g_i}` is a global complete intersection over `k`.

Here `S_g` is the localization `S[g⁻¹]` at `{1, g, g², …}` (`Localization.Away g`), `D(g)` is the
standard open `{p ∈ Spec S | g ∉ p}` (`PrimeSpectrum.basicOpen g`), and `dim S` is the Krull
dimension `ringKrullDim S`.

## Main definitions

* `IsGlobalCompleteIntersection`: `S` is a global complete intersection over `k`.
* `IsLocalCompleteIntersection`: `S` is a local complete intersection over `k`.
* `IsCompleteIntersection`: `S` is isomorphic to the quotient of a regular local `k`-algebra,
  essentially of finite type over `k`, by a regular sequence.
* `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`: a presentation
  `S = R[x_1, …, x_n]/(f_1, …, f_c)` all of whose nonempty fibres have dimension `n - c`.
* `Algebra.IsRelativeGlobalCompleteIntersection`: `S` admits such a presentation over `R`.

## Implementation notes

A finite type hypothesis on `S` is not imposed, being a consequence:
`IsGlobalCompleteIntersection.finiteType` reads it off a presentation, and the zero ring is finite
over `k`.

The dimension condition `dim S = n - c` is recorded as `c ≤ n` together with
`ringKrullDim S = ((n - c : ℕ) : WithBot ℕ∞)`, the natural-number difference, which agrees with
the genuine difference because `dim S = n - c ≥ 0` in the nonzero case.

The covering condition of the local notion is `Ideal.span s = ⊤`; that it says exactly that the
`D(g)` for `g ∈ s` cover `Spec S` is `localCompleteIntersection_cover_iff`.

## References

* [Stacks 00S9](https://stacks.math.columbia.edu/tag/00S9)
* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD)
* [Stacks 00SP](https://stacks.math.columbia.edu/tag/00SP)
-/

@[expose] public section

universe u v

/-- Let `k` be a field. A `k`-algebra `S` is a *global complete intersection over `k`* if either
`S` is the zero ring (`Subsingleton S`), or there are `n, c ≥ 0` and an isomorphism of
`k`-algebras `S ≃ₐ[k] k[x_1, …, x_n]/(f_1, …, f_c)` with `dim S = n - c`.

Here `k[x_1, …, x_n]` is `MvPolynomial (Fin n) k`, the relations `(f_1, …, f_c)` are the ideal
`Ideal.span (Set.range f)` for `f : Fin c → MvPolynomial (Fin n) k`, and the dimension condition
is `c ≤ n` together with `ringKrullDim S = ((n - c : ℕ) : WithBot ℕ∞)`. -/
@[stacks 00S9 "(1)"]
public def IsGlobalCompleteIntersection (k : Type*) [Field k] (S : Type*) [CommRing S]
    [Algebra k S] : Prop :=
  Subsingleton S ∨
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
      (_ : S ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f))),
      c ≤ n ∧ ringKrullDim S = ((n - c : ℕ) : WithBot ℕ∞)

/-- Let `k` be a field. A `k`-algebra `S` is a *local complete intersection over `k`* if there is
a set `s ⊆ S` whose standard opens `D(g)` cover `Spec S`, and such that `S_g = Localization.Away g`
is a global complete intersection over `k` for every `g ∈ s`.

The covering condition is recorded algebraically as `Ideal.span s = ⊤`;
`localCompleteIntersection_cover_iff` is its equivalence with `⨆ g ∈ s, D(g) = ⊤`. -/
@[stacks 00S9 "(2)", ega "IV 19.3.6", sga "6 0 3.2" "special case"]
public def IsLocalCompleteIntersection (k : Type*) [Field k] (S : Type*) [CommRing S]
    [Algebra k S] : Prop :=
  ∃ s : Set S, Ideal.span s = ⊤ ∧
    ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)

/-!
# Complete intersections over a field

Let `k` be a field. A local `k`-algebra `S` essentially of finite type over `k` is a *complete
intersection over `k`* if it can be written as `R/(f_1, …, f_c)` for some regular local
`k`-algebra `R`, essentially of finite type over `k`, and some regular sequence `f_1, …, f_c`
in the maximal ideal of `R`.

The length `c` of the regular sequence is not part of the data, and `c = 0` is allowed: a
regular local `k`-algebra essentially of finite type over `k` is a complete intersection over
`k`, the ambient ring `R` being `S` itself. In particular `k` is one.

## Main definitions

* `IsCompleteIntersection`: `S` is a complete intersection over `k`.

## Implementation notes

The hypotheses that `S` be local and essentially of finite type over `k` are not imposed: both
follow from the existence of `R`. The ideal `(f_1, …, f_c)` is proper, so `R/(f_1, …, f_c)` is a
nonzero quotient of a local ring, hence local, and it is essentially of finite type over `k`
because `R` is.

The condition `f_1, …, f_c ∈ 𝔪_R` is not stated separately: `RingTheory.Sequence.IsRegular R fs`
asks each `f_i` to be a nonzerodivisor on `R/(f_1, …, f_{i-1})` and `R/(f_1, …, f_c) ≠ 0`, and over
the local ring `R` the second clause says precisely that every `f_i` lies in `𝔪_R`
(`IsLocalRing.le_maximalIdeal`).

Sequences are `List R`, as in Mathlib's regular sequence API, and `(f_1, …, f_c)` is
`Ideal.ofList fs = Ideal.span {f | f ∈ fs}`. The number `c` is `fs.length`.

The witness ring is quantified in the universe of `k`. A `k`-algebra essentially of finite type
over `k` is a localization of a quotient of `k[x_1, …, x_n]`, so it is isomorphic to one carried
by a type in the universe of `k`.

## References

* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD)
-/

@[expose] public section



/-- Let `k` be a field. A `k`-algebra `S` is a *complete intersection over `k`* if there are a
regular local `k`-algebra `R`, essentially of finite type over `k`, and a regular sequence
`f_1, …, f_c` in `R` such that `S ≃ₐ[k] R/(f_1, …, f_c)`. The condition `f_1, …, f_c ∈ 𝔪_R` is
contained in `RingTheory.Sequence.IsRegular`, which asks the quotient `R/(f_1, …, f_c)` to be
nonzero. -/
@[stacks 00SD "Items (1)-(4) are the four clauses of the body, in order. The source's condition
`f_1, …, f_c ∈ 𝔪_R` is not stated separately: over the local ring `R` it is equivalent, given
item (3), to the nonvanishing of `R/(f_1, …, f_c)` that Mathlib's `RingTheory.Sequence.IsRegular`
already carries. The source's hypotheses that `S` be local and essentially of finite type over
`k` are omitted, both being consequences of the existence of `R`, as with the finite type
hypothesis in Definition 00S9. The witness `R` is quantified in the universe of `k`. See the
module docstring."]
public def IsCompleteIntersection (k : Type u) [Field k] (S : Type v) [CommRing S]
    [Algebra k S] : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R) (_ : IsRegularLocalRing R)
    (_ : Algebra.EssFiniteType k R) (fs : List R),
    RingTheory.Sequence.IsRegular R fs ∧ Nonempty (S ≃ₐ[k] R ⧸ Ideal.ofList fs)

end



/-!
# Relative global complete intersections

A ring map `R → S` is a *relative global complete intersection* if `S` admits a presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` such that every nonempty fibre of `Spec(S) → Spec(R)` has
dimension `n - c`. The definition is given in two layers: the property
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection` of a presentation, and the class
`Algebra.IsRelativeGlobalCompleteIntersection` of ring maps admitting such a presentation.

The fibre of `Spec(S) → Spec(R)` over a prime `p` of `R` is the spectrum of the fibre ring
`κ(p) ⊗_R S`, so the condition is that `dim(κ(p) ⊗_R S) = n - c` for every prime `p` whose fibre
ring is nonzero. Nothing is required over a prime with empty fibre; in particular the zero ring is
a relative global complete intersection over any ring, presented as `R[x_1]/(1)`.

## Main definitions

* `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`: a presentation
  `S = R[x_1, …, x_n]/(f_1, …, f_c)` all of whose nonempty fibres have dimension `n - c`.
* `Algebra.IsRelativeGlobalCompleteIntersection`: `S` admits such a presentation.

## Implementation notes

The notion is stated for an `R`-algebra, as Mathlib states `Algebra.Smooth`; for a ring map
`f : R →+* S` it is `Algebra.IsRelativeGlobalCompleteIntersection R S` for `f.toAlgebra`.

The presentation is Mathlib's `Algebra.Presentation R S ι σ`: a surjection
`R[x_1, …, x_n] → S` together with `f_1, …, f_c` spanning its kernel. The property is stated for
arbitrary finite index types, the numbers of variables and relations being `Nat.card ι` and
`Nat.card σ`, while the existential in the class ranges over `Fin n` and `Fin c`.

The fibre ring is `Ideal.Fiber p S = κ(p) ⊗_R S`; `PrimeSpectrum.preimageHomeomorphFiber` is a
homeomorphism between the fibre of `Spec(S) → Spec(R)` over `p` and `Spec(κ(p) ⊗_R S)`.

The dimension condition is the equation `dim + c = n` in `WithBot ℕ∞`, not
`dim = Algebra.Presentation.dimension`, which is the truncated natural subtraction `n - c`: the
ring `k[x, y]/(x, y)^2`, presented by `x^2, xy, y^2` with `n = 2` and `c = 3`, has a fibre of
dimension `0 = 2 - 3` in `ℕ` but is not a complete intersection. Written additively the condition
also makes `c ≤ n` automatic as soon as one fibre is nonempty.

Nonemptiness of a fibre is `Nontrivial (p.Fiber S)` (`PrimeSpectrum.nonempty_iff_nontrivial`).
Over a prime with `Subsingleton (p.Fiber S)` the Krull dimension of the fibre ring is `⊥`, and
`⊥ + c = ⊥ ≠ n`, so the hypothesis cannot be dropped.

Finite presentation is not assumed, being a consequence of
`Algebra.Presentation.finitePresentation_of_isFinite`.

## References

* [Stacks 00SP](https://stacks.math.columbia.edu/tag/00SP)
-/

@[expose] public section

/-- A presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` of `S` over `R` **is a relative global
complete intersection** if every nonempty fibre of `Spec(S) → Spec(R)` has dimension `n - c`.

The number of variables is `n = Nat.card ι` and the number of relations is `c = Nat.card σ`, the
fibre over a prime `p` of `R` is the spectrum of `p.Fiber S = κ(p) ⊗_R S`, it is nonempty exactly
when that ring is nonzero, and `dim = n - c` is written as the equation
`ringKrullDim (p.Fiber S) + c = n` in `WithBot ℕ∞`. -/
@[stacks 00SP "The source's displayed `S = R[x_1, …, x_n]/(f_1, …, f_c)`, a presentation together
with the dimension property of its fibres; `Algebra.IsRelativeGlobalCompleteIntersection` is the
property of the ring map, defined through this one. Stated for arbitrary finite index types, with
`n = Nat.card ι` and `c = Nat.card σ`. The fibre ring is `Ideal.Fiber p S = κ(p) ⊗[R] S`, and
`dim = n - c` is written additively as `ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι` in
`WithBot ℕ∞` rather than with the truncated subtraction `Algebra.Presentation.dimension`. See the
module docstring."]
public class Algebra.Presentation.IsRelativeGlobalCompleteIntersection {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) : Prop where
  /-- For every prime `p` of `R` with nonzero fibre ring `κ(p) ⊗_R S`, the dimension of the fibre
  over `p` equals the number of variables minus the number of relations, written additively. -/
  ringKrullDim_fiber_add_card_eq_card : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
    ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι

/-- A ring map `R → S` is a **relative global complete intersection** if there is a presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` such that every nonempty fibre of `Spec(S) → Spec(R)` has
dimension `n - c`, that is, a presentation satisfying
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection`. -/
@[stacks 00SP "Stated for an `R`-algebra `S`, as Mathlib states `Algebra.Smooth` and as the
sibling `Algebra.Syntomic` (00SL) is stated; for a ring map `f : R →+* S` it is
`Algebra.IsRelativeGlobalCompleteIntersection R S` at `f.toAlgebra`. The presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` is `Algebra.Presentation R S (Fin n) (Fin c)` and the dimension
condition on it is `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`, through which this
one is defined, as Mathlib defines `Algebra.IsStandardSmoothOfRelativeDimension` through
`Algebra.SubmersivePresentation`. See the module docstring."]
public class Algebra.IsRelativeGlobalCompleteIntersection (R : Type*) [CommRing R] (S : Type*)
    [CommRing S] [Algebra R S] : Prop where
  /-- There is a presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` of `S` over `R` all of whose
  nonempty fibres have dimension `n - c`. -/
  out : ∃ (n c : ℕ) (P : Algebra.Presentation R S (Fin n) (Fin c)),
    P.IsRelativeGlobalCompleteIntersection

end
