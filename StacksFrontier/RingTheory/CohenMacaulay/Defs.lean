module

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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.RegularSequence
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
public import StacksFrontier.RingTheory.Depth.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Cohen–Macaulay modules and rings

Let `(R, 𝔪)` be a local ring and let `M` be an `R`-module. Then `M` is *maximal Cohen–Macaulay*
when `depth_𝔪(M) = dim(R)`, and *Cohen–Macaulay* when `depth_𝔪(M) = dim(Supp(M))`. Over a
commutative ring `R` that need not be local, `M` is *Cohen–Macaulay* when `M_𝔭` is a
Cohen–Macaulay `R_𝔭`-module for every prime `𝔭` in the support of `M`. A Noetherian local ring is
*Cohen–Macaulay* when it is Cohen–Macaulay as a module over itself, and a Noetherian ring is
*Cohen–Macaulay* when all its local rings are.

Depth takes values in `ℕ∞`, while `ringKrullDim` and `Module.supportDim` take values in
`WithBot ℕ∞`, the value `⊥` being reserved for the empty spectrum and the empty support; the
equations are therefore read in `WithBot ℕ∞`.

## Main definitions

* `Module.IsMaximalCohenMacaulay`: the property `depth_𝔪(M) = dim(R)` of a module `M` over a
  local ring `R`.
* `Module.IsCohenMacaulay`: the property of an `R`-module `M` that `M_𝔭` is a Cohen–Macaulay
  `R_𝔭`-module for every prime `𝔭` in the support of `M`.
* `Module.IsCohenMacaulayAtMaximalIdeal`: the property `depth_𝔪(M) = dim(Supp(M))` of a module
  `M` over a local ring `(R, 𝔪)`.
* `IsCohenMacaulayModule`: a finite module over a Noetherian local ring whose depth equals the
  Krull dimension of its support.
* `IsCohenMacaulayLocalRing`: a Noetherian local ring that is Cohen–Macaulay as a module over
  itself.
* `localRingDepth`: the depth of a local ring along its maximal ideal.
* `IsCohenMacaulayLocalRingPropForm`: a Noetherian local ring whose depth equals its Krull
  dimension.
* `IsCohenMacaulayRing`: a Noetherian ring all of whose localisations at primes are
  Cohen–Macaulay local rings.

## Implementation notes

The definitions are stated without the Noetherian and finiteness hypotheses of the Stacks
Project: the equations are meaningful without them, and the lemmas that need them assume them.
`Module.IsCohenMacaulay` imposes its condition at the primes of `Supp(M)` only, so the zero module
is Cohen–Macaulay; read at all primes, with `depth(0) = ∞` and `dim(∅) = -∞`, the condition of
Tag 0AAH would hold for no module whose support is a proper subset of `Spec(R)`. Cohen–Macaulayness
at a prime is spelled out as the equation of Tag 00N3 over `R_𝔭`, and the localisations are
`Localization.AtPrime 𝔭` and `LocalizedModule 𝔭.primeCompl M`.
`Module.IsCohenMacaulayAtMaximalIdeal` is written `depth_𝔪(M) = dim(Supp(M))`, the mirror image of
the equation of Tag 00N3.

## References

* [Stacks Project, Tag 00N3](https://stacks.math.columbia.edu/tag/00N3)
* [Stacks Project, Tag 00N8](https://stacks.math.columbia.edu/tag/00N8)
* [Stacks Project, Tag 00NC](https://stacks.math.columbia.edu/tag/00NC)
* [Stacks Project, Tag 00NF](https://stacks.math.columbia.edu/tag/00NF)
* [Stacks Project, Tag 0AAH](https://stacks.math.columbia.edu/tag/0AAH)

## Tags

Cohen-Macaulay module, maximal Cohen-Macaulay module, Cohen-Macaulay ring, depth, Krull dimension,
dimension of support, local ring, localization
-/

@[expose] public section

/-- **Maximal Cohen–Macaulay module.** A module `M` over a local ring `(R, 𝔪)` is *maximal
Cohen–Macaulay* if its depth along `𝔪` equals the Krull dimension of `R`,
`depth_𝔪(M) = dim(R)`, which for `R` Noetherian is the largest value the depth of a nonzero
finite `R`-module can take. The
source states this for `R` Noetherian and `M` finite; neither hypothesis is needed to state the
condition, so both are left to the lemmas, and under them this is the source's condition. The
depth is that of Tag 00LI, so the zero module has depth `∞` and, `dim(R)` being finite for a
Noetherian local ring, is not maximal Cohen–Macaulay, as in the source. -/
@[stacks 00NF "Stated without the Noetherian and finiteness hypotheses, which the lemmas assume \
  where needed; under them this is the source's condition, with the depth of Tag 00LI. See the \
  module docstring.",
  ega "IV 7.5.3"]
public def Module.IsMaximalCohenMacaulay (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*)
    [AddCommGroup M] [Module R M] : Prop :=
  (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = ringKrullDim R

end



/-! ## Cohen–Macaulay modules over a not necessarily local ring -/

@[expose] public section

namespace Module

/-- **Cohen–Macaulay module.** An `R`-module `M` is *Cohen–Macaulay* if for every prime `𝔭` in
the support of `M` the localisation `M_𝔭` is a Cohen–Macaulay module over the local ring `R_𝔭`,
that is `depth_{𝔭R_𝔭}(M_𝔭) = dim Supp(M_𝔭)`, the equation being read in `WithBot ℕ∞`. -/
@[stacks 0AAH "The condition is imposed at the primes of `Supp(M)` rather than at all primes of \
  `R`, the literal reading being vacuous for the source's own conventions on the zero module; \
  Cohen–Macaulayness at a prime is spelled out as the equation `depth_{𝔭R_𝔭}(M_𝔭) = \
  dim Supp(M_𝔭)` of Definition 00N3, there being no predicate for it in this library; the \
  localisations are the canonical models; and the Noetherian and finiteness hypotheses are \
  dropped, as in tags 00LI and 00NF. See the module docstring.",
  ega "0 16.5.13",
  ega "IV 5.7.1" "special case",
  ega "IV 7.5.3"]
public def IsCohenMacaulay (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ p ∈ support R M,
    (depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞) =
      supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

end Module

end



/-!
## Cohen–Macaulay modules over a local ring

For `M` finite with `𝔪 • M ≠ M` one always has `depth_𝔪(M) ≤ dim(Supp(M))`
(`Module.depth_le_supportDim`), so the condition says that the depth is as large as the support
allows.
-/

@[expose] public section

/-- **Cohen–Macaulay module over a local ring.** A module `M` over a local ring `(R, 𝔪)` is
*Cohen–Macaulay* if the dimension of its support equals its depth,
`dim(Supp(M)) = depth_𝔪(M)`, the equality being read in `WithBot ℕ∞` where `Module.supportDim`
lives. -/
@[stacks 00N3 "Stated without the Noetherian and finiteness hypotheses, as in tags 00LI, 00NF \
  and 0AAH; the equation is oriented `depth_𝔪(M) = dim Supp(M)`, the spelling of \
  Cohen–Macaulayness already used by tags 00LK, 00NF, 0AAG, 0AAH and 0C6G. The name records \
  that the depth is taken at the maximal ideal, `Module.IsCohenMacaulay` being Definition 0AAH \
  for a not necessarily local ring. See the module docstring.",
  ega "0 16.5.1" "CM module def",
  ega "IV 7.5.3"]
public def Module.IsCohenMacaulayAtMaximalIdeal (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M

end

/-!
## Cohen–Macaulay local rings

A Noetherian local ring `R` is called *Cohen–Macaulay* if it is Cohen–Macaulay as a module over
itself. The underlying notion of a Cohen–Macaulay module is that its depth (with respect to the
maximal ideal) equals the Krull dimension of its support.
-/

@[expose] public section

open Order

/-- A finite module `M` over a Noetherian local ring `R` is *Cohen–Macaulay* if
its depth with respect to the maximal ideal of `R` equals the Krull dimension
of its support inside `Spec R`. -/
@[ega "0 16.5.1" "CM module def", ega "IV 5.7.1" "F is Cohen–Macaulay at x", ega "IV 7.5.3"]
def IsCohenMacaulayModule (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : Prop :=
  Module.depthSup R (IsLocalRing.maximalIdeal R) M =
    (Order.krullDim (Module.support R M) : WithBot ℕ∞)

/-- A Noetherian local ring `R` is called *Cohen–Macaulay* if it is
Cohen–Macaulay as a module over itself. -/
@[stacks 00N8, ega "0 16.5.13" "local ring", ega "0 16.5.1", ega "IV 5.7.1", ega "IV 7.5.3"]
def IsCohenMacaulayLocalRing (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Prop :=
  IsCohenMacaulayModule R R

/-- A Noetherian local ring is Cohen–Macaulay precisely when it is Cohen–Macaulay as a module over
itself. -/
theorem isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ IsCohenMacaulayModule R R :=
  Iff.rfl

end

end

/-!
## Cohen–Macaulay rings

A Noetherian ring `R` is called *Cohen–Macaulay* if all its local rings are Cohen–Macaulay.
-/

@[expose] public section

/-- The depth of a (Noetherian local) commutative ring `R` is the supremum,
taken in `ℕ∞`, of the lengths of `R`-regular sequences whose entries all lie
in the maximal ideal of `R`. -/
@[ega "0 16.4.5" "special case", sga "2 III 2.8" "special case"]
noncomputable def localRingDepth (R : Type*) [CommRing R] [IsLocalRing R] : ℕ∞ :=
  ⨆ (s : { s : List R // (∀ x ∈ s, x ∈ IsLocalRing.maximalIdeal R) ∧
                          RingTheory.Sequence.IsRegular R s }),
    (s.val.length : ℕ∞)

/-- A Noetherian local ring is *Cohen–Macaulay* if its depth equals its Krull
dimension. -/
@[ega "0 16.5.1", ega "IV 5.7.1", ega "IV 7.5.3"]
def IsCohenMacaulayLocalRingPropForm (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  (localRingDepth R : WithBot ℕ∞) = ringKrullDim R

/-- A Noetherian ring `R` is *Cohen–Macaulay* if every localisation `R_𝔭` at a
prime ideal `𝔭` is a Cohen–Macaulay local ring. -/
@[stacks 00NC, ega "0 16.5.13", ega "IV 7.5.3"]
def IsCohenMacaulayRing (R : Type*) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime],
    IsCohenMacaulayLocalRingPropForm (Localization.AtPrime P)

/-- A Noetherian ring `R` is Cohen–Macaulay if and only if every localisation `R_𝔭` at a prime
ideal `𝔭` is a Cohen–Macaulay local ring. -/
theorem isCohenMacaulayRing_iff (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsCohenMacaulayRing R ↔
      ∀ (P : Ideal R) [P.IsPrime],
        IsCohenMacaulayLocalRingPropForm (Localization.AtPrime P) := Iff.rfl

end
