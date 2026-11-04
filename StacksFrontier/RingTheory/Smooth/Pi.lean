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
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.Pi
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

universe u v w

/-!
# Smoothness of a product of two algebras

Let `R` be a ring and let `S = S' × S''` be a product of two `R`-algebras. This file proves
Stacks 0GIF: `S` is smooth over `R`
if and only if both `S'` and `S''` are.

The two directions are different arguments. Forwards, each factor is a principal localization of
the product: `S'` is `S` away from the idempotent `e = (1, 0)` and `S''` is `S` away from the
complementary idempotent `1 - e = (0, 1)`, so `S → S'` is smooth and a composition of smooth ring
maps is smooth. This is the source's argument, with the two localizations read off the idempotents
rather than off the decomposition of `Spec S` into the standard opens `D(e)` and `D(1 - e)`.
Backwards, `S` is the dependent product of the `Bool`-indexed family with values `S'` and `S''`,
and both halves of smoothness are known for a finite dependent product:
`Algebra.FormallySmooth.pi_iff` for formal smoothness, `Algebra.FinitePresentation.pi` for finite
presentation.

## Main results

* `Stacks.Smooth.BinaryProduct.solution`: the proof of `Algebra.Smooth.prod_iff`, 0GIF.

## Implementation notes

*The second factor is not a second argument.* `Stacks.Smooth.BinaryProduct.smooth_of_prod` is
proved for the first factor only, and applied to `S'' × S'`; that the second factor is the
localization away from `(0, 1)` is the same statement transported along
`Stacks.Smooth.BinaryProduct.prodComm`.

*The two factors lie in independent universes, while `Algebra.FormallySmooth.pi_iff` forces one
universe on a family.* Only the backward direction passes through a family, and there the general
case is reduced to the equal-universe case by transporting along `ULift.algEquiv` on each factor,
which puts both of them in the join of the two universes; the transport is `AlgEquiv.prodCongr`,
which is universe-general. The forward direction needs no such reduction.

*Mathlib has `RingEquiv.prodComm` and `AlgEquiv.prodCongr` but no `AlgEquiv.prodComm`*, so
commuting the two factors of a product of algebras is done here by the private `prodComm`.

*The source's route through Lemmas 00TC and 00ED is not taken, so neither is imported.* Those
lemmas turn the two standard opens covering `Spec S` into a criterion checked one prime at a time.
The idempotent decomposition they encode is available algebraically: the projection `S → S'` makes
`S'` a localization of `S` away from `(1, 0)` (`IsLocalization.Away.away_fst`), and both halves of
smoothness are already known to descend along a localization away from an element. So no prime and
no statement about `Spec` occurs below.

## References

* [Stacks 0GIF](https://stacks.math.columbia.edu/tag/0GIF), Lemma 10.137.14
  (`algebra-lemma-product-smooth`). The source's proof is omitted, with hints citing Lemma 00TC
  (smoothness is checked one prime at a time) and Lemma 00ED (`Spec` of a product is the disjoint
  union of the `Spec`s of the factors); the argument formalized here is that same idempotent
  decomposition, taken algebraically.
-/



@[expose] public section

namespace Stacks.Smooth.BinaryProduct

/-- Commuting the two factors of a product of `R`-algebras: `RingEquiv.prodComm` as an
`AlgEquiv`. -/
private def prodComm (R : Type u) [CommRing R] (A : Type v) (B : Type w) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] : (A × B) ≃ₐ[R] B × A :=
  .ofRingEquiv (f := RingEquiv.prodComm) fun _ ↦ rfl

/-- **A factor of a smooth product is smooth.** The projection `A × B → A` makes `A` the
localization of `A × B` away from the idempotent `(1, 0)`, so it is smooth, and smoothness is
stable under composition. -/
private theorem smooth_of_prod (R : Type u) [CommRing R] (A : Type v) (B : Type w) [CommRing A]
    [Algebra R A] [CommRing B] [Algebra R B] [Algebra.Smooth R (A × B)] : Algebra.Smooth R A := by
  algebraize [RingHom.fst A B]
  have : IsScalarTower R (A × B) A := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Smooth (A × B) A := .of_isLocalization_Away (1, 0)
  exact .comp R (A × B) A

/-- The `Bool`-indexed family of types with value `A` at `true` and `B` at `false`, whose dependent
product is the binary product `A × B` (`Stacks.Smooth.BinaryProduct.pairFamilyPiAlgEquiv`). -/
private def pairFamily (A B : Type u) : Bool → Type u := (cond · A B)

/-- The commutative ring structure on each value of `pairFamily A B`. -/
@[instance_reducible]
private def pairFamilyCommRing (A B : Type u) [CommRing A] [CommRing B] :
    ∀ b, CommRing (pairFamily A B b) := Bool.rec ‹CommRing B› ‹CommRing A›

attribute [local instance] pairFamilyCommRing

/-- The `R`-algebra structure on each value of `pairFamily A B`. -/
@[instance_reducible]
private def pairFamilyAlgebra (R : Type v) (A B : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] : ∀ b, Algebra R (pairFamily A B b) :=
  Bool.rec ‹Algebra R B› ‹Algebra R A›

attribute [local instance] pairFamilyAlgebra

/-- The dependent product of `pairFamily A B` is the binary product `A × B`, as `R`-algebras. -/
private def pairFamilyPiAlgEquiv (R : Type v) (A B : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [CommRing B] [Algebra R B] : (∀ b : Bool, pairFamily A B b) ≃ₐ[R] A × B where
  toFun f := (f true, f false)
  invFun p := Bool.rec p.2 p.1
  left_inv f := by funext b; cases b <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' r := rfl

/-- **A product of two smooth algebras in the same universe is smooth**, being the dependent
product of `pairFamily`, for which Mathlib has both halves of smoothness. -/
private theorem smooth_prod (R : Type v) [CommRing R] (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra.Smooth R A] [Algebra.Smooth R B] :
    Algebra.Smooth R (A × B) :=
  have : ∀ b, Algebra.Smooth R (pairFamily A B b) := Bool.rec ‹_› ‹_›
  have : Algebra.Smooth R (∀ b : Bool, pairFamily A B b) := {}
  .of_equiv (pairFamilyPiAlgEquiv R A B)

/-- **A product of two algebras is smooth if and only if both factors are**: `S' × S''` is smooth
over `R` if and only if `S'` and `S''` both are. This is the proof of `Algebra.Smooth.prod_iff`. -/
public theorem solution (R : Type u) [CommRing R] (S' : Type v) [CommRing S']
    [Algebra R S'] (S'' : Type w) [CommRing S''] [Algebra R S''] :
    Algebra.Smooth R (S' × S'') ↔ Algebra.Smooth R S' ∧ Algebra.Smooth R S'' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h
    have : Algebra.Smooth R (S'' × S') := .of_equiv (prodComm R S' S'')
    exact ⟨smooth_of_prod R S' S'', smooth_of_prod R S'' S'⟩
  · have := h.1
    have := h.2
    have : Algebra.Smooth R (ULift.{w} S') := .of_equiv ULift.algEquiv.symm
    have : Algebra.Smooth R (ULift.{v} S'') := .of_equiv ULift.algEquiv.symm
    have := smooth_prod R (ULift.{w} S') (ULift.{v} S'')
    exact .of_equiv (AlgEquiv.prodCongr ULift.algEquiv ULift.algEquiv)

end Stacks.Smooth.BinaryProduct

end

/-!
# Smoothness of a product of two algebras

Let `R` be a ring and let `S = S' × S''` be a product of two `R`-algebras. Then `S` is smooth
over `R` if and only if both factors are.

The two factors of a product ring are its two principal localizations at the complementary
idempotents `e = (1, 0)` and `1 - e = (0, 1)`: multiplication by `e` identifies `S'` with `S_e`
and `S''` with `S_{1-e}`, and `Spec S` is correspondingly the disjoint union of the closed-and-open
subsets `D(e) = Spec S'` and `D(1 - e) = Spec S''` (Lemma 00ED). Both directions of the
equivalence read off this decomposition. Forwards, a principal localization of a smooth algebra is
smooth, since `S → S_g` is smooth and a composition of smooth ring maps is smooth (Lemma 00TD).
Backwards, `e` and `1 - e` generate the unit ideal of `S`, so every prime of `S` avoids one of
them, and smoothness may be checked one prime at a time (Lemma 00TC): at a prime `q` not
containing `e` the localization `S_e ≅ S'` is smooth over `R` by hypothesis, and symmetrically for
`1 - e`. The hints in the source are exactly this, phrased geometrically.

## Main results

* `Algebra.Smooth.prod_iff`: a product of two `R`-algebras is smooth over `R` if and only if each
  factor is, 0GIF.

## Implementation notes

*The product is the literal `S' × S''`, not an abstract `S` with an `R`-algebra isomorphism
`S ≃ₐ[R] S' × S''`.* The source's `S = S' × S''` is a presentation of `S`, and the two readings
are interchangeable: `Algebra.Smooth` transfers along an `AlgEquiv` in either direction, by
`Algebra.FormallySmooth.of_equiv` on the one field and `Algebra.FinitePresentation.equiv` on the
other. The literal product is the spelling of the Mathlib sibling `Algebra.FormallySmooth.pi_iff`,
and it is what a consumer holding a decomposition into idempotents produces.

*The two factors lie in independent universes.* Nothing in the mathematics ties them together, so
neither does the statement; the common-universe case is the instance `S'' : Type u` of it, and
conversely a proof at a common universe extends to this one by transporting along
`ULift.algEquiv`. This is where the statement is genuinely more general than
`Algebra.FormallySmooth.pi_iff`, whose family `A : I → Type w` forces one universe on all factors.

*What this adds to Mathlib's `Algebra.FormallySmooth.pi_iff`.* `Algebra.Smooth R S` is formal
smoothness together with `Algebra.FinitePresentation R S`, and Mathlib settles the first
conjunct in both directions (`Algebra.FormallySmooth.pi_iff`, at `I = Bool` or `Fin 2`) but the
second only backwards (`Algebra.FinitePresentation.pi`, for a finite family). The content here is
therefore that each factor of a finitely presented product algebra is itself finitely presented —
true because that factor is the principal localization `S_e`, and a principal localization of a
finitely presented algebra is finitely presented.

Faithfulness. (1) No hypothesis is dead: beyond the ring and `R`-algebra structures on `R`, `S'`
and `S''` there is none — no finiteness, no Noetherian, no nontriviality of either factor, and
the conclusion uses all three algebra structures. (2) The scalars and the base are the source's:
smoothness is over `R` itself in all three assertions, and the `R`-algebra structure on `S' × S''`
is the componentwise one, `Prod.algebra`, which is the product in `R`-algebras. (3) There is no
canonical map to pin: the source's `S = S' × S''` is an equality of `R`-algebras, realized here by
taking `S` to be the product itself, so the projections `S → S'` and `S → S''` are `Prod.fst` and
`Prod.snd` and the statement is about that `S` and no other. (4) The instantiation is not
degenerate: both sides hold for `S' = S'' = R` (so `S = R × R`, smooth over `R` as
`R[x]/(x² - x)`), and both fail for `S' = k`, `S'' = k[x]/(x²)` over `R = k` a field, so neither
direction is vacuous. The degenerate case `S'' = 0` is included and is consistent: the zero ring
is smooth over `R`, and `S' × 0 ≅ S'`.

## References

* [Stacks 0GIF](https://stacks.math.columbia.edu/tag/0GIF), Lemma 10.137.14
  (`algebra-lemma-product-smooth`), in Section 10.137 "Smooth ring maps". The source's proof is
  omitted there, with hints citing Lemma 00TC (smoothness is checked one prime at a time) and
  Lemma 00ED (`Spec` of a product is the disjoint union of the `Spec`s of the factors).
-/

@[expose] public section

/-- **A product of two algebras is smooth if and only if both factors are.** Let `R` be a ring and
let `S = S' × S''` be a product of `R`-algebras. Then `S` is smooth over `R` if and only if both
`S'` and `S''` are smooth over `R`.

Each factor is the principal localization of `S` at one of the complementary idempotents
`(1, 0)` and `(0, 1)`, which is why the equivalence holds; see the module docstring. -/
@[stacks 0GIF "The product is the literal `S' × S''`, with the componentwise `Prod.algebra`
structure; the abstract form (an `S` with `S ≃ₐ[R] S' × S''`) follows by transport, via
`Algebra.FormallySmooth.of_equiv` and `Algebra.FinitePresentation.equiv`. The two factors are
allowed to lie in different universes, so this is not an instance of Mathlib's
`Algebra.FormallySmooth.pi_iff`; that lemma also settles only the formal smoothness half, the
finite presentation of each factor of a finitely presented product being the content added here.
See the module docstring."]
public theorem Algebra.Smooth.prod_iff (R : Type*) [CommRing R] (S' : Type*) [CommRing S']
    [Algebra R S'] (S'' : Type*) [CommRing S''] [Algebra R S''] :
    Algebra.Smooth R (S' × S'') ↔ Algebra.Smooth R S' ∧ Algebra.Smooth R S'' :=
    by apply Stacks.Smooth.BinaryProduct.solution

end
