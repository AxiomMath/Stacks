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

/-!
# Functoriality of the naive cotangent complex in a square of rings

A commutative square of rings
```
S --φ--> S'
↑        ↑
R -----> R'
```
together with presentations `α : P → S` of `S` over `R` and `α' : P' → S'` of `S'` over `R'`
is the datum for a morphism of presentations from `α` to `α'`, and hence for a map of naive
cotangent complexes `NL(α) → NL(α')`. This file proves that the construction is compatible with
stacking two such squares: for the canonical presentation `R'[S'] → S'` of an intermediate
algebra, the composite of the two canonical comparison morphisms `P → R'[S']` and `R'[S'] → P''`
is the canonical comparison morphism `P → P''` of the outer square.

The proof is a computation on the images of the variables, the only datum a morphism of
presentations carries. The canonical comparison morphism `Algebra.Generators.defaultHom P P'`
sends the variable `i` to `P'.σ (algebraMap S S' (P.val i))`, and the section of the canonical
presentation `Algebra.Generators.self R' S'` is `MvPolynomial.X`. So the composite sends `i` to
`P''.σ (algebraMap S' S'' (algebraMap S S' (P.val i)))`, whereas the comparison morphism of the
outer square sends it to `P''.σ (algebraMap S S'' (P.val i))`; the two agree because the top row
of the diagram commutes, which is `IsScalarTower S S' S''`.

## Main results

* `Stacks.NaiveCotangent.Functoriality.solution`: the statement of Stacks 06RQ, namely
  `Algebra.Generators.defaultHom_comp_defaultHom`.

## Implementation notes

Only the intermediate presentation has to be the canonical one: what the argument uses is that
its section is `MvPolynomial.X`, defined at the level of variables, so the two outer
presentations are arbitrary. The source's claim is the case `P = self R S`, `P'' = self R'' S''`.

## References

* [StacksProject 06RQ](https://stacks.math.columbia.edu/tag/06RQ)
-/

@[expose] public section

namespace Stacks.NaiveCotangent.Functoriality

/-- The canonical comparison morphism of presentations `P → P''` factors through the canonical
presentation `R'[S'] → S'` of an intermediate algebra: the composite of the canonical comparison
morphisms `P → R'[S']` and `R'[S'] → P''` is `Algebra.Generators.defaultHom P P''`. -/
public theorem solution {R S R' S' R'' S'' ι ι'' : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [CommRing R'] [CommRing S'] [Algebra R' S']
    [CommRing R''] [CommRing S''] [Algebra R'' S'']
    [Algebra R' R''] [Algebra R' S''] [Algebra S S'] [Algebra S' S''] [Algebra S S'']
    [IsScalarTower R' R'' S''] [IsScalarTower R' S' S''] [IsScalarTower S S' S'']
    (P : Algebra.Generators R S ι) (P'' : Algebra.Generators R'' S'' ι'') :
    (Algebra.Generators.defaultHom (Algebra.Generators.self R' S') P'').comp
        (Algebra.Generators.defaultHom P (Algebra.Generators.self R' S')) =
      Algebra.Generators.defaultHom P P'' := by
  ext i
  simp [IsScalarTower.algebraMap_apply S S' S'']

end Stacks.NaiveCotangent.Functoriality

end

/-!
# Functoriality of the naive cotangent complex in a commutative square of rings

A commutative square of rings
```
S --φ--> S'
↑        ↑
R -----> R'
```
together with presentations `α : P → S` of `S` over `R` and `α' : P' → S'` of `S'` over `R'`
is the datum for which the naive cotangent complex is functorial. A *morphism of presentations*
from `α` to `α'` is an `R`-algebra map `φ̃ : P → P'` with `φ ∘ α = α' ∘ φ̃`; it carries
`I = ker α` into `I' = ker α'`, hence induces `I/I² → I'/(I')²` and, by functoriality of
differentials, `Ω_{P/R} ⊗_P S → Ω_{P'/R'} ⊗_{P'} S'`, and these two maps commute with the
differentials of `NL(α)` and `NL(α')`: a map of two term complexes `NL(α) → NL(α')`.

For the canonical presentations `R[S] → S` and `R'[S'] → S'` the square itself produces a
morphism of presentations, namely `[s] ↦ [φ(s)]`, so the square produces *canonical* maps
`NL_{S/R} → NL_{S'/R'}` and `NL_{S/R} ⊗_S S' → NL_{S'/R'}`. The one assertion of the source's
display is that this construction is a functor rather than merely a map: stacking two squares,
```
S --φ--> S' --φ'--> S''
↑        ↑          ↑
R -----> R' ------> R''
```
the composite `NL_{S/R} → NL_{S'/R'} → NL_{S''/R''}` is the canonical map of the outer square.
That is what is stated here, and it is stated one level up, as an equality of morphisms of
presentations, from which the equality of the induced maps of complexes follows.

## Main results

* `Algebra.Generators.defaultHom_comp_defaultHom`: the canonical comparison morphism of
  presentations through the canonical presentation of an intermediate algebra is the canonical
  comparison morphism of the outer square. In particular the canonical maps
  `NL_{S/R} → NL_{S'/R'} → NL_{S''/R''}` compose to the canonical map `NL_{S/R} → NL_{S''/R''}`.

## Implementation notes

The square is the instance data `[Algebra R S]`, `[Algebra S S']`, `[Algebra R' S']` and, for the
second square, `[Algebra S' S'']`, `[Algebra R'' S'']`, `[Algebra R' R'']`; its commutativity is
carried by `IsScalarTower` instances, and the equality of the two composites `S → S''` — the
commutativity of the outer rectangle along the top and bottom rows — is `IsScalarTower S S' S''`,
the hypothesis that makes the conclusion true. The commutativity of the *left* square is not
needed and is therefore not assumed: this is weaker than the source's hypotheses, not stronger.

A presentation is `Algebra.Generators`: a family `val : ι → S` of values of the variables
together with a set theoretic section `σ` of the resulting surjection `R[ι] → S`. A morphism of
presentations is `Algebra.Generators.Hom`, recorded by the images `val : ι → P'.Ring` of the
variables; `Algebra.Generators.Hom.toAlgHom` is the map `φ̃ : P → P'`. The complex `NL(α)` is the
pair `Algebra.Extension.Cotangent` (the term `I/I²`, in degree one) and
`Algebra.Extension.CotangentSpace` (the term `Ω_{P/R} ⊗_P S`, in degree zero) together with
`Algebra.Extension.cotangentComplex`, and the induced maps are `Algebra.Extension.Cotangent.map`
and `Algebra.Extension.CotangentSpace.map` of `Algebra.Generators.Hom.toExtensionHom`; that they
commute with the differentials — the first half of the source's construction — is already
`Algebra.Extension.CotangentSpace.map_comp_cotangentComplex`.

The canonical presentation `R[S] → S` is `Algebra.Generators.self R S`, whose variables are
indexed by `S` and whose section is `MvPolynomial.X`. Consequently the source's canonical
morphism `[s] ↦ [φ(s)]` is `Algebra.Generators.defaultHom (self R S) (self R' S')`, pinned by
`(defaultHom (self R S) (self R' S')).val s = MvPolynomial.X (algebraMap S S' s)`, which is
`rfl`; the statement is about that map and not about some unspecified morphism.

Two departures from the source's form. First, generality: only the *intermediate* presentation
has to be the canonical one — what the proof uses is that its section is `MvPolynomial.X`, a
section defined at the level of variables — so the two outer presentations are arbitrary
families `P` and `P''`, and the source's claim is the case `P = self R S`, `P'' = self R'' S''`.
Second, level: the conclusion is an equality of morphisms of presentations rather than of maps of
complexes. It is the stronger statement, and the source's form follows from it in one rewrite,
by `Algebra.Generators.Hom.toExtensionHom_comp` together with
`Algebra.Extension.Cotangent.map_comp` in degree one, `Algebra.Extension.CotangentSpace.map_comp`
in degree zero, and `Algebra.Extension.H1Cotangent.map_comp` on `H¹`; it is also the form the
canonical map on `H¹(L_{S/R})`, `Algebra.H1Cotangent.map`, is defined in terms of.

Faithfulness. (1) No hypothesis is inert: `P`, `P''` and the intermediate algebra `S'` all occur
in the conclusion, and `IsScalarTower S S' S''` is what identifies the two sides — for a `S → S''`
different from `φ' ∘ φ` the equality is false, the remaining instances being those needed to form
the composite. (2) The scalars and bases are the source's: the inner morphism is a comparison of
a presentation of `S` over `R` with one of `S'` over `R'`, the outer one of `S` over `R` with one
of `S''` over `R''`; nothing is base changed, and no map is asked to be linear over a ring other
than the one the source uses. (3) The canonical map the source names is pinned, not merely
asserted to exist: the maps in the statement are the default comparison morphisms, which for the
canonical presentations are the source's `[s] ↦ [φ(s)]` by `rfl`, and the content is precisely
the characterising equation for their composite. (4) The instantiation is not degenerate: take
`R = ℤ`, `S = ℤ[x]`, `R' = R'' = ℤ[y]`, `S' = ℤ[x, y]`, `S'' = ℤ[x, y]/(x²)`, with `P = self R S`
and `P'' = self R'' S''`; no map in sight is an isomorphism, `S → S''` is not injective, and both
sides are maps of polynomial rings on infinitely many variables which agree on no smaller ground.

## References

* [StacksProject 06RQ](https://stacks.math.columbia.edu/tag/06RQ)
* [StacksProject 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

namespace Algebra.Generators

variable {R S R' S' R'' S'' ι ι'' : Type*}
  [CommRing R] [CommRing S] [Algebra R S]
  [CommRing R'] [CommRing S'] [Algebra R' S']
  [CommRing R''] [CommRing S''] [Algebra R'' S'']
  [Algebra R' R''] [Algebra R' S''] [Algebra S S'] [Algebra S' S''] [Algebra S S'']
  [IsScalarTower R' R'' S''] [IsScalarTower R' S' S''] [IsScalarTower S S' S'']

/-- **Functoriality of the naive cotangent complex in a square of rings** (Stacks 06RQ): given
two commutative squares of rings side by side,
```
S --φ--> S' --φ'--> S''
↑        ↑          ↑
R -----> R' ------> R''
```
a presentation `P` of `S` over `R`, a presentation `P''` of `S''` over `R''`, and the canonical
presentation `R'[S'] → S'` of the intermediate algebra, the composite of the canonical
comparison morphisms of presentations `P → R'[S']` and `R'[S'] → P''` is the canonical
comparison morphism `P → P''` of the outer square. Hence the canonical maps of naive cotangent
complexes `NL_{S/R} → NL_{S'/R'} → NL_{S''/R''}` compose to the canonical map
`NL_{S/R} → NL_{S''/R''}`. -/
@[stacks 06RQ "The display is the datum for functoriality of `NL`; what is stated is the
compatibility with composition of the canonical maps it produces, at the level of morphisms of
presentations. See the module docstring."]
public theorem defaultHom_comp_defaultHom (P : Generators R S ι) (P'' : Generators R'' S'' ι'') :
    (defaultHom (self R' S') P'').comp (defaultHom P (self R' S')) = defaultHom P P'' :=
    by apply Stacks.NaiveCotangent.Functoriality.solution

end Algebra.Generators

end
