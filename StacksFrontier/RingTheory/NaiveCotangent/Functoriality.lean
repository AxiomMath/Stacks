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

* `Stacks.NaiveCotangent.Functoriality.solution`: the compatibility with composition asserted in
  the paragraph of Stacks 06RQ, namely `Algebra.Generators.defaultHom_comp_defaultHom`. The
  full statement of the paragraph is `Algebra.Generators.naiveCotangentComplex_functorial`.

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
That is what is stated in this section (the other parts of the paragraph are in
`Algebra.Generators.naiveCotangentComplex_functorial` below), and it is stated one level up,
as an equality of morphisms of presentations, from which the equality of the induced maps of
complexes follows.

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

/-- **Compatibility of the canonical maps of `NL` with composition** (part of the paragraph of
Stacks 06RQ, whose full statement is `Algebra.Generators.naiveCotangentComplex_functorial`): given
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
public theorem defaultHom_comp_defaultHom (P : Generators R S ι) (P'' : Generators R'' S'' ι'') :
    (defaultHom (self R' S') P'').comp (defaultHom P (self R' S')) = defaultHom P P'' :=
    by apply Stacks.NaiveCotangent.Functoriality.solution

end Algebra.Generators

end

/-!
# The commutative square of rings and the functoriality of `NL`

The display of Stacks 06RQ is a commutative square of rings
```
S --φ--> S'
↑        ↑
R -----> R'
```
which is recorded here as `Stacks.NaiveCotangent.RingSquare`. The paragraph it heads asserts
the functoriality of the naive cotangent complex in such a square, and that is
`Algebra.Generators.naiveCotangentComplex_functorial`. In it the square is the instance data
`[Algebra R S]`, `[Algebra R' S']`, `[Algebra R R']`, `[Algebra S S']`, `[Algebra R S']` together
with `IsScalarTower R S S'` and `IsScalarTower R R' S'`, which say that both composites
`R → S'` are `algebraMap R S'`. This is the same datum as a `RingSquare`:
`Stacks.NaiveCotangent.RingSquare.ofIsScalarTower` turns the instance data into a square, and
`Stacks.NaiveCotangent.RingSquare.isScalarTower` shows that every square, with its four maps as
algebra structures, satisfies the two scalar tower conditions.

The parts of the paragraph, with the Mathlib declarations used for them, are:
* a morphism of presentations `φ̃ : P → P'` (`Algebra.Generators.Hom`, with
  `Algebra.Generators.Hom.toAlgHom`) maps `I = ker α` into `I' = ker α'`;
* the induced maps `I/I² → I'/(I')²` (`Algebra.Extension.Cotangent.map`) and
  `Ω_{P/R} ⊗_P S → Ω_{P'/R'} ⊗_{P'} S'` (`Algebra.Extension.CotangentSpace.map`) commute with the
  differentials (`Algebra.Extension.CotangentSpace.map_comp_cotangentComplex`), so they form a map
  of complexes `NL(α) → NL(α')`;
* the induced maps `S' ⊗_S I/I² → I'/(I')²` and `S' ⊗_S (Ω_{P/R} ⊗_P S) → Ω_{P'/R'} ⊗_{P'} S'`
  (`LinearMap.liftBaseChange`) commute with the differentials of `NL(α) ⊗_S S'` and `NL(α')`, a
  map of complexes `NL(α) ⊗_S S' → NL(α')`;
* for the canonical presentations `R[S] → S` and `R'[S'] → S'`
  (`Algebra.Generators.self`) the canonical morphism is `[s] ↦ [φ(s)]`, namely
  `Algebra.Generators.defaultHom (self R S) (self R' S')`;
* the construction is compatible with composition of squares
  (`Algebra.Generators.defaultHom_comp_defaultHom`).

## References

* [StacksProject 06RQ](https://stacks.math.columbia.edu/tag/06RQ)
-/

@[expose] public section

namespace Stacks.NaiveCotangent

/-- **A commutative square of rings** (Stacks 06RQ): ring maps `R → S`, `R → R'`, `R' → S'` and
`φ : S → S'` such that the two composites `R → S'` agree. It is the datum for which the naive
cotangent complex is functorial, see `Algebra.Generators.naiveCotangentComplex_functorial`. -/
@[stacks 06RQ "The commutative square of rings; the functoriality of the naive cotangent complex
in it is `Algebra.Generators.naiveCotangentComplex_functorial`."]
structure RingSquare (R S R' S' : Type*) [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    where
  /-- The left vertical map `R → S`. -/
  left : R →+* S
  /-- The bottom horizontal map `R → R'`. -/
  bottom : R →+* R'
  /-- The right vertical map `R' → S'`. -/
  right : R' →+* S'
  /-- The top horizontal map `φ : S → S'`. -/
  top : S →+* S'
  /-- The square commutes. -/
  comm : top.comp left = right.comp bottom

namespace RingSquare

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- The commutative square given by algebra structures `R → S`, `R → R'`, `R' → S'`, `S → S'`
and `R → S'` with `IsScalarTower R S S'` and `IsScalarTower R R' S'`. -/
@[simps]
def ofIsScalarTower [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S'] : RingSquare R S R' S' where
  left := algebraMap R S
  bottom := algebraMap R R'
  right := algebraMap R' S'
  top := algebraMap S S'
  comm := by rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- Every commutative square of rings is of the form `ofIsScalarTower`: with its four maps as
algebra structures and `R → S'` the composite, both scalar tower conditions hold. -/
theorem isScalarTower (sq : RingSquare R S R' S') :
    letI := sq.left.toAlgebra
    letI := sq.bottom.toAlgebra
    letI := sq.right.toAlgebra
    letI := sq.top.toAlgebra
    letI : Algebra R S' := (sq.top.comp sq.left).toAlgebra
    IsScalarTower R S S' ∧ IsScalarTower R R' S' :=
  letI := sq.left.toAlgebra
  letI := sq.bottom.toAlgebra
  letI := sq.right.toAlgebra
  letI := sq.top.toAlgebra
  letI : Algebra R S' := (sq.top.comp sq.left).toAlgebra
  ⟨IsScalarTower.of_algebraMap_eq' rfl, IsScalarTower.of_algebraMap_eq' sq.comm⟩

end RingSquare

end Stacks.NaiveCotangent

namespace Algebra.Generators

variable {R S R' S' ι ι' : Type*}
  [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [CommRing S'] [Algebra R' S']
  [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

/-- **Functoriality of the naive cotangent complex in a commutative square of rings**
(Stacks 06RQ). Let `R → S`, `R' → S'`, `R → R'`, `φ : S → S'` be a commutative square of rings
(as algebra structures with `IsScalarTower R S S'` and `IsScalarTower R R' S'`, see
`Stacks.NaiveCotangent.RingSquare`), and let `α : P → S`, `α' : P' → S'` be presentations of `S`
over `R` and of `S'` over `R'`. Then for every morphism of presentations `f : P → P'`:
1. `f` maps `I = ker α` into `I' = ker α'`;
2. the induced maps `I/I² → I'/(I')²` and `Ω_{P/R} ⊗_P S → Ω_{P'/R'} ⊗_{P'} S'` commute with the
   differentials, so they form a map of complexes `NL(α) → NL(α')`;
3. the induced maps on `NL(α) ⊗_S S'` commute with the differentials, so they form a map of
   complexes `NL(α) ⊗_S S' → NL(α')`.
Moreover:
4. for the canonical presentations `R[S] → S` and `R'[S'] → S'`, the canonical morphism
   `defaultHom (self R S) (self R' S')` is the ring map `[s] ↦ [φ(s)]`;
5. the construction is compatible with composition: for a second square
   `R' → R''`, `S' → S''`, the composite of the canonical morphisms `R[S] → R'[S'] → R''[S'']` is
   the canonical morphism `R[S] → R''[S'']` of the outer square, hence the canonical maps
   `NL_{S/R} → NL_{S'/R'} → NL_{S''/R''}` compose to the map of the outer square. -/
@[stacks 06RQ "The functoriality of the naive cotangent complex in the square: kernels, the
maps of complexes `NL(α) → NL(α')` and `NL(α) ⊗_S S' → NL(α')`, the canonical map of the
canonical presentations, and its compatibility with composition."]
theorem naiveCotangentComplex_functorial (P : Generators R S ι) (P' : Generators R' S' ι') :
    (∀ f : P.Hom P', P.ker.map f.toAlgHom ≤ P'.ker) ∧
    (∀ f : P.Hom P',
      Extension.CotangentSpace.map f.toExtensionHom ∘ₗ P.toExtension.cotangentComplex =
        P'.toExtension.cotangentComplex.restrictScalars S ∘ₗ
          Extension.Cotangent.map f.toExtensionHom) ∧
    (∀ f : P.Hom P',
      P'.toExtension.cotangentComplex ∘ₗ
          (Extension.Cotangent.map f.toExtensionHom).liftBaseChange S' =
        (Extension.CotangentSpace.map f.toExtensionHom).liftBaseChange S' ∘ₗ
          P.toExtension.cotangentComplex.baseChange S') ∧
    (∀ s : S, (defaultHom (self R S) (self R' S')).toAlgHom (.X s) = .X (algebraMap S S' s)) ∧
    (∀ (R'' S'' : Type _) [CommRing R''] [CommRing S''] [Algebra R'' S''] [Algebra R' R'']
      [Algebra R' S''] [Algebra S' S''] [Algebra S S''] [IsScalarTower R' R'' S'']
      [IsScalarTower R' S' S''] [IsScalarTower S S' S''],
      (defaultHom (self R' S') (self R'' S'')).comp (defaultHom (self R S) (self R' S')) =
        defaultHom (self R S) (self R'' S'')) := by
  refine ⟨fun f ↦ ?_, fun f ↦ Extension.CotangentSpace.map_comp_cotangentComplex _, fun f ↦ ?_,
    fun s ↦ by simp, fun R'' S'' _ _ _ _ _ _ _ _ _ _ ↦ defaultHom_comp_defaultHom _ _⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [ker_eq_ker_aeval_val, RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, ker_eq_ker_aeval_val, RingHom.mem_ker]
    simp [hx]
  · apply LinearMap.restrictScalars_injective S
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext s x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
    congr 1
    exact (Extension.CotangentSpace.map_cotangentComplex _ x).symm

end Algebra.Generators

end
