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
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization

/-!
# Irreducibility of `Spec` from irreducible fibres
-/

/-!
# Spec of a flat finitely presented algebra is irreducible from irreducible
fibres on a dense subset (Tag 00I6)

Let `R → S` be a ring map with `Spec R` irreducible. If the structure map
`Spec S → Spec R` is open (e.g. if `R → S` is flat and of finite presentation)
and the topological fibres of `Spec S → Spec R` are irreducible over a dense
subset of `Spec R`, then `Spec S` is irreducible.

The headline `irreducibleSpace_of_isOpenMap_dense_irreducible_fibres` is the
purely topological version of the Stacks lemma, formulated directly in terms of
fibres of the structure map (this is the *more general* form noted in the
Stacks statement, with `(b) + (c)` replaced by openness of the map on spectra).
The flat + finite presentation specialization follows by combining it with
`primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation`.
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `Y` is irreducible and `f : X → Y` is an open map whose topological
fibres `{x // f x = y}` are irreducible for `y` in a dense subset `D ⊆ Y`,
then `X` is nonempty. -/
private lemma nonempty_of_dense_irreducible_fibres
    [IrreducibleSpace Y] (f : X → Y) (D : Set Y) (hD : Dense D)
    (hfib : ∀ y ∈ D, IrreducibleSpace {x : X // f x = y}) :
    Nonempty X :=
  let ⟨y, hy⟩ := hD.nonempty
  ⟨(hfib y hy).toNonempty.some.1⟩

/-- If `Y` is irreducible and `f : X → Y` is a continuous open map whose
topological fibres are irreducible for `y` in a dense subset, then `X` is
preirreducible. -/
private lemma preirreducibleSpace_of_isOpenMap_dense_irreducible_fibres
    [IrreducibleSpace Y]
    (f : X → Y) (hf : IsOpenMap f)
    (D : Set Y) (hD : Dense D)
    (hfib : ∀ y ∈ D, IrreducibleSpace {x : X // f x = y}) :
    PreirreducibleSpace X := by
  refine ⟨fun U V hU hV ⟨xU, _, hxU⟩ ⟨xV, _, hxV⟩ => ?_⟩
  obtain ⟨y, _, hyU, hyV⟩ := (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible _ _
    (hf U hU) (hf V hV) ⟨f xU, trivial, xU, hxU, rfl⟩ ⟨f xV, trivial, xV, hxV, rfl⟩
  obtain ⟨y₀, ⟨⟨xU, hxU, hfxU⟩, ⟨xV, hxV, hfxV⟩⟩, hy₀D⟩ :=
    hD.inter_open_nonempty _ ((hf U hU).inter (hf V hV)) ⟨y, hyU, hyV⟩
  have := hfib y₀ hy₀D
  obtain ⟨⟨x₀, _⟩, _, hx₀U, hx₀V⟩ :=
    (IrreducibleSpace.isIrreducible_univ {x : X // f x = y₀}).isPreirreducible _ _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      ⟨⟨xU, hfxU⟩, trivial, hxU⟩ ⟨⟨xV, hfxV⟩, trivial, hxV⟩
  exact ⟨x₀, trivial, hx₀U, hx₀V⟩

/-- **Topological core of Stacks 00I6.** Let `f : X → Y` be a continuous open
map between topological spaces with `Y` irreducible. If the fibres
`{x // f x = y}` of `f` are irreducible spaces for `y` in a dense subset of
`Y`, then `X` is irreducible.

This is the *more general* form of Stacks tag 00I6 (Algebra, Lemma 10.130.4)
indicated in the statement, with the flatness and finite-presentation
hypotheses replaced by openness of the structure map on spectra. -/
@[ega "IV 2.3.5" "(iii), special case", ega "IV 4.4.2" "irreducibility clause"]
theorem irreducibleSpace_of_isOpenMap_dense_irreducible_fibres
    [IrreducibleSpace Y]
    (f : X → Y) (hf : IsOpenMap f)
    (D : Set Y) (hD : Dense D)
    (hfib : ∀ y ∈ D, IrreducibleSpace {x : X // f x = y}) :
    IrreducibleSpace X :=
  have : Nonempty X := nonempty_of_dense_irreducible_fibres f D hD hfib
  have : PreirreducibleSpace X :=
    preirreducibleSpace_of_isOpenMap_dense_irreducible_fibres f hf D hD hfib
  ⟨inferInstance⟩

/-- **Stacks 00I6** (algebraic form, more general statement). Let `R → S` be a
ring map. Assume:
* `Spec R` is irreducible;
* the induced map `Spec S → Spec R` is open;
* the topological fibres of `Spec S → Spec R` are irreducible for `p` in a
  dense subset of `Spec R`.

Then `Spec S` is irreducible. -/
@[stacks 00I6 "general form", ega "IV 2.3.5" "(iii), special case", ega "IV 4.4.2" "special case"]
theorem irreducibleSpace_primeSpectrum_of_isOpenMap_comap
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IrreducibleSpace (PrimeSpectrum R)]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R S)))
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hfib : ∀ p ∈ D,
      IrreducibleSpace
        {q : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) q = p}) :
    IrreducibleSpace (PrimeSpectrum S) :=
  irreducibleSpace_of_isOpenMap_dense_irreducible_fibres
    (PrimeSpectrum.comap (algebraMap R S)) hopen
    D hD hfib

/-- **Stacks 00I6** (flat + finite-presentation form). Let `R → S` be a flat
ring map of finite presentation. If `Spec R` is irreducible and the
topological fibres of `Spec S → Spec R` are irreducible for `p` in a dense
subset of `Spec R`, then `Spec S` is irreducible. -/
@[stacks 00I6]
theorem irreducibleSpace_primeSpectrum_of_flat_finitePresentation
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IrreducibleSpace (PrimeSpectrum R)]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hfib : ∀ p ∈ D,
      IrreducibleSpace
        {q : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) q = p}) :
    IrreducibleSpace (PrimeSpectrum S) :=
  irreducibleSpace_primeSpectrum_of_isOpenMap_comap R S
    (primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation R S)
    D hD hfib

end

/-!
# Tensor with the base field preserves the unique minimal prime (Tag 00I7)

Stacks lemma 00I7 says: if `k` is a separably closed field and `R`, `S` are
`k`-algebras each with a unique minimal prime, then so does `R ⊗_k S`. The
general proof is deep — it reduces to the algebraically closed case via the
algebraic closure, then to the case of two domains, and finally uses the
Nullstellensatz together with irreducibility of the fibres of a flat finite-type
map.

This file formalizes the trivial special case in which one of the two factors
is `k` itself. The `k`-algebra isomorphism `Algebra.TensorProduct.rid` then
identifies `R ⊗_k k` with `R`, and we transport the unique minimal prime along
this ring isomorphism. The same argument handles `k ⊗_k S` via
`Algebra.TensorProduct.lid`.

The key reusable ingredient is `unique_minimalPrime_of_ringEquiv`: any ring
isomorphism transports the property of having a unique minimal prime.
-/

@[expose] public section

open scoped TensorProduct

/-- A ring isomorphism transports the property of having a unique minimal prime. -/
theorem unique_minimalPrime_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : ∃! p, p ∈ minimalPrimes S) : ∃! p, p ∈ minimalPrimes R := by
  have hcomap : minimalPrimes R =
      Ideal.comap (e : R →+* S) '' minimalPrimes S := by
    have := Ideal.comap_minimalPrimes_eq_of_surjective
      (f := (e : R →+* S)) e.surjective (I := (⊥ : Ideal S))
    have hbot : (⊥ : Ideal S).comap (e : R →+* S) = ⊥ :=
      Ideal.comap_bot_of_injective _ e.injective
    simpa [minimalPrimes, hbot] using this
  obtain ⟨q, hq, huniq⟩ := h
  refine ⟨Ideal.comap (e : R →+* S) q, ?_, ?_⟩
  · rw [hcomap]; exact ⟨q, hq, rfl⟩
  · intro p hp
    rw [hcomap] at hp
    obtain ⟨q', hq', rfl⟩ := hp
    rw [huniq q' hq']

/-- The right-factor trivial case of Stacks 00I7: if the right factor is the
base field `k` itself, then `R ⊗[k] k` has a unique minimal prime whenever
`R` does. -/
theorem tensorProduct_rid_unique_minimalPrime (k : Type*) [Field k] (R : Type*) [CommRing R]
    [Algebra k R] (hR : ∃! p, p ∈ minimalPrimes R) : ∃! p, p ∈ minimalPrimes (R ⊗[k] k) :=
  unique_minimalPrime_of_ringEquiv (Algebra.TensorProduct.rid k k R).toRingEquiv hR

/-- The left-factor trivial case of Stacks 00I7: if the left factor is the
base field `k` itself, then `k ⊗[k] S` has a unique minimal prime whenever
`S` does. -/
theorem tensorProduct_lid_unique_minimalPrime (k : Type*) [Field k] (S : Type*) [CommRing S]
    [Algebra k S] (hS : ∃! p, p ∈ minimalPrimes S) : ∃! p, p ∈ minimalPrimes (k ⊗[k] S) :=
  unique_minimalPrime_of_ringEquiv (Algebra.TensorProduct.lid k S).toRingEquiv hS

/-- **Stacks Tag 00I7 (right-factor-is-the-base-field special case).**
Let `k` be a field and let `R` be a `k`-algebra with a unique minimal prime.
Then `R ⊗_k k` has a unique minimal prime.

The full Stacks lemma asserts the same conclusion for `R ⊗_k S` for any pair
of `k`-algebras `R`, `S` each with a unique minimal prime; that proof requires
the algebraic closure of `k`, generic-fibre irreducibility for the flat
finite-type map `R → R ⊗_k S` (Hilbert Nullstellensatz, Jacobson), and a limit
argument over finitely generated subalgebras.

Only the degenerate `S = k` case is formalized here, and it does not use
separable closedness of `k`: it is `Algebra.TensorProduct.rid` transported along
`unique_minimalPrime_of_ringEquiv`. Accordingly no `[IsSepClosed k]` hypothesis
is assumed, and the `@[stacks 00I7]` attribute is qualified -- **tag 00I7 is
still open** in the generality Stacks states. -/
@[stacks 00I7 "Only the degenerate S = k case; the general R ⊗_k S statement is not formalized."]
alias tensorProduct_unique_minimalPrime_of_isSepClosed_right_base :=
  tensorProduct_rid_unique_minimalPrime

end
