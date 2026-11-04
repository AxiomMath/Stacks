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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducedness ascends along a flat ring map with reduced fibres

If `φ : R → S` is a flat map of Noetherian rings, `R` is reduced and every fibre ring
`κ(𝔭) ⊗_R S` is reduced, then `S` is reduced.

## Main results

* `Stacks.Flatness.ReducedFibreAscent.isReduced_left_of_tensor`: for `A` flat over `R` and
  `R → T` injective, if `A ⊗[R] T` is reduced then `A` is reduced.
* `Stacks.Flatness.ReducedFibreAscent.isReduced_of_flat_of_forall_isReduced_fiber`: a flat
  `R`-algebra whose fibre rings at a finite family of primes of `R` with zero intersection are
  reduced is reduced.
* `isReduced_of_flat_of_isReduced_fiber`: a flat ring map of Noetherian rings with reduced source
  and reduced fibre rings has reduced target.

## References

* [StacksProject 0C21](https://stacks.math.columbia.edu/tag/0C21)

## Tags

reduced ring, flat ring map, fibre ring, ascent, minimal prime, Noetherian ring
-/

@[expose] public section

universe u v w

@[expose] public section

namespace Stacks.Flatness.ReducedFibreAscent

open scoped TensorProduct

/-- If `R → T` is injective and `A` is a flat `R`-algebra with `A ⊗[R] T` reduced, then `A` is
reduced. -/
public theorem isReduced_left_of_tensor {R A T : Type*} [CommSemiring R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra R T] [Module.Flat R A]
    (h : Function.Injective (algebraMap R T)) [IsReduced (A ⊗[R] T)] : IsReduced A :=
  isReduced_of_injective (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := T))
    (Algebra.TensorProduct.includeLeft_injective h)

/-- For a finite family of `R`-algebras `B i`, if every `A ⊗[R] B i` is reduced, then
`A ⊗[R] (∀ i, B i)` is reduced. -/
public theorem isReduced_tensorProduct_pi {R A : Type*} {ι : Type*} (B : ι → Type*)
    [CommSemiring R] [CommRing A] [Algebra R A] [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [Finite ι] [∀ i, IsReduced (A ⊗[R] B i)] : IsReduced (A ⊗[R] (∀ i, B i)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  exact isReduced_of_injective (Algebra.TensorProduct.piRight R R A B) (AlgEquiv.injective _)

/-- Let `S` be a flat `R`-algebra and `p : ι → Ideal R` a finite family of primes of `R` whose
intersection is zero. If every fibre ring `κ(p i) ⊗_R S` is reduced, then `S` is reduced. -/
public theorem isReduced_of_flat_of_forall_isReduced_fiber {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] {ι : Type w} [Finite ι] (p : ι → Ideal R)
    [hp : ∀ i, (p i).IsPrime] (hzero : ∀ r : R, (∀ i, r ∈ p i) → r = 0)
    (hred : ∀ i, IsReduced ((p i).Fiber S)) : IsReduced S := by
  have hinj : Function.Injective (algebraMap R (∀ i, (p i).ResidueField)) :=
    (injective_iff_map_eq_zero _).mpr fun r hr => hzero r fun i =>
      Ideal.algebraMap_residueField_eq_zero.mp (congrFun hr i)
  have : ∀ i, IsReduced (S ⊗[R] (p i).ResidueField) := fun i => by
    have := hred i
    exact isReduced_of_injective (Algebra.TensorProduct.comm R S (p i).ResidueField)
      (AlgEquiv.injective _)
  have := isReduced_tensorProduct_pi (R := R) (A := S) fun i => (p i).ResidueField
  exact isReduced_left_of_tensor hinj

/-- In a reduced commutative ring, an element lying in every minimal prime is zero. -/
public theorem eq_zero_of_forall_mem_minimalPrimes {R : Type*} [CommRing R] [IsReduced R] {r : R}
    (hr : ∀ q ∈ minimalPrimes R, r ∈ q) : r = 0 := by
  have hmem : r ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.2 hr
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes from rfl, Ideal.sInf_minimalPrimes,
    Ideal.radical_bot_of_isReduced] at hmem
  simpa using hmem

/-- Let `R → S` be a flat ring map of Noetherian rings. If `R` is reduced and every fibre ring
`κ(𝔭) ⊗_R S` is reduced, then `S` is reduced. -/
public theorem solution {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [IsReduced R] (hfibre : ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S)) :
    IsReduced S := by
  have : Finite {q : Ideal R // q ∈ minimalPrimes R} :=
    (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  exact isReduced_of_flat_of_forall_isReduced_fiber (S := S)
    (ι := {q : Ideal R // q ∈ minimalPrimes R}) Subtype.val
    (hp := fun i => Ideal.IsMinimalPrime.isPrime i.2)
    (fun r hr => eq_zero_of_forall_mem_minimalPrimes fun q hq => hr ⟨q, hq⟩)
    (fun i => @hfibre i.1 (Ideal.IsMinimalPrime.isPrime i.2))

end Stacks.Flatness.ReducedFibreAscent

end

@[expose] public section

/-- Let `R → S` be a flat ring map of Noetherian rings. If `R` is reduced and every fibre ring
`κ(𝔭) ⊗_R S` is reduced, then `S` is reduced. -/
@[stacks 0C21 "The ring map is an `Algebra R S` instance with `Module.Flat R S`, and the fibre \
  ring `S ⊗_R κ(𝔭)` is Mathlib's `Ideal.Fiber 𝔭 S`, as in the statements of Tags 0339 and 033A. \
  Reducedness is Mathlib's `IsReduced`, and the fibre hypothesis is reducedness, not geometric \
  reducedness, so this is not an affine instance of Mathlib's \
  `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`. \
  See the module docstring.",
  ega "IV 3.3.5" "affine case",
  ega "IV 11.3.13" "(ii) reduced, Noetherian"]
public theorem isReduced_of_flat_of_isReduced_fiber {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [IsReduced R] (hfibre : ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S)) :
    IsReduced S :=
  Stacks.Flatness.ReducedFibreAscent.solution (R := R) hfibre

end
