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
# The surjectivity locus of a map of modules with finite cokernel

Let `R` be a ring and let `φ : M →ₗ[R] N` be a map of `R`-modules whose cokernel
`Coker(φ) = N ⧸ φ(M)` is a finite `R`-module. The set of primes `p` at which the localized map
`φ_p : M_p → N_p` is surjective is the set of primes at which the fibre map
`φ ⊗ κ(p) : M ⊗ κ(p) → N ⊗ κ(p)` is surjective: both conditions are the vanishing of a base change
of `Coker(φ)`, and Nakayama's lemma over the local ring `R_p` identifies the two.

## Main results

* `LinearMap.setOf_localizedMap_atPrime_surjective_eq_setOf_baseChange_surjective` and
  `Stacks.Modules.SurjectivityLocus.solution`: the locus where `φ_p` is surjective is the locus
  where `φ ⊗ κ(p)` is surjective.

## References

* [StacksProject 05GE](https://stacks.math.columbia.edu/tag/05GE)

## Tags

surjective locus, residue field, Nakayama's lemma, support, localization
-/

@[expose] public section

@[expose] public section

namespace Stacks.Modules.SurjectivityLocus

open TensorProduct

/-- In an exact sequence `M → N → P` whose second map is surjective, the first map is surjective
exactly when `P` vanishes. -/
private theorem Function.Exact.surjective_iff_subsingleton {M N P : Type*} [Zero P]
    {f : M → N} {g : N → P} (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Surjective f ↔ Subsingleton P := by
  refine ⟨fun hf ↦ subsingleton_of_forall_eq 0 fun p ↦ ?_,
    fun _ n ↦ (h n).mp (Subsingleton.elim _ _)⟩
  obtain ⟨n, rfl⟩ := hg p
  exact (h n).mpr (hf n)

/-- Base change of `φ : M →ₗ[R] N` along `R → A` is surjective exactly when the base change of
its cokernel vanishes. -/
private theorem LinearMap.baseChange_surjective_iff_subsingleton_tensorProduct_coker
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Type*) [Ring A] [Algebra R A] (φ : M →ₗ[R] N) :
    Function.Surjective (φ.baseChange A) ↔ Subsingleton (A ⊗[R] (N ⧸ LinearMap.range φ)) :=
  Function.Exact.surjective_iff_subsingleton
    (lTensor_exact A (LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)) (Submodule.mkQ_surjective _))
    (LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _))

/-- A finite module misses the prime `p` from its support exactly when its fibre at `p`
vanishes. -/
@[ega "0 1.7.5" "Nakayama step", sga "3 V 4.1.3" "more general"]
private theorem Module.notMem_support_iff_subsingleton_residueField_tensorProduct
    {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    {p : PrimeSpectrum R} :
    p ∉ Module.support R Q ↔ Subsingleton (p.asIdeal.ResidueField ⊗[R] Q) :=
  (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).not.trans
    not_nontrivial_iff_subsingleton

/-- For a map `φ` of `R`-modules with finite cokernel, the set of primes at which the localization
of `φ` is surjective is the set of primes at which the fibre map of `φ` is surjective. -/
public theorem solution {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) [Module.Finite R (N ⧸ φ.range)] :
    {p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} =
      {p | Function.Surjective (φ.baseChange p.asIdeal.ResidueField)} := by
  ext p
  simp only [Set.mem_ofPred_eq,
    _root_.LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker,
    LinearMap.baseChange_surjective_iff_subsingleton_tensorProduct_coker,
    ← _root_.Module.notMem_support_iff,
    Module.notMem_support_iff_subsingleton_residueField_tensorProduct]

end Stacks.Modules.SurjectivityLocus

end

@[expose] public section

/-- Let `R` be a ring and let `φ : M →ₗ[R] N` be a map of `R`-modules whose cokernel `N ⧸ φ.range`
is a finite `R`-module. Then the set of primes `p` of `R` such that the localized map
`φ_p : M_p → N_p` is surjective is the set of primes `p` such that the fibre map
`φ ⊗ κ(p) : M ⊗_R κ(p) → N ⊗_R κ(p)` is surjective. -/
@[stacks 05GE "the equality of the two loci in the displayed formula"]
public theorem LinearMap.setOf_localizedMap_atPrime_surjective_eq_setOf_baseChange_surjective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) [Module.Finite R (N ⧸ φ.range)] :
    {p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} =
      {p | Function.Surjective (φ.baseChange p.asIdeal.ResidueField)} :=
  Stacks.Modules.SurjectivityLocus.solution φ

end
