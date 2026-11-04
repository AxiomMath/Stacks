module

public import StacksFrontier.Algebra.Homology.Resolution.Existence
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

/-!
# The syzygies of a resolution

Let `P` be a `FreeResolutionData R M`, that is an augmented complex
`⋯ → F 2 →[d 1] F 1 →[d 0] F 0 →[ε] M → 0`.
Its *syzygies* are `K 0 = M` and `K (n+1) = ker(F n → K n)`, and they fit into short exact
sequences `0 → K (n+1) → F n → K n → 0`.

Writing `δ 0 = ε` and `δ (n+1) = d n` for the augmented differentials, so that
`δ n : F n → T n` with `T 0 = M` and `T (n+1) = F n`, one has `K (n+1) = ker (δ n)` for every
`n` on the nose: the map `F n → K n` is the corestriction of `δ n`, and its kernel is
`ker (δ n)`. So `K` is defined by a case split, not by a recursion, and neither are its module
structures.

## Main results

* `FreeResolutionData.syzygy`, with `FreeResolutionData.syzygyIncl` and
  `FreeResolutionData.syzygyProj`: the syzygies and the two maps of the short exact sequence.
* `FreeResolutionData.injective_syzygyIncl`, `FreeResolutionData.exact_syzygy`,
  `FreeResolutionData.surjective_syzygyProj`, bundled as
  `FreeResolutionData.shortExact_syzygy`: the sequences are short exact. Only exactness of the
  resolution is used, and only for surjectivity; injectivity and exactness in the middle hold
  for any augmented complex.
* `FreeResolutionData.finite_syzygy`: over a Noetherian ring, the syzygies of a resolution of a
  finite module by finite modules are finite, being submodules of the `F n`.

## Implementation notes

`syzygy 0` is `M` itself, not a module isomorphic to it, and
`FreeResolutionData.instModuleSyzygy 0` unfolds to the given module structure on `M`; so a
statement about `M` may be fed to a statement about `syzygy 0` directly.

## References

* [StacksProject 00LP](https://stacks.math.columbia.edu/tag/00LP)
* [StacksProject 00RC](https://stacks.math.columbia.edu/tag/00RC)

## Tags

resolution, syzygy, short exact sequence, dimension shifting
-/

@[expose] public section

universe u v

namespace FreeResolutionData

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (P : FreeResolutionData R M)

/-- The target of the `n`-th augmented differential: `M` for `n = 0` and `F (n-1)` after that. -/
protected def target : ℕ → Type v
  | 0 => M
  | (m + 1) => P.F m

/-- The additive group structure on `P.target n`, that of `M` or of `F (n-1)`. -/
@[instance_reducible] protected def instAddCommGroupTarget : ∀ n, AddCommGroup (P.target n)
  | 0 => inferInstanceAs (AddCommGroup M)
  | (m + 1) => inferInstanceAs (AddCommGroup (P.F m))

attribute [instance] FreeResolutionData.instAddCommGroupTarget

/-- The `R`-module structure on `P.target n`, that of `M` or of `F (n-1)`. -/
@[instance_reducible] protected def instModuleTarget : ∀ n, Module R (P.target n)
  | 0 => inferInstanceAs (Module R M)
  | (m + 1) => inferInstanceAs (Module R (P.F m))

attribute [instance] FreeResolutionData.instModuleTarget

/-- The augmented differentials of the resolution: the augmentation `ε : F 0 → M` at `n = 0` and
the differential `d (n-1) : F n → F (n-1)` after that. -/
protected def delta : ∀ n, P.F n →ₗ[R] P.target n
  | 0 => P.ε
  | (m + 1) => P.d m

/-- The `0`-th augmented differential is the augmentation `ε`. -/
@[simp] theorem delta_zero : P.delta 0 = P.ε := rfl

/-- The `(m+1)`-st augmented differential is the differential `d m`. -/
@[simp] theorem delta_succ (m : ℕ) : P.delta (m + 1) = P.d m := rfl

/-- Consecutive augmented differentials compose to zero. -/
theorem IsComplex.delta_comp_delta {P : FreeResolutionData R M} (h : P.IsComplex) (m : ℕ) :
    (P.delta m).comp (P.delta (m + 1)) = 0 := by
  cases m with
  | zero => exact h.1
  | succ k => exact h.2 k

/-- Exactness of the resolution, read along the augmented differentials. -/
theorem IsExact.range_delta_succ {P : FreeResolutionData R M} (h : P.IsExact) (m : ℕ) :
    LinearMap.range (P.delta (m + 1)) = LinearMap.ker (P.delta m) := by
  cases m with
  | zero => exact h.2.1
  | succ k => exact h.2.2 k

/-- An exact resolution is a complex. -/
theorem IsExact.isComplex {P : FreeResolutionData R M} (h : P.IsExact) : P.IsComplex :=
  have key := fun m => LinearMap.range_le_ker_iff.mp (h.range_delta_succ m).le
  ⟨key 0, fun n => key (n + 1)⟩

/-- The syzygies of the resolution: `syzygy 0` is `M` itself, and `syzygy (n+1)` is the kernel of
the `n`-th augmented differential, a submodule of `F n`. -/
protected def syzygy : ℕ → Type v
  | 0 => M
  | (m + 1) => LinearMap.ker (P.delta m)

/-- The additive group structure on `P.syzygy n`, that of `M` or of the submodule
`ker (δ (n-1))`. -/
@[instance_reducible] protected def instAddCommGroupSyzygy : ∀ n, AddCommGroup (P.syzygy n)
  | 0 => inferInstanceAs (AddCommGroup M)
  | (m + 1) => inferInstanceAs (AddCommGroup (LinearMap.ker (P.delta m)))

attribute [instance] FreeResolutionData.instAddCommGroupSyzygy

/-- The `R`-module structure on `P.syzygy n`, that of `M` or of the submodule `ker (δ (n-1))`. -/
@[instance_reducible] protected def instModuleSyzygy : ∀ n, Module R (P.syzygy n)
  | 0 => inferInstanceAs (Module R M)
  | (m + 1) => inferInstanceAs (Module R (LinearMap.ker (P.delta m)))

attribute [instance] FreeResolutionData.instModuleSyzygy

/-- The `0`-th syzygy is `M`. -/
theorem syzygy_zero : P.syzygy 0 = M := rfl

/-- The inclusion `K (n+1) → F n` of the `(n+1)`-st syzygy. -/
protected def syzygyIncl (n : ℕ) : P.syzygy (n + 1) →ₗ[R] P.F n :=
  (LinearMap.ker (P.delta n)).subtype

/-- The inclusion `K (n+1) → F n` is injective. -/
theorem injective_syzygyIncl (n : ℕ) : Function.Injective (P.syzygyIncl n) :=
  Subtype.val_injective

/-- The range of the inclusion `K (n+1) → F n` is the kernel of the `n`-th augmented
differential. -/
theorem range_syzygyIncl (n : ℕ) :
    LinearMap.range (P.syzygyIncl n) = LinearMap.ker (P.delta n) :=
  Submodule.range_subtype _

/-- The projection `F n → K n` onto the `n`-th syzygy: the augmentation at `n = 0`, and the
corestriction of the `n`-th augmented differential to its image after that. -/
protected def syzygyProj (hc : P.IsComplex) : ∀ n, P.F n →ₗ[R] P.syzygy n
  | 0 => P.ε
  | (m + 1) => (P.delta (m + 1)).codRestrict (LinearMap.ker (P.delta m)) fun x =>
      congrArg (fun f : P.F (m + 1) →ₗ[R] P.target m => f x) (hc.delta_comp_delta m)

/-- The kernel of the projection `F n → K n` is the kernel of the `n`-th augmented
differential. -/
theorem ker_syzygyProj (hc : P.IsComplex) (n : ℕ) :
    LinearMap.ker (P.syzygyProj hc n) = LinearMap.ker (P.delta n) := by
  cases n with
  | zero => rfl
  | succ m => exact LinearMap.ker_codRestrict _ _ _

/-- For an augmented complex, the sequence `K (n+1) → F n → K n` is exact. -/
theorem exact_syzygy (hc : P.IsComplex) (n : ℕ) :
    Function.Exact (P.syzygyIncl n) (P.syzygyProj hc n) :=
  LinearMap.exact_iff.mpr ((P.ker_syzygyProj hc n).trans (P.range_syzygyIncl n).symm)

/-- For an exact resolution, the projection `F n → K n` is surjective. -/
theorem surjective_syzygyProj (h : P.IsExact) (n : ℕ) :
    Function.Surjective (P.syzygyProj h.isComplex n) := by
  cases n with
  | zero => exact h.1
  | succ m =>
    intro y
    obtain ⟨x, hx⟩ := (h.range_delta_succ m).ge y.2
    exact ⟨x, Subtype.ext hx⟩

/-- **The short exact sequences of a resolution.** For an exact resolution
`⋯ → F 1 → F 0 → M → 0` the sequence `0 → K (n+1) → F n → K n → 0` is short exact, where
`K 0 = M` and `K (n+1) = ker (F n → K n)`. -/
theorem shortExact_syzygy (h : P.IsExact) (n : ℕ) :
    Function.Injective (P.syzygyIncl n) ∧
      Function.Exact (P.syzygyIncl n) (P.syzygyProj h.isComplex n) ∧
      Function.Surjective (P.syzygyProj h.isComplex n) :=
  ⟨P.injective_syzygyIncl n, P.exact_syzygy h.isComplex n, P.surjective_syzygyProj h n⟩

/-- Over a Noetherian ring, the syzygies of a resolution of a finite module by finite modules are
finite. -/
theorem finite_syzygy [IsNoetherianRing R] [Module.Finite R M] (hfin : P.IsFinite) (n : ℕ) :
    Module.Finite R (P.syzygy n) := by
  cases n with
  | zero => exact inferInstanceAs (Module.Finite R M)
  | succ m =>
    have : Module.Finite R (P.F m) := hfin m
    have : IsNoetherian R (P.F m) := isNoetherian_of_isNoetherianRing_of_finite R (P.F m)
    exact inferInstanceAs (Module.Finite R (LinearMap.ker (P.delta m)))

end FreeResolutionData

end
