module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksCore.Tactic.StacksAttribute

/-! # Obstructing finite Tor dimension

"`S` has finite Tor dimension over `R`" is used in Stacks Tags 09PU and 09PV in the unquantified
form `∃ b, ∀ N i, b < i → Tor i (S, N) = 0`. To contradict it one needs a *single* module `M`
against which `Tor` fails to vanish in arbitrarily high degree, and the two lemmas here package
that: `not_exists_tor_vanishing_bound_of_forall_ne_zero` takes nonvanishing in every degree, and
`not_exists_tor_vanishing_bound_of_even_ne_zero` takes it only in the even degrees `2n`, which is
all Gulliksen's argument provides — the obstruction there is the class `γ_n(ξ)` in degree `2n`.

Also here is the computation of when a homology class of a chain complex of modules vanishes:
`homologyπ_eq_zero_iff_exists_boundary` says the class of a cycle is zero exactly when the cycle
is a boundary, which is how the nonvanishing above is checked in practice.

## Main results

* `not_exists_tor_vanishing_bound_of_forall_ne_zero`,
  `not_exists_tor_vanishing_bound_of_even_ne_zero` — contradicting finite Tor dimension.
* `homologyπ_eq_zero_iff_exists_boundary` — a homology class vanishes iff its cycle bounds.

## References

* [Stacks Project, Tag 09PU](https://stacks.math.columbia.edu/tag/09PU)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open CategoryTheory Limits

universe u v

/-- If `Tor i (S, M)` is nonzero for every `i`, then `S` has no uniform degree beyond which
`Tor` against every module vanishes. -/
public theorem not_exists_tor_vanishing_bound_of_forall_ne_zero
    {R S M : Type u} [CommRing R] [AddCommGroup S] [Module R S]
    [AddCommGroup M] [Module R M]
    (h : ∀ i : ℕ,
      ¬ IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj
        (ModuleCat.of R M))) :
    ¬ ∃ b : ℕ, ∀ (N : ModuleCat.{u} R) (i : ℕ), b < i →
      IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj N) := by
  rintro ⟨b, hb⟩
  exact h (b + 1) (hb (ModuleCat.of R M) (b + 1) (by omega))

/-- Nonvanishing of `Tor` in the even degrees `2n`, `n > 0`, already contradicts finite Tor
dimension: beyond any claimed bound `b` lies `2(b+1)`. This is the form Gulliksen's argument
delivers, its obstruction in degree `2n` being the `n`-th divided power of a degree-2 class. -/
public theorem not_exists_tor_vanishing_bound_of_even_ne_zero
    {R S M : Type u} [CommRing R] [AddCommGroup S] [Module R S]
    [AddCommGroup M] [Module R M]
    (h : ∀ n : ℕ, 0 < n →
      ¬ IsZero (((Tor (ModuleCat.{u} R) (2 * n)).obj (ModuleCat.of R S)).obj
        (ModuleCat.of R M))) :
    ¬ ∃ b : ℕ, ∀ (N : ModuleCat.{u} R) (i : ℕ), b < i →
      IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj N) := by
  rintro ⟨b, hb⟩
  exact h (b + 1) (by omega) (hb (ModuleCat.of R M) (2 * (b + 1)) (by omega))

/-- The homology class of a cycle in a chain complex of modules vanishes exactly when the cycle
is the image of the differential. The forward direction uses exactness of
`X (n+1) → cycles n → homology n` at the middle, the reverse that `toCycles` composed with
`homologyπ` is zero. -/
public theorem homologyπ_eq_zero_iff_exists_boundary
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔
      ∃ y : K.X (n + 1), K.d (n + 1) n y = K.iCycles n z := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    { X₁ := K.X (n + 1), X₂ := K.cycles n, X₃ := K.homology n,
      f := K.toCycles (n + 1) n, g := K.homologyπ n,
      zero := K.toCycles_comp_homologyπ (n + 1) n }
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel (n + 1) n (by simp))
  have hi : ∀ y, K.iCycles n (K.toCycles (n + 1) n y) = K.d (n + 1) n y := fun y =>
    congrArg (fun k : K.X (n + 1) ⟶ K.X n => k y) (K.toCycles_i (n + 1) n)
  constructor
  · intro hz
    obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
    exact ⟨y, (hi y).symm⟩
  · rintro ⟨y, hy⟩
    obtain rfl : K.toCycles (n + 1) n y = z :=
      (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance ((hi y).trans hy)
    exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ (n + 1) n) y

end DividedPowers.TateResolution

end
