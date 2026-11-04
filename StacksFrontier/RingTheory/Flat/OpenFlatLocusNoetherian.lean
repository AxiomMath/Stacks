module

import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Coalgebra.CoassocSimps

public import StacksFrontier.RingTheory.Flat.FiberExactLocus
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.Sequence.RegularLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness of the flat locus over a polynomial ring with Noetherian base

Let `R` be a Noetherian ring, let `P = R[x_1, …, x_n]` and let `M` be a finitely presented
`P`-module. This file proves that the flat locus of `M` relative to `R`,
`{𝔮 ∈ Spec(P) | M_𝔮 is flat over R}`, is open.

The ring map `R → P` is flat and every fibre `P ⊗_R κ(𝔭)` is the polynomial ring
`κ(𝔭)[x_1, …, x_n]`, hence regular of dimension `n`. Resolve `M` by finite free `P`-modules and
split the resolution into the short exact sequences `0 → K_{i+1} → F_i → K_i → 0` of its syzygies.
Then:

1. every `(K_i)_𝔮` is flat over `R`, and the `(m+1)`-st syzygy is *free* at `𝔮` for every `m ≥ n`
   (`Module.free_localizedModule_atPrime_of_forall_shortExact`);
2. clearing denominators
   (`Stacks.Flatness.OpenFlatLocus.exists_linearMap_bijective_baseChange`) turns a basis of
   `(K_{m+1})_𝔮` into a map `β : P^r → K_{m+1}` which becomes an isomorphism at `𝔮`, so that the
   finite complex `0 → P^r → F_m → ⋯ → F_0` of finite free `P`-modules — the truncated
   resolution — has exact fibre complex at `𝔮`
   (`Stacks.Flatness.OpenFlatLocus.truncFibreExact_of_forall_flat`);
3. the locus where that fibre complex is exact is open
   (`Stacks.Flatness.OpenFlatLocus.exists_basicOpen_truncFibreExact`);
4. at every prime of a basic open inside it, the local criterion for flatness at the bottom index
   makes the cokernel of `F_1 → F_0`, which is `M`, flat over `R`
   (`Stacks.Flatness.OpenFlatLocus.flat_baseChange_zero_of_truncFibreExact`);
5. flatness over `R` is local on `Spec(P_g)`, so `M_g` is flat over `R`
   (`Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime`).

## Main definitions

* `LinearMap.clampFin`, `LinearMap.clampFinEquiv`: reindexing between standard free modules of
  possibly different ranks.
* `FreeComplexTruncation.truncD`: the differentials of the truncated complex.

## Main results

In the namespace `Stacks.Flatness.OpenFlatLocus`:

* `exists_away_flat_of_flat_atPrime_mvPolynomial_of_isNoetherianRing`: if `M_𝔮` is flat over `R`
  then `M_g` is flat over `R` for some `g ∉ 𝔮`.
* `isOpen_setOf_flat_localizedModule_atPrime_mvPolynomial`: the flat locus is open.

## Implementation notes
*The truncated complex.* The openness of the fibre-exact locus takes its complex as a family
`F : ℕ → Type*` with `φ : ∀ i, F (i+1) →ₗ[S] F i`, so the truncated complex has to be presented as
a family which is `F i` below an index and `P^r` at it. Such a family has no definitional
description in Lean — `if i ≤ m then F i else G` reduces for no variable `i`, and building it by
transport along propositional equalities of types puts a `cast` in every differential. The way out
is to take the family to consist of *standard* free modules `Fin (truncRank i) → P`: the cut and
paste then happens in the rank function `truncRank : ℕ → ℕ`, which is an ordinary arithmetic `if`,
and the family is a plain function of it. `LinearMap.clampFin`, defined for *all* pairs of ranks,
absorbs the fact that `truncRank i` is only propositionally `c i`; the differentials are honest
composites, with no `cast` anywhere, and `Module.Free`/`Module.Finite` for the family are found by
instance
search.

*Which syzygy.* The truncation is taken at `m = n + 1`, not at `m = n`. Any `m ≥ n` works, since
the fibre ring has dimension at most `n ≤ m`, and taking `m ≥ 1` makes the bottom differential of
the truncated complex the resolution's own `F_1 → F_0` in every case, so that its cokernel is `M`
on the nose, with no appeal to `β` and no separate treatment of `n = 0` and `n = 1`.

*Base change in two steps.* The fibre condition is a base change from `P` to `T = P_𝔮/𝔭P_𝔮`,
while the flatness machinery and the local criterion live over `P_𝔮`. The two are matched by
`Stacks.Flatness.OpenFlatLocus.injective_baseChange_iff_baseChange` and
`Stacks.Flatness.OpenFlatLocus.exact_baseChange_iff_baseChange`, which read a base change to `T`
through the intermediate `P_𝔮` using
`Stacks.Flatness.FibreExactnessLocus.baseChange_comp_cancelBaseChange`.

*Universes.* The terms of a finite free resolution of `M` over `P` are standard free `P`-modules,
so they live in the universe of `R`, and the dimension-shifting step needs them in the universe of
`M` as well; the technical core therefore has `R` and `M` in one universe. The main results do
not: a finitely presented module is isomorphic to a quotient of a standard free module, and
replacing `M` by such a quotient removes the restriction.

## References

* [StacksProject 00MH](https://stacks.math.columbia.edu/tag/00MH)
* [StacksProject 00MI](https://stacks.math.columbia.edu/tag/00MI)
* [StacksProject 00RB](https://stacks.math.columbia.edu/tag/00RB)
* [StacksProject 00RC](https://stacks.math.columbia.edu/tag/00RC)

## Tags

flat locus, openness of flatness, free resolution, syzygy, truncated complex, polynomial ring,
fibre, local criterion for flatness
-/

@[expose] public section

open TensorProduct

universe u v

namespace LinearMap
open Stacks.RegularSequence.FibrewiseLocus

/-! ### Reindexing standard free modules -/

/-- The map `(Fin a → S) → (Fin b → S)` which reindexes along the identity on `ℕ`, extending by
zero where the source runs out. It is an isomorphism as soon as `a = b`
(`LinearMap.clampFinEquiv`).

It is defined for *all* `a` and `b`, so a family of standard free modules can be compared with a
family whose ranks are only propositionally equal to its own, without transporting along an
equality of types. -/
def clampFin (S : Type*) [CommRing S] (a b : ℕ) : (Fin a → S) →ₗ[S] (Fin b → S) where
  toFun w x := if h : (x : ℕ) < a then w ⟨x, h⟩ else 0
  map_add' v w := by funext x; by_cases h : (x : ℕ) < a <;> simp [h]
  map_smul' t w := by funext x; by_cases h : (x : ℕ) < a <;> simp [h]

/-- `LinearMap.clampFin` sends `w` to the function which is `w x` at indices `x < a` and `0`
elsewhere. -/
theorem clampFin_apply {S : Type*} [CommRing S] {a b : ℕ} (w : Fin a → S) (x : Fin b) :
    clampFin S a b w x = if h : (x : ℕ) < a then w ⟨x, h⟩ else 0 := rfl

/-- `LinearMap.clampFin` between two equal ranks is the identity. -/
@[simp] theorem clampFin_self (S : Type*) [CommRing S] (a : ℕ) :
    clampFin S a a = LinearMap.id :=
  LinearMap.ext fun w => funext fun x => by simp [clampFin_apply, x.isLt]

/-- For `a = b`, `LinearMap.clampFin S b a` is a left inverse of `LinearMap.clampFin S a b`. -/
theorem clampFin_clampFin {S : Type*} [CommRing S] {a b : ℕ} (h : a = b) (w : Fin a → S) :
    clampFin S b a (clampFin S a b w) = w := by subst h; simp

/-- `LinearMap.clampFin` as an isomorphism, for two ranks that agree. -/
def clampFinEquiv (S : Type*) [CommRing S] {a b : ℕ} (h : a = b) :
    (Fin a → S) ≃ₗ[S] (Fin b → S) :=
  LinearEquiv.ofLinearMap (clampFin S a b) (clampFin S b a) (by subst h; simp) (by subst h; simp)

/-- `LinearMap.clampFinEquiv` acts as `LinearMap.clampFin`. -/
@[simp] theorem clampFinEquiv_apply {S : Type*} [CommRing S] {a b : ℕ} (h : a = b)
    (w : Fin a → S) : clampFinEquiv S h w = clampFin S a b w := rfl

/-- The inverse of `LinearMap.clampFinEquiv` acts as `LinearMap.clampFin` in the other
direction. -/
@[simp] theorem clampFinEquiv_symm_apply {S : Type*} [CommRing S] {a b : ℕ} (h : a = b)
    (w : Fin b → S) : (clampFinEquiv S h).symm w = clampFin S b a w := rfl

/-- The underlying linear map of `LinearMap.clampFinEquiv` is `LinearMap.clampFin`. -/
@[simp] theorem coe_clampFinEquiv {S : Type*} [CommRing S] {a b : ℕ} (h : a = b) :
    (clampFinEquiv S h : (Fin a → S) →ₗ[S] (Fin b → S)) = clampFin S a b := rfl

/-- The underlying linear map of the inverse of `LinearMap.clampFinEquiv` is
`LinearMap.clampFin` in the other direction. -/
@[simp] theorem coe_clampFinEquiv_symm {S : Type*} [CommRing S] {a b : ℕ} (h : a = b) :
    ((clampFinEquiv S h).symm : (Fin b → S) →ₗ[S] (Fin a → S)) = clampFin S b a := rfl

/-- A commuting square of `S`-modules whose verticals are isomorphisms stays commuting after base
change to an `S`-algebra `T`. -/
theorem baseChange_comp_coe_baseChange {S : Type*} [CommRing S] {X X' Y Y' : Type*}
    [AddCommGroup X] [Module S X] [AddCommGroup X'] [Module S X'] [AddCommGroup Y] [Module S Y]
    [AddCommGroup Y'] [Module S Y'] (T : Type*) [CommRing T] [Algebra S T] {u : X →ₗ[S] Y}
    {v : X' →ₗ[S] Y'} {e₁ : X' ≃ₗ[S] X} {e₂ : Y' ≃ₗ[S] Y} (h : u ∘ₗ ↑e₁ = ↑e₂ ∘ₗ v) :
    LinearMap.baseChange T u ∘ₗ ↑(e₁.baseChange S T X' X) =
      ↑(e₂.baseChange S T Y' Y) ∘ₗ LinearMap.baseChange T v := by
  rw [Stacks.Flatness.FibreExactnessLocus.coe_baseChange_linearEquiv,
      Stacks.Flatness.FibreExactnessLocus.coe_baseChange_linearEquiv,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]

end LinearMap

namespace FreeComplexTruncation
open Stacks.RegularSequence.FibrewiseLocus

/-! ### The truncated complex `0 → S^r → F_m → ⋯ → F_0` in coordinates -/

variable {S : Type u} [CommRing S] {F : ℕ → Type u} [∀ i, AddCommGroup (F i)]
  [∀ i, Module S (F i)] (c : ℕ → ℕ) (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S))
  (dd : ∀ i, F (i + 1) →ₗ[S] F i) (m r : ℕ) (psi : (Fin r → S) →ₗ[S] F m)

/-- The ranks of the truncated complex `0 → S^r → F_m → ⋯ → F_0`: the rank of `F i` below `m`, then
`r`, then `0`. Only the *ranks* are cut and pasted, so this is a function `ℕ → ℕ` and the family of
modules `fun i => Fin (truncRank i) → S` is a plain function of it, with no type-level case
split. -/
def truncRank (i : ℕ) : ℕ := if i ≤ m then c i else if i = m + 1 then r else 0

/-- For `i ≤ m`, `truncRank c m r i` is `c i`. -/
theorem truncRank_of_le {i : ℕ} (h : i ≤ m) : truncRank c m r i = c i := by
  rw [truncRank, ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- `truncRank c m r (m + 1)` is `r`. -/
theorem truncRank_succ : truncRank c m r (m + 1) = r := by
  rw [truncRank, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- The differentials of the truncated complex, in coordinates: the `i`-th differential of the
resolution read in the chosen bases for `i < m`, the map `psi` at `i = m`, and `0` above. The
`LinearMap.clampFin`s absorb the fact that `truncRank i` is only propositionally `c i`. -/
noncomputable def truncD (i : ℕ) :
    (Fin (truncRank c m r (i + 1)) → S) →ₗ[S] (Fin (truncRank c m r i) → S) :=
  if i < m then
    LinearMap.clampFin S (c i) (truncRank c m r i) ∘ₗ
      ((E i).toLinearMap ∘ₗ dd i ∘ₗ (E (i + 1)).symm.toLinearMap) ∘ₗ
      LinearMap.clampFin S (truncRank c m r (i + 1)) (c (i + 1))
  else if i = m then
    LinearMap.clampFin S (c m) (truncRank c m r i) ∘ₗ ((E m).toLinearMap ∘ₗ psi) ∘ₗ
      LinearMap.clampFin S (truncRank c m r (i + 1)) r
  else 0

/-- For `i < m`, `truncD` is the `i`-th differential of the resolution read in the chosen bases. -/
theorem truncD_of_lt {i : ℕ} (h : i < m) :
    truncD c E dd m r psi i =
      LinearMap.clampFin S (c i) (truncRank c m r i) ∘ₗ
        ((E i).toLinearMap ∘ₗ dd i ∘ₗ (E (i + 1)).symm.toLinearMap) ∘ₗ
        LinearMap.clampFin S (truncRank c m r (i + 1)) (c (i + 1)) := by
  rw [truncD, ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- At `i = m`, `truncD` is the map `psi` read in the chosen basis of `F m`. -/
theorem truncD_top :
    truncD c E dd m r psi m =
      LinearMap.clampFin S (c m) (truncRank c m r m) ∘ₗ ((E m).toLinearMap ∘ₗ psi) ∘ₗ
        LinearMap.clampFin S (truncRank c m r (m + 1)) r := by
  rw [truncD, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl m)),
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- For `i > m`, `truncD` is zero. -/
theorem truncD_of_gt {i : ℕ} (h : m < i) : truncD c E dd m r psi i = 0 := by
  rw [truncD, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The identification `F i ≅ S^{truncRank i}` for `i ≤ m`. -/
noncomputable def truncEquiv {i : ℕ} (h : i ≤ m) : F i ≃ₗ[S] (Fin (truncRank c m r i) → S) :=
  (E i).trans (LinearMap.clampFinEquiv S (truncRank_of_le c m r h).symm)

/-- `truncEquiv` applies the chosen basis `E i` and then reindexes by `LinearMap.clampFin`. -/
theorem truncEquiv_apply {i : ℕ} (h : i ≤ m) (x : F i) :
    truncEquiv c E m r h x = LinearMap.clampFin S (c i) (truncRank c m r i) (E i x) := rfl

/-- The ladder square identifying the `i`-th differential of the truncated complex with the `i`-th
differential of the resolution, for `i < m`. -/
theorem truncD_comp_truncEquiv {i : ℕ} (h : i < m) :
    truncD c E dd m r psi i ∘ₗ ↑(truncEquiv c E m r (Nat.succ_le_of_lt h)) =
      ↑(truncEquiv c E m r h.le) ∘ₗ dd i := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    truncD_of_lt c E dd m r psi h, truncEquiv_apply, truncEquiv_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.clampFin_clampFin (truncRank_of_le c m r (Nat.succ_le_of_lt h)).symm,
    LinearEquiv.symm_apply_apply]

/-- The ladder square identifying the top differential of the truncated complex with `psi`. -/
theorem truncD_comp_clampFinEquiv :
    truncD c E dd m r psi m ∘ₗ ↑(LinearMap.clampFinEquiv S (truncRank_succ c m r).symm) =
      ↑(truncEquiv c E m r le_rfl) ∘ₗ psi := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    truncD_top c E dd m r psi, truncEquiv_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.clampFinEquiv_apply]
  rw [LinearMap.clampFin_clampFin (truncRank_succ c m r).symm]

/-- **The truncated complex is a complex, below the top.** -/
theorem truncD_comp_truncD_of_succ_lt (hd : ∀ i, dd i ∘ₗ dd (i + 1) = 0) {k : ℕ}
    (hk : k + 1 < m) :
    truncD c E dd m r psi k ∘ₗ truncD c E dd m r psi (k + 1) = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (truncEquiv c E m r (Nat.succ_le_of_lt hk)).surjective x
  have h2 := LinearMap.congr_fun (truncD_comp_truncEquiv c E dd m r psi hk) y
  have h1 := LinearMap.congr_fun
    (truncD_comp_truncEquiv c E dd m r psi (by omega : k < m)) (dd (k + 1) y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [h2, h1, ← LinearMap.comp_apply, hd k]
  simp

/-- **The truncated complex is a complex at the top**, where it is that `psi` lands in the kernel
of the differential below it. The length is spelled `k + 1` so that the hypothesis on `psi`
typechecks. -/
theorem truncD_comp_truncD_top {k r : ℕ} (psi : (Fin r → S) →ₗ[S] F (k + 1))
    (hpsi : dd k ∘ₗ psi = 0) :
    truncD c E dd (k + 1) r psi k ∘ₗ truncD c E dd (k + 1) r psi (k + 1) = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ :=
    (LinearMap.clampFinEquiv S (truncRank_succ c (k + 1) r).symm).surjective x
  have h1 := LinearMap.congr_fun (truncD_comp_clampFinEquiv c E dd (k + 1) r psi) y
  have h2 := LinearMap.congr_fun
    (truncD_comp_truncEquiv c E dd (k + 1) r psi (Nat.lt_succ_self k)) (psi y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [h1, h2, ← LinearMap.comp_apply, hpsi]
  simp

end FreeComplexTruncation

namespace Stacks.Flatness.OpenFlatLocus
open Stacks.RegularSequence.FibrewiseLocus

open Stacks.Flatness.FibreExactnessLocus FreeComplexTruncation

/-! ### Base change in two steps -/

section TwoStep

variable {S : Type*} [CommRing S] {X Y Z : Type*} [AddCommGroup X] [Module S X]
  [AddCommGroup Y] [Module S Y] [AddCommGroup Z] [Module S Z]
  (A : Type*) [CommRing A] [Algebra S A] (T : Type*) [CommRing T] [Algebra S T] [Algebra A T]
  [IsScalarTower S A T]

/-- Injectivity after base change to `T` may be read in two steps, through an intermediate
`S`-algebra `A`. -/
theorem injective_baseChange_iff_baseChange (f : X →ₗ[S] Y) :
    Function.Injective (LinearMap.baseChange T f) ↔
      Function.Injective (LinearMap.baseChange T (LinearMap.baseChange A f)) :=
  injective_iff_of_ladder_linearEquiv (baseChange_comp_cancelBaseChange A T f)

/-- Exactness after base change to `T` may be read in two steps, through an intermediate
`S`-algebra `A`. -/
theorem exact_baseChange_iff_baseChange (f : X →ₗ[S] Y) (g : Y →ₗ[S] Z) :
    Function.Exact (LinearMap.baseChange T f) (LinearMap.baseChange T g) ↔
      Function.Exact (LinearMap.baseChange T (LinearMap.baseChange A f))
        (LinearMap.baseChange T (LinearMap.baseChange A g)) :=
  Function.Exact.iff_of_ladder_linearEquiv (baseChange_comp_cancelBaseChange A T f)
    (baseChange_comp_cancelBaseChange A T g)

end TwoStep

/-! ### Splicing a family of short exact sequences -/

/-- **Splicing.** If `0 → K (i+1) →[f i] F i →[g i] K i → 0` is short exact for every `i`, then the
spliced complex `⋯ → F (i+1) →[f i ∘ g (i+1)] F i → ⋯` is exact. -/
theorem exact_comp_comp_of_forall_shortExact {B : Type*} [CommRing B] {K F : ℕ → Type*}
    [∀ i, AddCommGroup (K i)] [∀ i, Module B (K i)] [∀ i, AddCommGroup (F i)]
    [∀ i, Module B (F i)] (f : ∀ i, K (i + 1) →ₗ[B] F i) (g : ∀ i, F i →ₗ[B] K i)
    (hf : ∀ i, Function.Injective (f i)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hg : ∀ i, Function.Surjective (g i)) (i : ℕ) :
    Function.Exact (f (i + 1) ∘ₗ g (i + 2)) (f i ∘ₗ g (i + 1)) := by
  rw [LinearMap.exact_iff, LinearMap.ker_comp, LinearMap.range_comp,
    LinearMap.ker_eq_bot.mpr (hf i), Submodule.comap_bot,
    LinearMap.range_eq_top.mpr (hg (i + 2)), Submodule.map_top,
    ← LinearMap.exact_iff.mp (hfg (i + 1))]

/-- The range of a spliced differential is the range of the syzygy inclusion. -/
theorem range_comp_eq_range {B : Type*} [CommRing B] {K F : ℕ → Type*}
    [∀ i, AddCommGroup (K i)] [∀ i, Module B (K i)] [∀ i, AddCommGroup (F i)]
    [∀ i, Module B (F i)] (f : ∀ i, K (i + 1) →ₗ[B] F i) (g : ∀ i, F i →ₗ[B] K i)
    (hg : ∀ i, Function.Surjective (g i)) (i : ℕ) :
    LinearMap.range (f i ∘ₗ g (i + 1)) = LinearMap.range (f i) := by
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (hg (i + 1)), Submodule.map_top]

/-! ### The fibre-exactness condition of the truncated complex -/

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The fibre complex of the truncated complex `0 → S^r → F_m → ⋯ → F_0` is exact at `𝔮`:
the top differential becomes injective and the complex becomes exact at `F̄_m, …, F̄_1` after
`(S_𝔮/𝔭S_𝔮) ⊗_S -`. -/
def TruncFibreExact {F : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] (c : ℕ → ℕ)
    (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S)) (dd : ∀ i, F (i + 1) →ₗ[S] F i) (m r : ℕ)
    (psi : (Fin r → S) →ₗ[S] F m) (q : Ideal S) [q.IsPrime] : Prop :=
  Function.Injective
      (LinearMap.baseChange (fiberLocalRing R q) (truncD c E dd m r psi m)) ∧
    ∀ k < m, Function.Exact
      (LinearMap.baseChange (fiberLocalRing R q) (truncD c E dd m r psi (k + 1)))
      (LinearMap.baseChange (fiberLocalRing R q) (truncD c E dd m r psi k))

/-! ### Openness of the fibre-exact locus of the truncated complex -/

/-- **Openness of the fibre-exact locus of the truncated complex.** If the fibre complex of
`0 → S^r → F_m → ⋯ → F_0` is exact at `𝔮`, it is exact at every prime of a basic open neighbourhood
of `𝔮`. -/
theorem exists_basicOpen_truncFibreExact [IsNoetherianRing R] [Algebra.FiniteType R S]
    [Module.Flat R S] (d : ℕ)
    (hfib : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
          Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
        TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
        ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    {F : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] (c : ℕ → ℕ)
    (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S)) (dd : ∀ i, F (i + 1) →ₗ[S] F i) (m r : ℕ)
    (psi : (Fin r → S) →ₗ[S] F m)
    (hcomp : ∀ k < m, truncD c E dd m r psi k ∘ₗ truncD c E dd m r psi (k + 1) = 0)
    (q : Ideal S) [hqp : q.IsPrime] (hq : TruncFibreExact (R := R) c E dd m r psi q) :
    ∃ g ∉ q, ∀ q' : PrimeSpectrum S, q' ∈ PrimeSpectrum.basicOpen g →
      TruncFibreExact (R := R) c E dd m r psi q'.asIdeal := by
  have hopen :=
    Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay_of_equidimensional
      (R := R) (S := S) d hfib m (fun i => Fin (truncRank c m r i) → S)
      (truncD c E dd m r psi) hcomp
  obtain ⟨g, hgq, hg⟩ :=
    exists_basicOpen_subset_of_isOpen hopen (q := (⟨q, hqp⟩ : PrimeSpectrum S)) hq
  exact ⟨g, hgq, fun q' hq' => hg hq'⟩


/-! ### The fibre complex of the truncated resolution is exact at a point of flatness -/

section AtPrime

variable {F K : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
  [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]

/-- The range of a composite with a surjection is the range of the outer map. -/
theorem range_comp_of_surjective {B X Y Z : Type*} [CommRing B] [AddCommGroup X] [Module B X]
    [AddCommGroup Y] [Module B Y] [AddCommGroup Z] [Module B Z] (u : Y →ₗ[B] Z) {v : X →ₗ[B] Y}
    (hv : Function.Surjective v) : LinearMap.range (u ∘ₗ v) = LinearMap.range u := by
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hv, Submodule.map_top]

variable (c : ℕ → ℕ) (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S)) (incl : ∀ i, K (i + 1) →ₗ[S] F i)
  (proj : ∀ i, F i →ₗ[S] K i)

/-- **The fibre complex of the truncated resolution is exact at `𝔮`.** Let
`0 → K (i+1) → F i → K i → 0` be short exact for every `i`, with every `(K i)_𝔮` flat over `R`,
and let `β : S^r → K (m+1)` become an isomorphism at `𝔮`. Then the fibre complex at `𝔮` of the
truncated complex `0 → S^r → F_m → ⋯ → F_0` — whose top differential is `incl m ∘ β` and whose
lower ones are the spliced `incl i ∘ proj (i+1)` — is exact.

The reduction modulo `𝔭` of each short exact sequence stays short exact because its quotient
`(K i)_𝔮` is flat over `R` (`LinearMap.injective_baseChange_quotient_iff`), and the spliced complex
of a family of short exact sequences is exact (`exact_comp_comp_of_forall_shortExact`). -/
theorem truncFibreExact_of_forall_flat [Module.Flat R S]
    (hincl : ∀ i, Function.Injective (incl i))
    (hmid : ∀ i, Function.Exact (incl i) (proj i))
    (hproj : ∀ i, Function.Surjective (proj i))
    (q : Ideal S) [q.IsPrime]
    (hKflat : ∀ i, Module.Flat R (Localization.AtPrime q ⊗[S] K i))
    {m r : ℕ} (β : (Fin r → S) →ₗ[S] K (m + 1))
    (hβ : Function.Bijective (LinearMap.baseChange (Localization.AtPrime q) β)) :
    TruncFibreExact (R := R) c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) q := by
  have hAflat : Module.Flat S (Localization.AtPrime q) := inferInstance
  have hAincl : ∀ i, Function.Injective
      (LinearMap.baseChange (Localization.AtPrime q) (incl i)) := fun i =>
    Module.Flat.lTensor_preserves_injective_linearMap _ (hincl i)
  have hAmid : ∀ i, Function.Exact (LinearMap.baseChange (Localization.AtPrime q) (incl i))
      (LinearMap.baseChange (Localization.AtPrime q) (proj i)) := fun i =>
    Module.Flat.lTensor_exact _ (hmid i)
  have hAproj : ∀ i, Function.Surjective
      (LinearMap.baseChange (Localization.AtPrime q) (proj i)) := fun i =>
    LinearMap.baseChange_surjective _ (hproj i)
  have hTincl : ∀ i, Function.Injective (LinearMap.baseChange (fiberLocalRing R q)
      (LinearMap.baseChange (Localization.AtPrime q) (incl i))) := fun i => by
    have := hKflat i
    rw [LinearMap.injective_baseChange_quotient_iff (I := q.under R)]
    exact LinearMap.lTensor_injective_of_exact_of_flat
      ((LinearMap.baseChange (Localization.AtPrime q) (proj i)).restrictScalars R) (hAproj i)
      ((LinearMap.baseChange (Localization.AtPrime q) (incl i)).restrictScalars R) (hAincl i)
      (hAmid i) (R ⧸ q.under R)
  have hTmid : ∀ i, Function.Exact
      (LinearMap.baseChange (fiberLocalRing R q)
        (LinearMap.baseChange (Localization.AtPrime q) (incl i)))
      (LinearMap.baseChange (fiberLocalRing R q)
        (LinearMap.baseChange (Localization.AtPrime q) (proj i))) := fun i =>
    lTensor_exact _ (hAmid i) (hAproj i)
  have hTproj : ∀ i, Function.Surjective (LinearMap.baseChange (fiberLocalRing R q)
      (LinearMap.baseChange (Localization.AtPrime q) (proj i))) := fun i =>
    LinearMap.baseChange_surjective _ (hAproj i)
  set eβ := LinearEquiv.ofBijective (LinearMap.baseChange (Localization.AtPrime q) β) hβ with heβ
  have hTβ : Function.Bijective (LinearMap.baseChange (fiberLocalRing R q)
      (LinearMap.baseChange (Localization.AtPrime q) β)) := by
    have : (LinearMap.baseChange (Localization.AtPrime q) β) = ↑eβ := rfl
    rw [this, ← Stacks.Flatness.FibreExactnessLocus.coe_baseChange_linearEquiv]
    exact (eβ.baseChange (Localization.AtPrime q) (fiberLocalRing R q) _ _).bijective
  have hspl := fun k => exact_comp_comp_of_forall_shortExact
    (fun i => LinearMap.baseChange (fiberLocalRing R q)
      (LinearMap.baseChange (Localization.AtPrime q) (incl i)))
    (fun i => LinearMap.baseChange (fiberLocalRing R q)
      (LinearMap.baseChange (Localization.AtPrime q) (proj i))) hTincl hTmid hTproj k
  refine ⟨?_, fun k hk => ?_⟩
  · rw [injective_iff_of_ladder_linearEquiv (LinearMap.baseChange_comp_coe_baseChange
        (fiberLocalRing R q) (truncD_comp_clampFinEquiv c E
          (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β))),
      injective_baseChange_iff_baseChange (Localization.AtPrime q) (fiberLocalRing R q),
      LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    exact (hTincl m).comp hTβ.1
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with hkm | hkm
    · subst hkm
      rw [Function.Exact.iff_of_ladder_linearEquiv
        (LinearMap.baseChange_comp_coe_baseChange (fiberLocalRing R q)
          (truncD_comp_clampFinEquiv c E (fun i => incl i ∘ₗ proj (i + 1)) (k + 1) r
            (incl (k + 1) ∘ₗ β)))
        (LinearMap.baseChange_comp_coe_baseChange (fiberLocalRing R q)
          (truncD_comp_truncEquiv c E (fun i => incl i ∘ₗ proj (i + 1)) (k + 1) r
            (incl (k + 1) ∘ₗ β) hk)),
        exact_baseChange_iff_baseChange (Localization.AtPrime q) (fiberLocalRing R q)]
      simp only [LinearMap.baseChange_comp]
      rw [LinearMap.exact_iff, range_comp_of_surjective _ hTβ.2]
      exact (LinearMap.exact_iff.mp (hspl k)).trans
        (range_comp_of_surjective _ (hTproj (k + 2)))
    · rw [Function.Exact.iff_of_ladder_linearEquiv
        (LinearMap.baseChange_comp_coe_baseChange (fiberLocalRing R q)
          (truncD_comp_truncEquiv c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) hkm))
        (LinearMap.baseChange_comp_coe_baseChange (fiberLocalRing R q)
          (truncD_comp_truncEquiv c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) hk)),
        exact_baseChange_iff_baseChange (Localization.AtPrime q) (fiberLocalRing R q)]
      simp only [LinearMap.baseChange_comp]
      exact hspl k

end AtPrime


/-! ### The complex condition for the spliced truncated complex -/

section Spliced

variable {F K : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
  [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
  (c : ℕ → ℕ) (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S)) (incl : ∀ i, K (i + 1) →ₗ[S] F i)
  (proj : ∀ i, F i →ₗ[S] K i)

/-- In a spliced family of exact sequences, `proj i ∘ incl i = 0`. -/
theorem proj_comp_incl (hmid : ∀ i, Function.Exact (incl i) (proj i)) (i : ℕ) :
    proj i ∘ₗ incl i = 0 :=
  LinearMap.ext fun x => (hmid i).apply_apply_eq_zero x

/-- **The truncated resolution is a complex.** Below the top this is the splicing relation
`proj ∘ incl = 0`, and at the top it is that the top differential factors through `incl m`. -/
theorem truncD_comp_truncD_spliced (hmid : ∀ i, Function.Exact (incl i) (proj i)) {m r : ℕ}
    (β : (Fin r → S) →ₗ[S] K (m + 1)) {k : ℕ} (hk : k < m) :
    truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) k ∘ₗ
      truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) (k + 1) = 0 := by
  have hz : ∀ i y, proj i (incl i y) = 0 := fun i => (hmid i).apply_apply_eq_zero
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with hkm | hkm
  · subst hkm
    exact truncD_comp_truncD_top c E _ _ (LinearMap.ext fun x => by simp [hz])
  · exact truncD_comp_truncD_of_succ_lt c E _ _ _ _
      (fun i => LinearMap.ext fun x => by simp [hz]) hkm

end Spliced


/-! ### The cokernel of the bottom differential -/

section Coker

variable {F K : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
  [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
  (c : ℕ → ℕ) (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S)) (incl : ∀ i, K (i + 1) →ₗ[S] F i)
  (proj : ∀ i, F i →ₗ[S] K i)

/-- The exactness in the middle of the short exact sequences base changed along `S → A`. -/
theorem exact_baseChange_incl_proj (A : Type*) [CommRing A] [Algebra S A] [Module.Flat S A]
    (hmid : ∀ i, Function.Exact (incl i) (proj i)) (i : ℕ) :
    Function.Exact (LinearMap.baseChange A (incl i)) (LinearMap.baseChange A (proj i)) := by
  exact Module.Flat.lTensor_exact _ (hmid i)

/-- The surjectivity of the projections base changed along `S → A`. -/
theorem surjective_baseChange_proj (A : Type*) [CommRing A] [Algebra S A]
    (hproj : ∀ i, Function.Surjective (proj i)) (i : ℕ) :
    Function.Surjective (LinearMap.baseChange A (proj i)) := by
  exact LinearMap.baseChange_surjective _ (hproj i)

/-- **The range of the bottom differential of the truncated complex is the range of `incl 0`**,
read across the chosen identification of `F 0` with a standard free module. -/
theorem range_baseChange_truncD_zero (A : Type*) [CommRing A] [Algebra S A]
    (hproj : ∀ i, Function.Surjective (proj i)) {m r : ℕ} (hm : 0 < m)
    (β : (Fin r → S) →ₗ[S] K (m + 1)) :
    Submodule.map
        ((truncEquiv c E m r (Nat.zero_le m)).baseChange S A (F 0)
          (Fin (truncRank c m r 0) → S)).toLinearMap
        (LinearMap.range (LinearMap.baseChange A (incl 0))) =
      LinearMap.range (LinearMap.baseChange A
        (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 0)) := by
  have hlad := LinearMap.baseChange_comp_coe_baseChange (S := S) A
    (truncD_comp_truncEquiv c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) hm)
  have h1 : LinearMap.range (LinearMap.baseChange A
        (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 0)) =
      Submodule.map
        ((truncEquiv c E m r (Nat.zero_le m)).baseChange S A (F 0)
          (Fin (truncRank c m r 0) → S)).toLinearMap
        (LinearMap.range (LinearMap.baseChange A (incl 0 ∘ₗ proj 1))) := by
    rw [← range_comp_of_surjective _
      ((truncEquiv c E m r (Nat.succ_le_of_lt hm)).baseChange S A (F 1)
        (Fin (truncRank c m r 1) → S)).surjective, hlad, LinearMap.range_comp]
  have h2 : LinearMap.range (LinearMap.baseChange A (incl 0 ∘ₗ proj 1)) =
      LinearMap.range (LinearMap.baseChange A (incl 0)) := by
    rw [LinearMap.baseChange_comp (A := A) (proj 1) (incl 0)]
    exact range_comp_of_surjective _ (surjective_baseChange_proj proj A hproj 1)
  rw [h1, h2]

/-- **The cokernel of the bottom differential of the truncated complex is `A ⊗_S K 0`.** For a
resolution, `K 0` is the module being resolved, so this identifies the cokernel with its base
change. -/
noncomputable def cokerTruncDZeroEquiv (A : Type*) [CommRing A] [Algebra S A] [Module.Flat S A]
    (hmid : ∀ i, Function.Exact (incl i) (proj i))
    (hproj : ∀ i, Function.Surjective (proj i)) {m r : ℕ} (hm : 0 < m)
    (β : (Fin r → S) →ₗ[S] K (m + 1)) :
    ((A ⊗[S] (Fin (truncRank c m r 0) → S)) ⧸
        LinearMap.range (LinearMap.baseChange A
          (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 0))) ≃ₗ[A]
      (A ⊗[S] K 0) :=
  (Submodule.Quotient.equiv (LinearMap.range (LinearMap.baseChange A (incl 0))) _
      ((truncEquiv c E m r (Nat.zero_le m)).baseChange S A (F 0)
        (Fin (truncRank c m r 0) → S))
      (range_baseChange_truncD_zero c E incl proj A hproj hm β)).symm.trans
    ((Submodule.quotEquivOfEq _ _
        (LinearMap.exact_iff.mp (exact_baseChange_incl_proj incl proj A hmid 0)).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (surjective_baseChange_proj proj A hproj 0)))

end Coker


/-! ### The local criterion for flatness at one index, over `R_𝔭 → S_𝔮` -/

section LocalCriterion

attribute [local instance] Ideal.algebraLocalizationAtPrimeUnder
  Ideal.isScalarTower_localizationAtPrimeUnder
  Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder

/-- **The local criterion for flatness at one index.** Let `𝔮` be a prime of `S`, let
`X →[g] Y →[f] Z` be a complex of `S_𝔮`-modules with `Y` finite and `Z` free over `S_𝔮`, and
suppose the complex becomes exact after reducing modulo `𝔭 = R ∩ 𝔮`. Then `Z/f(Y)` is flat over
`R`.

This is `Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top` applied over the
local homomorphism `R_𝔭 → S_𝔮`, whose reduction modulo `𝔪_{R_𝔭}` is the fibre ring
(`Ideal.map_maximalIdeal_eq_map_under`), followed by `Module.flat_iff_of_isLocalization`, which
turns flatness over `R_𝔭` into flatness over `R`. -/
theorem flat_quotient_range_of_exact_baseChange_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] (q : Ideal S)
    [q.IsPrime] {X Y Z : Type*} [AddCommGroup X] [Module (Localization.AtPrime q) X]
    [AddCommGroup Y] [Module (Localization.AtPrime q) Y]
    [Module.Finite (Localization.AtPrime q) Y] [AddCommGroup Z] [Module R Z]
    [Module (Localization.AtPrime q) Z] [IsScalarTower R (Localization.AtPrime q) Z]
    [Module.Free (Localization.AtPrime q) Z] (g : X →ₗ[Localization.AtPrime q] Y)
    (f : Y →ₗ[Localization.AtPrime q] Z) (hfg : f ∘ₗ g = 0)
    (hex : Function.Exact (LinearMap.baseChange (fiberLocalRing R q) g)
      (LinearMap.baseChange (fiberLocalRing R q) f)) :
    Module.Flat R (Z ⧸ LinearMap.range f) := by
  have hnoethA : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have hflatRA : Module.Flat (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R)) (q.under R).primeCompl
      (Localization.AtPrime q)).mpr (Module.Flat.trans R S (Localization.AtPrime q))
  let modUY : Module (Localization.AtPrime (q.under R)) Y :=
    Module.compHom _
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
  let modUZ : Module (Localization.AtPrime (q.under R)) Z :=
    Module.compHom _
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
  have htY : IsScalarTower (Localization.AtPrime (q.under R)) (Localization.AtPrime q) Y :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htZ : IsScalarTower (Localization.AtPrime (q.under R)) (Localization.AtPrime q) Z :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htRZ : IsScalarTower R (Localization.AtPrime (q.under R)) Z :=
    IsScalarTower.of_algebraMap_smul fun a x => by
      show algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
        (algebraMap R (Localization.AtPrime (q.under R)) a) • x = a • x
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]
  have hflatZ : Module.Flat (Localization.AtPrime (q.under R)) Z :=
    Module.Flat.trans (Localization.AtPrime (q.under R)) (Localization.AtPrime q) Z
  have hJ : Ideal.map
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)))
      = (q.under R).map (algebraMap R (Localization.AtPrime q)) :=
    Ideal.map_maximalIdeal_eq_map_under q
  have hex' : Function.Exact (LinearMap.baseChange
      (Localization.AtPrime q ⧸ Ideal.map
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)))) g)
      (LinearMap.baseChange _ f) := by rw [hJ]; exact hex
  have hRp := (Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top
    (R := Localization.AtPrime (q.under R)) g f hfg
    (fun y hy => mem_sup_range_of_exact_baseChange _ g f hex' y hy)).2
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
    (q.under R).primeCompl (Z ⧸ LinearMap.range f)).mp hRp

end LocalCriterion


/-! ### Flatness of the resolved module at a prime where the fibre complex is exact -/

section Flatness

variable {F K : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
  [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
  (c : ℕ → ℕ) (E : ∀ i, F i ≃ₗ[S] (Fin (c i) → S)) (incl : ∀ i, K (i + 1) →ₗ[S] F i)
  (proj : ∀ i, F i →ₗ[S] K i)

/-- **The resolved module is flat over `R` at every prime where the fibre complex of the truncated
complex is exact.** This is `flat_quotient_range_of_exact_baseChange_fiber` at the bottom index,
together with the identification of the cokernel there with the base change of `K 0`. -/
theorem flat_baseChange_zero_of_truncFibreExact [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] (hmid : ∀ i, Function.Exact (incl i) (proj i))
    (hproj : ∀ i, Function.Surjective (proj i)) {m r : ℕ} (hm : 0 < m)
    (β : (Fin r → S) →ₗ[S] K (m + 1)) (q : Ideal S) [q.IsPrime]
    (hq : TruncFibreExact (R := R) c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) q) :
    Module.Flat R (Localization.AtPrime q ⊗[S] K 0) := by
  have hfinY : Module.Finite (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[S] (Fin (truncRank c m r 1) → S)) :=
    Module.Finite.base_change S (Localization.AtPrime q) _
  have hfreeZ : Module.Free (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[S] (Fin (truncRank c m r 0) → S)) := Module.Free.tensor
  have hfg : LinearMap.baseChange (Localization.AtPrime q)
        (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 0) ∘ₗ
      LinearMap.baseChange (Localization.AtPrime q)
        (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 1) = 0 := by
    rw [← LinearMap.baseChange_comp, truncD_comp_truncD_spliced c E incl proj hmid β hm]
    simp
  have hex : Function.Exact (LinearMap.baseChange (fiberLocalRing R q)
        (LinearMap.baseChange (Localization.AtPrime q)
          (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 1)))
      (LinearMap.baseChange (fiberLocalRing R q)
        (LinearMap.baseChange (Localization.AtPrime q)
          (truncD c E (fun i => incl i ∘ₗ proj (i + 1)) m r (incl m ∘ₗ β) 0))) := by
    rw [← exact_baseChange_iff_baseChange (Localization.AtPrime q) (fiberLocalRing R q)]
    exact hq.2 0 hm
  have hquot := flat_quotient_range_of_exact_baseChange_fiber q _ _ hfg hex
  exact Module.Flat.of_linearEquiv
    (((cokerTruncDZeroEquiv c E incl proj (Localization.AtPrime q) hmid hproj hm
      β).restrictScalars R).symm)

end Flatness


/-! ### Clearing denominators -/

/-- **Clearing denominators.** If `S_𝔮 ⊗_S X` is finite free over `S_𝔮`, then there is a map
`β : S^r → X` of `S`-modules whose base change to `S_𝔮` is an isomorphism: lift a basis of
`S_𝔮 ⊗_S X` to `X`, which is possible up to units because every element of a localization is
`x/s`. -/
theorem exists_linearMap_bijective_baseChange {S : Type u} [CommRing S] (q : Ideal S) [q.IsPrime]
    (X : Type u) [AddCommGroup X] [Module S X]
    [Module.Free (Localization.AtPrime q) (Localization.AtPrime q ⊗[S] X)]
    [Module.Finite (Localization.AtPrime q) (Localization.AtPrime q ⊗[S] X)] :
    ∃ (r : ℕ) (β : (Fin r → S) →ₗ[S] X),
      Function.Bijective (LinearMap.baseChange (Localization.AtPrime q) β) := by
  classical
  have hfin := Module.Free.ChooseBasisIndex.fintype (Localization.AtPrime q)
    (Localization.AtPrime q ⊗[S] X)
  set ι := Module.Free.ChooseBasisIndex (Localization.AtPrime q) (Localization.AtPrime q ⊗[S] X)
    with hι
  set b : Module.Basis (Fin (Fintype.card ι)) (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[S] X) :=
    (Module.Free.chooseBasis (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[S] X)).reindex (Fintype.equivFin ι) with hb
  choose p hp0 using fun j : Fin (Fintype.card ι) => IsLocalizedModule.mk'_surjective q.primeCompl
    (TensorProduct.mk S (Localization.AtPrime q) X 1) (b j)
  have hp : ∀ j, IsLocalizedModule.mk'
      (TensorProduct.mk S (Localization.AtPrime q) X 1) (p j).1 (p j).2 = b j := hp0
  have hunit : ∀ j, IsUnit (algebraMap S (Localization.AtPrime q) ((p j).2 : S)) := fun j =>
    IsLocalization.map_units (Localization.AtPrime q) (p j).2
  have hb' : ∀ j, (b.isUnitSMul hunit) j = (1 : Localization.AtPrime q) ⊗ₜ[S] (p j).1 := fun j => by
    have hc := IsLocalizedModule.mk'_cancel'
      (TensorProduct.mk S (Localization.AtPrime q) X 1) (p j).1 (p j).2
    rw [Module.Basis.isUnitSMul_apply, ← hp j, IsScalarTower.algebraMap_smul]
    exact hc
  refine ⟨Fintype.card ι, Fintype.linearCombination S (fun j => (p j).1), ?_⟩
  set b1 := Module.Basis.ofIsLocalizedModule (Localization.AtPrime q) q.primeCompl
    (TensorProduct.mk S (Localization.AtPrime q) (Fin (Fintype.card ι) → S) 1)
    (Pi.basisFun S (Fin (Fintype.card ι))) with hb1
  have hkey : LinearMap.baseChange (Localization.AtPrime q)
      (Fintype.linearCombination S (fun j => (p j).1)) =
      (b1.equiv (b.isUnitSMul hunit) (Equiv.refl _)).toLinearMap := by
    refine Module.Basis.ext b1 fun j => ?_
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [hb' j, hb1, Module.Basis.ofIsLocalizedModule_apply]
    simp [Fintype.linearCombination_apply, Pi.single_apply, LinearMap.baseChange_tmul]
  rw [hkey]
  exact (b1.equiv (b.isUnitSMul hunit) (Equiv.refl _)).bijective


/-! ### The flat locus over a polynomial ring with Noetherian base -/

attribute [local instance] Ideal.algebraLocalizationAtPrimeUnder
  Ideal.isScalarTower_localizationAtPrimeUnder
  Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder

/-- **Flatness spreads out over a polynomial ring with Noetherian base**: if `M_𝔮` is flat over `R`
then `M_{𝔮'}` is flat over `R` for every `𝔮'` in a basic open neighbourhood of `𝔮`. -/
theorem exists_basicOpen_forall_flat_localizedModule_mvPolynomial
    {R M : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M]
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule.AtPrime q M)) :
    ∃ g ∉ q, ∀ q' : PrimeSpectrum (MvPolynomial (Fin n) R), q' ∈ PrimeSpectrum.basicOpen g →
      Module.Flat R (LocalizedModule.AtPrime q'.asIdeal M) := by
  classical
  have hnoethP : IsNoetherianRing (MvPolynomial (Fin n) R) :=
    Algebra.FiniteType.isNoetherianRing R (MvPolynomial (Fin n) R)
  obtain ⟨Res, hex, hff⟩ := exists_finite_free_resolution (MvPolynomial (Fin n) R) M
  let modRF : ∀ i, Module R (Res.F i) := fun _ =>
    Module.compHom _ (algebraMap R (MvPolynomial (Fin n) R))
  have towRF : ∀ i, IsScalarTower R (MvPolynomial (Fin n) R) (Res.F i) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let modRK : ∀ i, Module R (Res.syzygy i) := fun i =>
    match i with
    | 0 => inferInstanceAs (Module R M)
    | (_ + 1) => Module.compHom _ (algebraMap R (MvPolynomial (Fin n) R))
  have towRK : ∀ i, IsScalarTower R (MvPolynomial (Fin n) R) (Res.syzygy i) := fun i =>
    match i with
    | 0 => inferInstanceAs (IsScalarTower R (MvPolynomial (Fin n) R) M)
    | (_ + 1) => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfreeF : ∀ i, Module.Free (MvPolynomial (Fin n) R) (Res.F i) := fun i => (hff i).1
  have hfinF : ∀ i, Module.Finite (MvPolynomial (Fin n) R) (Res.F i) := fun i => (hff i).2
  have hfinK : ∀ i, Module.Finite (MvPolynomial (Fin n) R) (Res.syzygy i) :=
    Res.finite_syzygy fun i => (hff i).2
  set incl := Res.syzygyIncl with hincldef
  set proj := Res.syzygyProj hex.isComplex with hprojdef
  have hinclinj : ∀ i, Function.Injective (incl i) := Res.injective_syzygyIncl
  have hmid : ∀ i, Function.Exact (incl i) (proj i) := Res.exact_syzygy hex.isComplex
  have hprojsurj : ∀ i, Function.Surjective (proj i) := Res.surjective_syzygyProj hex
  have hfintype : ∀ i, Fintype (Module.Free.ChooseBasisIndex (MvPolynomial (Fin n) R) (Res.F i)) :=
    fun i => Module.Free.ChooseBasisIndex.fintype _ _
  set c : ℕ → ℕ := fun i =>
    Fintype.card (Module.Free.ChooseBasisIndex (MvPolynomial (Fin n) R) (Res.F i)) with hcdef
  set E : ∀ i, Res.F i ≃ₗ[MvPolynomial (Fin n) R] (Fin (c i) → MvPolynomial (Fin n) R) := fun i =>
    ((Module.Free.chooseBasis (MvPolynomial (Fin n) R) (Res.F i)).reindex
      (Fintype.equivFin _)).equivFun with hEdef
  have hAflatR : Module.Flat R (Localization.AtPrime q) :=
    Module.Flat.trans R (MvPolynomial (Fin n) R) (Localization.AtPrime q)
  have hAF : ∀ i, Module.Flat R (Localization.AtPrime q ⊗[MvPolynomial (Fin n) R] Res.F i) :=
    fun i =>
      have : Module.Free (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[MvPolynomial (Fin n) R] Res.F i) := Module.Free.tensor
      Module.Flat.trans R (Localization.AtPrime q) _
  have hA0 : Module.Flat R (Localization.AtPrime q ⊗[MvPolynomial (Fin n) R] Res.syzygy 0) :=
    Module.Flat.of_linearEquiv
      ((LocalizedModule.equivTensorProduct q.primeCompl M).restrictScalars R).symm
  have hKflat : ∀ i,
      Module.Flat R (Localization.AtPrime q ⊗[MvPolynomial (Fin n) R] Res.syzygy i) :=
    Module.Flat.of_forall_shortExact hAF
      (fun i => (LinearMap.baseChange (Localization.AtPrime q) (incl i)).restrictScalars R)
      (fun i => (LinearMap.baseChange (Localization.AtPrime q) (proj i)).restrictScalars R)
      (fun i =>
        show Function.Injective (LinearMap.baseChange (Localization.AtPrime q) (incl i)) from by
          rw [LinearMap.baseChange_eq_ltensor]
          exact Module.Flat.lTensor_preserves_injective_linearMap _ (hinclinj i))
      (fun i => exact_baseChange_incl_proj incl proj _ hmid i)
      (fun i => surjective_baseChange_proj proj _ hprojsurj i) hA0
  have hdim : ringKrullDim (fiberLocalRing R q) ≤ ((n + 2 : ℕ) : WithBot ℕ∞) :=
    (Ideal.ringKrullDim_fiberRing_mvPolynomial_le q).trans
      (by exact_mod_cast Nat.le_add_right n 2)
  have hfreeK : Module.Free (Localization.AtPrime q)
      (LocalizedModule.AtPrime q (Res.syzygy (n + 2))) :=
    Module.free_localizedModule_atPrime_of_forall_shortExact (K := fun i => Res.syzygy i)
      (F := fun i => Res.F i) incl proj hinclinj hmid hprojsurj q (n := n + 2)
      (Ideal.isRegularLocalRing_fiberRing_mvPolynomial q) hdim hq
  have hfreeKt : Module.Free (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[MvPolynomial (Fin n) R] Res.syzygy (n + 2)) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct q.primeCompl (Res.syzygy (n + 2)))
  have hfinKt : Module.Finite (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[MvPolynomial (Fin n) R] Res.syzygy (n + 2)) :=
    Module.Finite.base_change _ _ _
  obtain ⟨r, β, hβ⟩ := exists_linearMap_bijective_baseChange q (Res.syzygy (n + 2))
  have hqex := truncFibreExact_of_forall_flat c E incl proj hinclinj hmid hprojsurj q hKflat β hβ
  have hcomp : ∀ k < n + 1, truncD c E (fun i => incl i ∘ₗ proj (i + 1)) (n + 1) r
      (incl (n + 1) ∘ₗ β) k ∘ₗ
      truncD c E (fun i => incl i ∘ₗ proj (i + 1)) (n + 1) r (incl (n + 1) ∘ₗ β) (k + 1) = 0 :=
    fun k hk => truncD_comp_truncD_spliced c E incl proj hmid β hk
  obtain ⟨g, hgq, hg⟩ := exists_basicOpen_truncFibreExact (R := R) n
    (fun p _ _ =>
      Ideal.isMaximalCohenMacaulay_and_equidimensional_and_ringKrullDim_fiber_mvPolynomial p n)
    c E _ (n + 1) r _ hcomp q hqex
  refine ⟨g, hgq, fun q' hq'' => ?_⟩
  have hflat0 := flat_baseChange_zero_of_truncFibreExact c E incl proj hmid hprojsurj
    (Nat.succ_pos n) β q'.asIdeal (hg q' hq'')
  have hflat0' : Module.Flat R
      (Localization.AtPrime q'.asIdeal ⊗[MvPolynomial (Fin n) R] M) := hflat0
  exact Module.Flat.of_linearEquiv
    ((LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl M).restrictScalars R)


/-! ### From flatness at the points of a basic open to flatness over it -/

/-- **Flatness over the base spreads from the points of a basic open to the basic open itself.** If
`M_{𝔮}` is flat over `R` for every prime `𝔮` of `S` with `g ∉ 𝔮`, then `M_g` is flat over `R`.

Flatness over `R` is local on `Spec (S_g)` (`Module.flat_of_isLocalized_maximal`), and the local
ring of `M_g` at a prime `P` of `S_g` is the localization of `M` at the prime `P ∩ S` of `S`:
`(S_g)_P` is the localization of `S` at `P ∩ S`
(`IsLocalization.isLocalization_atPrime_localization_atPrime`), and a composite of two base changes
is a base change (`IsBaseChange.comp`). -/
@[stacks 05IL "flatness over the base", stacks 05IR "flatness over the base"]
theorem flat_localizedModule_away_of_forall_flat_atPrime {R S M : Type*} [CommRing R]
    [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (g : S)
    (H : ∀ q : PrimeSpectrum S, q ∈ PrimeSpectrum.basicOpen g →
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    Module.Flat R (LocalizedModule.Away g M) := by
  refine Module.flat_of_isLocalized_maximal (Localization.Away g) (LocalizedModule.Away g M)
    (fun P _ => LocalizedModule.AtPrime P (LocalizedModule.Away g M))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl _) fun P hP => ?_
  have hPprime : P.IsPrime := hP.isPrime
  have hqprime : (P.comap (algebraMap S (Localization.Away g))).IsPrime := inferInstance
  have hgq : g ∉ P.comap (algebraMap S (Localization.Away g)) := fun hg =>
    hP.ne_top (P.eq_top_of_isUnit_mem hg
      (IsLocalization.map_units (Localization.Away g) ⟨g, Submonoid.mem_powers g⟩))
  have hbc1 : IsBaseChange (Localization.Away g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) (Localization.Away g) _).mp
      inferInstance
  have hbc2 : IsBaseChange (Localization.AtPrime P)
      (LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule.Away g M)) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) _).mp inferInstance
  have hloc : IsLocalizedModule (P.comap (algebraMap S (Localization.Away g))).primeCompl
      ((LocalizedModule.mkLinearMap P.primeCompl
          (LocalizedModule.Away g M)).restrictScalars S ∘ₗ
        LocalizedModule.mkLinearMap (Submonoid.powers g) M) :=
    (isLocalizedModule_iff_isBaseChange _ (Localization.AtPrime P) _).mpr (hbc1.comp hbc2)
  have hflat := H ⟨P.comap (algebraMap S (Localization.Away g)), hqprime⟩
    ((PrimeSpectrum.mem_basicOpen g _).mpr hgq)
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso (P.comap (algebraMap S (Localization.Away g))).primeCompl
      ((LocalizedModule.mkLinearMap P.primeCompl
          (LocalizedModule.Away g M)).restrictScalars S ∘ₗ
        LocalizedModule.mkLinearMap (Submonoid.powers g) M)).restrictScalars R).symm


/-! ### Flatness spreads out over a polynomial ring with Noetherian base -/

/-- Let `R` be Noetherian, let `M` be a finitely presented module over `P = R[x_1, …, x_n]`, with
`R` and `M` in one universe, and let `𝔮` be a prime of `P` such that `M_𝔮` is flat over `R`. Then
there is a `g ∈ P`, `g ∉ 𝔮`, such that `M_g` is flat over `R`. -/
theorem exists_away_flat_mvPolynomial_aux
    {R M : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M]
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule.AtPrime q M)) :
    ∃ g ∉ q, Module.Flat R (LocalizedModule.Away g M) := by
  obtain ⟨g, hgq, hg⟩ := exists_basicOpen_forall_flat_localizedModule_mvPolynomial q hq
  exact ⟨g, hgq, flat_localizedModule_away_of_forall_flat_atPrime g hg⟩

/-- For `R` Noetherian and `M` a finitely presented module over `P = R[x_1, …, x_n]`, if `M_𝔮` is
flat over `R` then `M_g` is flat over `R` for some `g ∉ 𝔮`. -/
theorem exists_away_flat_of_flat_atPrime_mvPolynomial_of_isNoetherianRing
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M]
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule.AtPrime q M)) :
    ∃ g ∉ q, Module.Flat R (LocalizedModule.Away g M) := by
  classical
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M
  set e := f.quotKerEquivOfSurjective hf with he
  have : Module.FinitePresentation (MvPolynomial (Fin n) R)
      ((Fin k → MvPolynomial (Fin n) R) ⧸ LinearMap.ker f) :=
    Module.FinitePresentation.of_equiv e.symm
  have key : ∀ T : Submonoid (MvPolynomial (Fin n) R),
      LocalizedModule T ((Fin k → MvPolynomial (Fin n) R) ⧸ LinearMap.ker f) ≃ₗ[R]
        LocalizedModule T M := fun T => by
    have := IsLocalizedModule.of_linearEquiv_right T (LocalizedModule.mkLinearMap T M) e
    exact (IsLocalizedModule.iso T
      (LocalizedModule.mkLinearMap T M ∘ₗ e.toLinearMap)).restrictScalars R
  have hq' : Module.Flat R (LocalizedModule.AtPrime q
      ((Fin k → MvPolynomial (Fin n) R) ⧸ LinearMap.ker f)) :=
    Module.Flat.of_linearEquiv (key _)
  obtain ⟨g, hgq, hg⟩ := exists_away_flat_mvPolynomial_aux
    (M := (Fin k → MvPolynomial (Fin n) R) ⧸ LinearMap.ker f) q hq'
  refine ⟨g, hgq, ?_⟩
  exact Module.Flat.of_linearEquiv (key (Submonoid.powers g)).symm

/-- **Openness of the flat locus over a polynomial ring with Noetherian base.** For `R` Noetherian
and `M` a finitely presented module over `P = R[x_1, …, x_n]`, the set of primes `𝔮` of `P` at
which `M_𝔮` is flat over `R` is open in `Spec(P)`. -/
@[sga "3 VIB 13.1" "(i), special case"]
theorem isOpen_setOf_flat_localizedModule_atPrime_mvPolynomial
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M] :
    IsOpen {q : PrimeSpectrum (MvPolynomial (Fin n) R) |
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨g, hgq, hg⟩ :=
    exists_away_flat_of_flat_atPrime_mvPolynomial_of_isNoetherianRing q.asIdeal hq
  refine ⟨PrimeSpectrum.basicOpen g, fun q' hq' => ?_, (PrimeSpectrum.basicOpen g).isOpen,
    (PrimeSpectrum.mem_basicOpen g q).mpr hgq⟩
  have hle : Submonoid.powers g ≤ q'.asIdeal.primeCompl :=
    Submonoid.powers_le.mpr ((PrimeSpectrum.mem_basicOpen g q').mp hq')
  exact Module.Flat.of_isLocalizedModule_of_tower q'.asIdeal.primeCompl
    (IsLocalizedModule.liftOfLE (Submonoid.powers g) q'.asIdeal.primeCompl hle
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      (LocalizedModule.mkLinearMap q'.asIdeal.primeCompl M))


end Stacks.Flatness.OpenFlatLocus


end
