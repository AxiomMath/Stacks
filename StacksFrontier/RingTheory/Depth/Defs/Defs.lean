module

public import Mathlib.RingTheory.Regular.RegularSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth of a module along an ideal

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` an `R`-module. The `I`-depth of `M`
is `⊤` when `I • M = M`, and is otherwise the supremum in `ℕ∞ = {0, 1, 2, …, ∞}` of the
lengths of the `M`-regular sequences all of whose terms lie in `I`. Here a sequence
`f₁, …, f_r` is `M`-regular (`RingTheory.Sequence.IsRegular`) when `fᵢ` is a nonzerodivisor
on `M/(f₁, …, f_{i-1})M` for every `i` and `M/(f₁, …, f_r)M ≠ 0`; in particular the empty
sequence is `M`-regular exactly when `M ≠ 0`. For a local ring `(R, 𝔪)` the depth of `M` is
`Module.depth R (IsLocalRing.maximalIdeal R) M`. The module `M` is not assumed finite.

## Main definitions

* `Module.depth`: the `I`-depth `depth_I(M) : ℕ∞` of an `R`-module `M` along an ideal `I` of `R`.
* `Module.depthSup`: the supremum of the lengths of the `M`-regular sequences in `I`; it agrees
  with `Module.depth R I M` when `I • M ≠ M`, and is `0` for `M = 0`.

## Main results

* `Module.depth_eq_depth_of_linearEquiv`: the depth is invariant under a linear equivalence.
* `Module.depth_eq_top_of_subsingleton`: the depth of the zero module is `⊤`.
* `Module.le_depth_of_isRegular`: an `M`-regular sequence in `I` bounds the depth below by its
  length.
* `Module.depth_bot_eq_zero`: the `⊥`-depth of a nonzero module is `0`.

## References

* [StacksProject 00LI](https://stacks.math.columbia.edu/tag/00LI)

## Tags

depth, regular sequence, ideal
-/

@[expose] public section

open scoped Classical in
/-- The `I`-depth of an `R`-module `M`, for `I` an ideal of `R`: the supremum in
`ℕ∞ = {0, 1, 2, …, ∞}` of the lengths of the `M`-regular sequences with all terms in `I`,
except that the depth is `⊤` when `I • M = M` (which happens for instance when `M = 0`). -/
@[stacks 00LI,
  ega "0 16.4.5" "more general",
  ega "IV 5.7.1" "more general",
  ega "IV 6.10.3",
  sga "2 III 2.8" "special case",
  sga "2 IV 5.3",
  sga "2 XI 3.10"]
public noncomputable def Module.depth (R : Type*) [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] : ℕ∞ :=
  if I • (⊤ : Submodule R M) = ⊤ then ⊤
  else
    ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs}, (rs.length : ℕ∞)

/-- Depth along an ideal is invariant under a linear equivalence. -/
public theorem Module.depth_eq_depth_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : Module.depth R I M = Module.depth R I N := by
  have hset : {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} =
      {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular N rs} := by
    ext rs
    simp only [Set.mem_ofPred_eq, e.isRegular_congr rs]
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range]
  simp only [Module.depth, hset, htop]

/-- The depth of the zero module is `⊤`. -/
@[ega "0 16.4.5" "partial"]
public theorem Module.depth_eq_top_of_subsingleton {R : Type*} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Subsingleton M] : Module.depth R I M = ⊤ := by
  simp [Module.depth, Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule R M))]

open scoped Pointwise in
/-- A prefix `l.take j` of an `M`-regular sequence is `M`-regular. -/
public theorem isRegular_take {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (l : List R) (hlR : RingTheory.Sequence.IsRegular M l) (j : ℕ) :
    RingTheory.Sequence.IsRegular M (l.take j) := by
  rw [RingTheory.Sequence.isRegular_iff] at hlR ⊢
  obtain ⟨hwr, hne⟩ := hlR
  refine ⟨?_, fun he => hne (le_antisymm (he.le.trans (Submodule.smul_mono ?_ le_rfl)) le_top)⟩
  · rw [← List.take_append_drop j l, RingTheory.Sequence.isWeaklyRegular_append_iff] at hwr
    exact hwr.left
  · conv_rhs => rw [← List.take_append_drop j l]
    rw [Ideal.ofList_append]
    exact le_sup_left

/-- An `M`-regular sequence with all its terms in `I` bounds `depth_I(M)` below by its
length. -/
public theorem Module.le_depth_of_isRegular {R : Type*} [CommRing R] (I : Ideal R) {M : Type*}
    [AddCommGroup M] [Module R M] {rs : List R} (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : RingTheory.Sequence.IsRegular M rs) : (rs.length : ℕ∞) ≤ Module.depth R I M := by
  classical
  rw [Module.depth]
  split_ifs with h
  · exact le_top
  · exact le_biSup (fun rs : List R => ((rs.length : ℕ) : ℕ∞))
      (show rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} from
        ⟨hmem, hreg⟩)

/-- The `⊥`-depth of a nonzero module is `0`. -/
public theorem Module.depth_bot_eq_zero {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Nontrivial M] : Module.depth R ⊥ M = 0 := by
  rw [Module.depth, ite_eq_right (by simp : (⊥ : Ideal R) • (⊤ : Submodule R M) ≠ ⊤)]
  refine le_antisymm (iSup₂_le fun rs hrs => ?_) zero_le
  match rs, hrs with
  | [], _ => simp
  | a :: t, ⟨hmem, hreg⟩ =>
    have hr := ((RingTheory.Sequence.isWeaklyRegular_cons_iff M a t).mp
      hreg.toIsWeaklyRegular).1
    rw [Ideal.mem_bot.mp (hmem a (by simp))] at hr
    exact absurd hr.subsingleton (not_subsingleton M)

end

@[expose] public section

/-- The supremum (in `ℕ∞`) of the lengths of the `M`-regular sequences whose entries all lie
in the ideal `I`, for `M` a module over a commutative ring `R`. It agrees with
`Module.depth R I M` whenever `I • M ≠ M`; when `I • M = M` there is no `M`-regular sequence,
not even the empty one, and it is `0`. -/
@[ega "0 16.4.5" "partial", ega "IV 6.10.3"]
noncomputable def Module.depthSup (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup { n : ℕ∞ | ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧
      RingTheory.Sequence.IsRegular M rs }

/-- `Module.depthSup` written as an indexed supremum over the `M`-regular sequences in `I`
themselves, rather than as a supremum over the set of their lengths. -/
theorem Module.depthSup_eq_iSup {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Module.depthSup R I M =
      ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs},
        (rs.length : ℕ∞) := by
  refine le_antisymm (sSup_le ?_) (iSup₂_le fun rs hrs => le_sSup ⟨rs, rfl, hrs⟩)
  rintro n ⟨rs, rfl, hrs⟩
  exact le_iSup₂_of_le rs hrs le_rfl

/-- An `M`-regular sequence with all its terms in `I` bounds `Module.depthSup R I M` below by
its length. -/
theorem Module.le_depthSup {R : Type*} [CommRing R] {I : Ideal R} {M : Type*}
    [AddCommGroup M] [Module R M] {rs : List R} (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : RingTheory.Sequence.IsRegular M rs) :
    (rs.length : ℕ∞) ≤ Module.depthSup R I M :=
  le_sSup ⟨rs, rfl, hmem, hreg⟩

end
