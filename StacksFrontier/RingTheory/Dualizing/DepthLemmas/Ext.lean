module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.Finiteness.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.ShortExact
import all StacksFrontier.RingTheory.Depth.ShortExact

/-!
# Depth read off the vanishing of `Ext`

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module. Rees' theorem says
that `I` contains an `M`-regular sequence of length `n` exactly when `Ext^i_R(R/I, M)` vanishes
for every `i < n`. Translated into the invariant `Module.depth` of Stacks 00LI — which sets the
depth to `⊤` on the degenerate branch `I • M = M` rather than leaving it undefined — this reads
`n ≤ depth_I(M) ↔ ∀ i < n, Ext^i_R(R/I, M) = 0`, and hence

`depth_I(M) = inf { i | Ext^i_R(R/I, M) ≠ 0 }`,

the infimum being taken in `ℕ∞`, so that it is `⊤` when every such `Ext` vanishes.

## Main results

* `Module.natCast_le_depth_iff_subsingleton_ext` — Rees' theorem for `Module.depth`, the
  degenerate branch included.
* `ModuleCat.subsingleton_ext_of_lt_ideal_depth` — `Ext^i_R(N, M)` vanishes below the `I`-depth
  of `M` for every finite `N` annihilated by a power of `I`.
* `Module.depth_eq_sInf_nontrivial_ext` — the `I`-depth is the least degree in which `Ext` from
  `R ⧸ I` is nontrivial.

## Implementation notes

The degenerate branch is part of the statement rather than a case to be excluded: when
`I • M = M` and `M` is finite, Nakayama produces `r ∈ I` acting as the identity on `M` while
`1 - r` annihilates `R ⧸ I`, so every `Ext^i_R(R/I, M)` vanishes and both sides of Rees'
criterion hold for every `n`.

The module `M` and the ring `R` live in independent universes, with `R` small relative to that
of `M`. The quotient `R ⧸ I` is therefore replaced by its canonical small model
`Shrink (R ⧸ I)`, which has the same `Ext` groups because it is linearly equivalent to it; this
is universe bookkeeping only.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [Stacks Project, Tag 00LW](https://stacks.math.columbia.edu/tag/00LW)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public section

open Stacks.Depth.ShortExactInequalities

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Ideal RingTheory.Sequence

universe u v

variable {R : Type u} [CommRing R]

/-- Whether an ideal `I` satisfies `I • M = M` depends on `M` only up to linear equivalence. -/
theorem LinearEquiv.smul_top_eq_top_iff {M : Type*} {N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (I : Ideal R) :
    I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
  rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_smul'', Submodule.map_top,
    LinearEquiv.range]

variable {M : Type v} [AddCommGroup M] [Module R M] {I : Ideal R}

/-- On the degenerate branch `I • M = M` of a finite module every `Ext^i_R(R/I, M)` vanishes:
Nakayama produces `r ∈ I` acting as the identity on `M`, and `1 - r` annihilates `R ⧸ I`, so
the identity of `Ext^i_R(R/I, M)` is the zero map. -/
theorem Module.subsingleton_ext_quotient_of_smul_top_eq_top [Small.{v} R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (htop : I • (⊤ : Submodule R M) = ⊤) (i : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) (ModuleCat.of R M) i) := by
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
    Module.Finite.fg_top htop.ge
  have hann : (1 - r) ∈ Module.annihilator R (Shrink.{v} (R ⧸ I)) := by
    rw [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq, annihilator_quotient]
    simpa only [neg_sub] using (Ideal.neg_mem_iff I).mpr hr1
  have hid : ((1 - r) • 𝟙 (ModuleCat.of R M) : ModuleCat.of R M ⟶ ModuleCat.of R M)
      = 𝟙 (ModuleCat.of R M) := by
    ext m
    simpa [sub_smul] using hr0 m Submodule.mem_top
  have hz := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
    (M := ModuleCat.of R M) (N := ModuleCat.of R (Shrink.{v} (R ⧸ I))) hann i
  rw [hid] at hz
  rw [← AddCommGrpCat.isZero_of_iff_subsingleton, IsZero.iff_id_eq_zero, ← hz]
  ext x
  simp

/-- **Rees' theorem for `Module.depth`.** For a finite module `M` over a Noetherian ring `R` and
an ideal `I ⊆ R`, one has `n ≤ depth_I(M)` if and only if `Ext^i_R(R/I, M) = 0` for every
`i < n`. The degenerate branch `I • M = M` is included: there both sides hold for every `n`. -/
@[sga "2 III 2.8" "prof M = inf{i"]
theorem Module.natCast_le_depth_iff_subsingleton_ext [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ Module.depth R I M ↔
      ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
        (ModuleCat.of R M) i) := by
  by_cases htop : I • (⊤ : Submodule R M) = ⊤
  · simp only [Module.depth, ite_eq_left_of_eq_true _ _ (eq_true htop), le_top, true_iff]
    exact fun i _ => Module.subsingleton_ext_quotient_of_smul_top_eq_top I M htop i
  · rw [natCast_le_depth_iff_exists_isRegular htop]
    exact (ModuleCat.exists_isRegular_tfae I n (ModuleCat.of R M)
      (lt_top_iff_ne_top.mpr htop)).out 4 2

/-- Every `Ext^i_R(R/I, M)` with `i` below the `I`-depth of `M` vanishes. -/
@[sga "2 IV 5.3" "Ext^i_A(k, M = k"]
theorem Module.subsingleton_ext_quotient_of_lt_depth [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] {i : ℕ}
    (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) (ModuleCat.of R M) i) :=
  (Module.natCast_le_depth_iff_subsingleton_ext I M (i + 1)).mp
    (by exact_mod_cast Order.add_one_le_of_lt hi) i (Nat.lt_succ_self i)

/-- `Ext^i_R(N, M)` vanishes below the `I`-depth of `M` for **every** finite module `N`
annihilated by a power of `I`, not just for `N = R ⧸ I`: a power of `I` annihilating `N` forces
the support of `N` into `V(I)`, and Rees' theorem turns the vanishing of `Ext^j_R(R/I, M)` below
the depth into an `M`-regular sequence in `I` long enough to kill `Ext^i_R(N, M)`. -/
@[stacks 0AVZ "Ext vanishing below depth for modules annihilated by an ideal power",
  ega "0 16.4.4" "Ext^i(k",
  sga "2 III 2.2" "Clause (a), special case",
  sga "2 III 2.4" "(4)⇒(2)",
  sga "2 III 2.8" "Ext^i(k",
  sga "2 IV 5.3" "Ext^i_A(k, special case"]
theorem ModuleCat.subsingleton_ext_of_lt_ideal_depth [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) {k : ℕ} (hk : I ^ k ≤ Module.annihilator R N) {i : ℕ}
    (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (Ext N M i) := by
  have hsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
    exact fun x hx => Ideal.mem_radical_iff.mpr ⟨k, hk (Ideal.pow_mem_pow hx k)⟩
  have hlt := lt_top_iff_ne_top.mpr hIM
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    ((ModuleCat.exists_isRegular_tfae I (i + 1) M hlt).out 2 4).mp fun j hj =>
      Module.subsingleton_ext_quotient_of_lt_depth I (M : Type v)
        ((Nat.cast_le.mpr (Nat.lt_succ_iff.mp hj)).trans_lt hi)
  exact ModuleCat.subsingleton_ext_of_exists_isRegular I N hsupp M hlt rs hmem hreg i (by omega)


/-- The `I`-depth of a finite module over a Noetherian ring is the least degree in which `Ext`
from `R ⧸ I` is nontrivial; if every such `Ext` vanishes, both sides are `⊤`. -/
@[ega "0 16.4.4" "depth = least n Ext≠0",
  sga "2 III 3.4" "(1) <=> (3)",
  sga "2 III 2.2" "(b), N = A/I", sga "2 III 2.8" "Ext characterization"]
theorem Module.depth_eq_sInf_nontrivial_ext (R : Type u) [CommRing R] [IsNoetherianRing R]
    [Small.{v} R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Module.depth R I M =
      sInf {n : ℕ∞ | ∃ i : ℕ, n = (i : ℕ∞) ∧
        Nontrivial (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) (ModuleCat.of R M) i)} := by
  have hdepth_le : Module.depth R I M ≤
      sInf {n : ℕ∞ | ∃ i : ℕ, n = (i : ℕ∞) ∧
        Nontrivial (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) (ModuleCat.of R M) i)} := by
    refine le_sInf ?_
    rintro x ⟨i, rfl, hi⟩
    exact not_lt.mp fun hcon => (not_nontrivial_iff_subsingleton.mpr
      (Module.subsingleton_ext_quotient_of_lt_depth I M hcon)) hi
  rcases eq_or_ne (Module.depth R I M) ⊤ with htop | htop
  · exact htop.trans (top_unique (htop.symm.trans_le hdepth_le)).symm
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp htop
  have hnt : Nontrivial
      (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) (ModuleCat.of R M) d) := by
    by_contra hzero
    have hsub := not_nontrivial_iff_subsingleton.mp hzero
    have hvan := (Module.natCast_le_depth_iff_subsingleton_ext I M (d + 1)).mpr fun i hi => by
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hid
      · exact hsub
      · exact (Module.natCast_le_depth_iff_subsingleton_ext I M d).mp hd.le i hid
    rw [← hd, Nat.cast_le] at hvan
    omega
  refine le_antisymm hdepth_le ?_
  rw [← hd]
  exact sInf_le ⟨d, rfl, hnt⟩

end
