module


public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Tactic.Monotonicity.Lemmas
import StacksFrontier.RingTheory.Depth.Dimension
import StacksFrontier.RingTheory.Depth.ShortExact
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.MinimalPrimes
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Depth.Nakayama

@[expose] public section

universe u v

/-!
# Depth is computed by weakly regular sequences

Proof of `Module.depth_eq_iSup_isWeaklyRegular_length` (Stacks 0AUI): for a finite module `M`
over a commutative ring `R` and an ideal `I ⊆ R`, the `I`-depth of `M` is the supremum of the
lengths of the sequences `f₁, …, f_r ∈ I` such that `fᵢ` is a nonzerodivisor on
`M/(f₁, …, f_{i-1})M`, that is, of the weakly `M`-regular sequences contained in `I`.

`Module.depth R I M` is defined by a case distinction on whether `I • M = M`, and in the second
case as the supremum of the lengths of the `M`-regular sequences in `I` — those weakly regular
sequences `f₁, …, f_r` which moreover satisfy `M/(f₁, …, f_r)M ≠ 0`. Both the case distinction
and the nonvanishing requirement disappear at once, for the two reasons the source gives. If
`I • M ≠ M`, then `(f₁, …, f_r)M ≤ I • M ≠ M` for every sequence drawn from `I`, so a weakly
`M`-regular sequence in `I` is automatically `M`-regular and the two index sets coincide. If
`I • M = M`, then Nakayama's lemma produces an `a ∈ I` acting on `M` as the identity, and then
`a` is a nonzerodivisor on `M` while `M/aM = 0`, so `a` followed by *any* sequence whatsoever is
weakly `M`-regular; there are weakly regular sequences in `I` of every length and the supremum
is `⊤`, the value the definition assigns in this case.

## Main results

* `Stacks.Depth.WeaklyRegularLength.solution`: the `I`-depth of a finite module `M` is the
  supremum of the lengths of the weakly `M`-regular sequences in `I`.

## Implementation notes

The `I • M = M` branch uses the constant sequences `a, a, …, a` rather than the source's
`f, 0, 0, …`; the two work for the same reason, namely that every term after the first acts on
the zero module `M/aM`, where every element is a nonzerodivisor. That reason is what
`isWeaklyRegular_cons_of_smul_eq_self` isolates, so the choice of tail is immaterial.

Nakayama's lemma is used in its Mathlib form
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` (Stacks 00DV (1)), which
returns `r` with `r - 1 ∈ I` annihilating `N`; the element acting as the identity is `1 - r`.
That corollary is stated here for an arbitrary finitely generated submodule `N ≤ I • N`, the
form its proof gives, and applied to `N = ⊤`.

## References

* [StacksProject 0AUI](https://stacks.math.columbia.edu/tag/0AUI)
-/

@[expose] public section

namespace Stacks.Depth.WeaklyRegularLength

open Pointwise RingTheory.Sequence

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- If `I • M ≠ M`, then a weakly `M`-regular sequence with all terms in `I` is `M`-regular:
the sequence generates an ideal contained in `I`, so `M/(f₁, …, f_r)M ≠ 0` comes for free. -/
private theorem isRegular_iff_isWeaklyRegular_of_smul_top_ne_top {I : Ideal R}
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) {rs : List R} (hmem : ∀ r ∈ rs, r ∈ I) :
    IsRegular M rs ↔ IsWeaklyRegular M rs := by
  rw [isRegular_iff]
  refine and_iff_left fun hc => hI (le_antisymm le_top ?_)
  calc (⊤ : Submodule R M) = Ideal.ofList rs • ⊤ := hc
    _ ≤ I • ⊤ := Submodule.smul_mono_left (Ideal.span_le.mpr hmem)

/-- Every sequence is weakly regular on the zero module: each of the quotients
`M/(f₁, …, f_{i-1})M` is zero, and every element is a nonzerodivisor on the zero module. -/
private theorem isWeaklyRegular_of_subsingleton [Subsingleton M] (rs : List R) :
    IsWeaklyRegular M rs :=
  (isWeaklyRegular_iff_Fin M rs).mpr fun _ _ _ _ => Subsingleton.elim _ _

/-- An element `a` acting on `M` as the identity may be prefixed to an arbitrary sequence to
give a weakly `M`-regular one: `a` is a nonzerodivisor on `M`, and `M/aM = 0` so the rest of
the sequence is unconstrained. -/
private theorem isWeaklyRegular_cons_of_smul_eq_self {a : R} (ha : ∀ m : M, a • m = m)
    (rs : List R) : IsWeaklyRegular M (a :: rs) := by
  have hreg : IsSMulRegular M a := fun x y hxy => by simpa only [ha] using hxy
  have : Subsingleton (QuotSMulTop a M) :=
    Submodule.Quotient.subsingleton_iff.mpr <| le_antisymm le_top fun x _ =>
      ha x ▸ Submodule.smul_mem_pointwise_smul x a ⊤ Submodule.mem_top
  exact .cons hreg (isWeaklyRegular_of_subsingleton _)

/-- Nakayama's lemma in the form used here: if `N` is a finitely generated submodule with
`N ≤ I • N`, then some element of `I` acts on `N` as the identity. -/
private theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul (I : Ideal R) (N : Submodule R M)
    (hn : N.FG) (hin : N ≤ I • N) : ∃ a ∈ I, ∀ n ∈ N, a • n = n := by
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin
  refine ⟨1 - r, by simpa only [neg_sub] using (Ideal.neg_mem_iff I).mpr hr, fun n hn => ?_⟩
  rw [sub_smul, one_smul, hrN n hn, sub_zero]

/-- If `I • M = M` for a finite `R`-module `M`, then `I` contains weakly `M`-regular sequences
of every length, so the supremum of their lengths is `⊤`. -/
private theorem iSup_isWeaklyRegular_length_eq_top_of_smul_top_eq_top [Module.Finite R M]
    (I : Ideal R) (h : I • (⊤ : Submodule R M) = ⊤) :
    ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs}, (rs.length : ℕ∞) = ⊤ := by
  obtain ⟨a, haI, ha⟩ :=
    exists_mem_and_smul_eq_self_of_fg_of_le_smul I ⊤ Module.Finite.fg_top h.ge
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  have hmem : List.replicate (n + 1) a ∈
      {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs} := by
    refine ⟨fun x hx => List.eq_of_mem_replicate hx ▸ haI, ?_⟩
    rw [List.replicate_succ]
    exact isWeaklyRegular_cons_of_smul_eq_self (fun m => ha m Submodule.mem_top) _
  calc (n : ℕ∞) ≤ ((List.replicate (n + 1) a).length : ℕ∞) := by simp
    _ ≤ _ := le_iSup₂ (f := fun rs (_ : rs ∈ _) => (rs.length : ℕ∞)) _ hmem

/-- **Stacks 0AUI.** The `I`-depth of a finite `R`-module `M` is the supremum of the lengths of
the weakly `M`-regular sequences in `I`. -/
public theorem solution (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.depth R I M =
      ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsWeaklyRegular M rs},
        (rs.length : ℕ∞) := by
  rw [Module.depth]
  split_ifs with h
  · exact (iSup_isWeaklyRegular_length_eq_top_of_smul_top_eq_top I h).symm
  · exact congrArg (fun S : Set (List R) => ⨆ rs ∈ S, (rs.length : ℕ∞))
      (Set.ext fun _ => and_congr_right (isRegular_iff_isWeaklyRegular_of_smul_top_ne_top h))

end Stacks.Depth.WeaklyRegularLength

end

/-!
# Depth is computed by sequences of successive nonzerodivisors

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` a finite `R`-module. The `I`-depth of
`M` is defined (`Module.depth`) by a case distinction: it is `⊤` when `I • M = M`, and is
otherwise the supremum of the lengths of the `M`-regular sequences with all terms in `I`, a
sequence being `M`-regular when each `fᵢ` is a nonzerodivisor on `M/(f₁, …, f_{i-1})M` *and*
`M/(f₁, …, f_r)M ≠ 0`. This file records that the case distinction and the nonvanishing
requirement may both be dropped at once: `depth_I(M)` is the supremum of the lengths of the
sequences `f₁, …, f_r ∈ I` such that `fᵢ` is a nonzerodivisor on `M/(f₁, …, f_{i-1})M`, which
is Mathlib's `RingTheory.Sequence.IsWeaklyRegular M [f₁, …, f_r]`.

The two supremums agree for the following reason. If `I • M ≠ M`, then a sequence in `I`
which is weakly `M`-regular satisfies `(f₁, …, f_r) • M ≤ I • M ≠ M`, hence is `M`-regular,
so the two index sets coincide. If `I • M = M`, then finiteness of `M` produces `f ∈ I`
acting on `M` as `id` (Nakayama, tag 00DV), and then `f, 0, 0, …` is weakly `M`-regular of
every length, so the supremum is `⊤` as well.

## Main results

* `Module.depth_eq_iSup_isWeaklyRegular_length`: `depth_I(M)` is the supremum of the lengths
  of the weakly `M`-regular sequences contained in `I`.

## Implementation notes

Faithfulness to [StackProject 0AUI]:

1. No dead hypothesis: `Module.Finite R M` is used by the conclusion, not decoration — for
   `R = ℤ`, `I = (2)` and `M = ℚ/ℤ` one has `I • M = M`, so `depth_I(M) = ⊤`, while no
   element of `(2)` is a nonzerodivisor on `ℚ/ℤ` and the right-hand supremum is `0`.
2. The scalars are the source's: the sequences are drawn from the ideal `I` of `R` itself and
   `IsWeaklyRegular M` is regularity of the `R`-module `M`, the quotients `M/(f₁, …, f_i)M`
   being taken over `R`; no localisation or base change intervenes.
3. Both sides are pinned, not merely compared: the left-hand side is the value of
   `Module.depth R I M` (tag 00LI) and the right-hand side is the supremum over the
   explicitly described set of lists, so the statement is the computation of the depth and
   not the existence of long weakly regular sequences.
4. Not degenerate: for `R = ℤ`, `I = (p)` and `M = ℤ` both sides are `1`, and for `I = R`
   both sides are `⊤`; so neither the hypothesis nor the equality is vacuous.

The source phrases the right-hand side as "sequences `f₁, …, f_r ∈ I` such that `fᵢ` is a
nonzerodivisor on `M/(f₁, …, f_{i-1})M`"; this is exactly Mathlib's
`RingTheory.Sequence.IsWeaklyRegular`, whose spelling is used instead. Lengths are compared in
`ℕ∞`, matching the source's supremum in `{0, 1, 2, …, ∞}` and the type of `Module.depth`. The
set of lists is described in the same form as in the definition of `Module.depth`, so that the
two supremums differ only in `IsRegular` versus `IsWeaklyRegular`.

## References

* [StackProject 0AUI](https://stacks.math.columbia.edu/tag/0AUI)

## Tags

depth, regular sequence, nonzerodivisor
-/

namespace Module

/-- The `I`-depth of a finite `R`-module `M` is the supremum of the lengths of the sequences
`f₁, …, f_r ∈ I` such that `fᵢ` is a nonzerodivisor on `M/(f₁, …, f_{i-1})M`; that is, the
nonvanishing requirement `M/(f₁, …, f_r)M ≠ 0` on regular sequences and the case distinction
`I • M = M` in the definition of the depth may be dropped together. -/
@[stacks 0AUI, ega "0 16.4.5" "more general"]
public theorem depth_eq_iSup_isWeaklyRegular_length (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth R I M =
      ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsWeaklyRegular M rs},
        (rs.length : ℕ∞) :=
  Stacks.Depth.WeaklyRegularLength.solution R I M

end Module

/-!
# Depth drops by one modulo a nonzerodivisor

Proof of `Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` (Stacks 090R):
for `R` a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module,

* `depth_I(M/xM) + 1 = depth_I(M)` for every `x ∈ I` that is a nonzerodivisor on `M`, and
* if `I • M ≠ M`, every `M`-regular sequence with all terms in `I` is a prefix of an
  `M`-regular sequence with all terms in `I` of length exactly `depth_I(M)`.

The first assertion is two inequalities, both read off the description of the depth as the
supremum of the lengths of the weakly regular sequences in `I` (Stacks 0AUI). Prepending `x` to a
weakly `M/xM`-regular sequence in `I` gives a weakly `M`-regular sequence in `I` one longer
(`RingTheory.Sequence.IsWeaklyRegular.cons`), so `depth_I(M/xM) ≤ depth_I(M) - 1`; the
one-term sequence `x` gives `1 ≤ depth_I(M)`, and the two together are
`depth_I(M/xM) + 1 ≤ depth_I(M)`. Conversely the short exact sequence
`0 → M →(x·) M → M/xM → 0` and the estimate
`min {depth_I(M), depth_I(M) - 1} ≤ depth_I(M/xM)` of Stacks 00LX give
`depth_I(M) - 1 ≤ depth_I(M/xM)`, which is `depth_I(M) ≤ depth_I(M/xM) + 1` because the
subtraction of `ℕ∞` is truncated.

The second assertion follows by induction along the given sequence: for `rs = x :: t` the
sequence `t` is `M/xM`-regular with all terms in `I` and `I • (M/xM) ≠ M/xM`, so the induction
hypothesis extends it inside `M/xM` to length `depth_I(M/xM)`, and prepending `x` extends `rs`
to length `depth_I(M/xM) + 1 = depth_I(M)`. The base case `rs = []` is the statement that
`depth_I(M)` is attained, proved by induction on its value, which is a natural number: a nonzero
depth produces a nonzerodivisor `x ∈ I` as the first term of a weakly regular sequence, and
`M/xM` has depth one less.

## Main results

* `Stacks.Depth.ModNonzerodivisor.solution`: dividing by a nonzerodivisor in `I` drops the
  `I`-depth by one, and, when `I • M ≠ M`, every `M`-regular sequence in `I` extends to one of
  length `depth_I(M)`.

## Implementation notes

Both assertions are proved through the weakly regular sequences of Stacks 0AUI rather than
through the regular sequences of the definition of `Module.depth` (Stacks 00LI): the supremum
over weakly regular sequences has no case distinction on `I • M = M`, so the first assertion
needs no separate treatment of the degenerate case, where both sides are `⊤`. Stacks 0AUI
enters only through its two directions, `length_le_depth_of_isWeaklyRegular` and
`depth_le_of_forall_isWeaklyRegular_length_le`. In the second assertion regularity is carried
along the induction instead, through `RingTheory.Sequence.isRegular_cons_iff`.

The finiteness of `depth_I(M)` under `I • M ≠ M` is the source's remark that the process of
extending a regular sequence stops, and it is proved here as `depth_ne_top` by the source's
argument: `I` and `Ann(M)` generate a proper ideal, so both are contained in a maximal ideal
`𝔭`, the localization `M_𝔭` is nonzero, and depth does not drop under that
localization, whence
`depth_I(M) ≤ depth_{𝔭R_𝔭}(M_𝔭) ≤ dim Supp(M_𝔭) ≤ dim(R_𝔭) < ∞`
by Stacks 00LK and Krull's height theorem. The prime is taken maximal rather than minimal over
`I + Ann(M)` because only membership in the support and above `I` is used.

The inductions of the second assertion quantify over the module, which changes along them, so
they are run at a fixed universe for the module and instantiated once, at the end.

## References

* [StacksProject 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public section

namespace Stacks.Depth.ModNonzerodivisor

open Ideal IsLocalRing Module Pointwise RingTheory.Sequence



section Depth

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R)
  [Module.Finite R M]

/-- A weakly `M`-regular sequence with all terms in `I` has length at most `depth_I(M)`. -/
public theorem length_le_depth_of_isWeaklyRegular {rs : List R}
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs) : (rs.length : ℕ∞) ≤ depth R I M :=
  Module.depth_eq_iSup_isWeaklyRegular_length R I M ▸
    le_biSup (fun l : List R => (l.length : ℕ∞)) (show rs ∈ _ from ⟨hmem, hreg⟩)

/-- Conversely, a bound on the lengths of all weakly `M`-regular sequences in `I` bounds
`depth_I(M)`, which is their supremum. -/
public theorem depth_le_of_forall_isWeaklyRegular_length_le {d : ℕ∞}
    (h : ∀ rs : List R, (∀ r ∈ rs, r ∈ I) → IsWeaklyRegular M rs → (rs.length : ℕ∞) ≤ d) :
    depth R I M ≤ d :=
  Module.depth_eq_iSup_isWeaklyRegular_length R I M ▸ iSup₂_le fun rs hrs => h rs hrs.1 hrs.2

/-- A module of nonzero `I`-depth admits a nonzerodivisor in `I`: the first term of a weakly
regular sequence in `I` of positive length. -/
public theorem exists_mem_isSMulRegular_of_depth_ne_zero (h : depth R I M ≠ 0) :
    ∃ x ∈ I, IsSMulRegular M x := by
  by_contra hc
  refine h (le_zero_iff.mp (depth_le_of_forall_isWeaklyRegular_length_le I ?_))
  rintro (_ | ⟨a, t⟩) hmem hreg
  · simp
  · exact absurd ((isWeaklyRegular_cons_iff M a t).mp hreg).1 fun hx =>
      hc ⟨a, hmem a (List.mem_cons_self ..), hx⟩

omit [Module.Finite R M] in
/-- A module with `I • M ≠ M` is nonzero. -/
private theorem nontrivial_of_smul_top_ne_top (h : I • (⊤ : Submodule R M) ≠ ⊤) :
    Nontrivial M :=
  (subsingleton_or_nontrivial M).resolve_left fun _ => h (Subsingleton.elim _ _)

omit [Module.Finite R M] in
/-- For `x ∈ I`, the quotient `M/xM` absorbs `I` exactly when `M` does: `M/xM` is the quotient by
a submodule of `IM`. -/
private theorem smul_top_quotSMulTop_eq_top_iff {x : R} (hx : x ∈ I) :
    I • (⊤ : Submodule R (QuotSMulTop x M)) = ⊤ ↔ I • (⊤ : Submodule R M) = ⊤ := by
  have hxle : x • (⊤ : Submodule R M) ≤ I • ⊤ := by
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left (by simpa using hx)
  have hmap : Submodule.map (x • (⊤ : Submodule R M)).mkQ (I • ⊤)
      = I • (⊤ : Submodule R (QuotSMulTop x M)) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [← hmap, LinearMap.map_eq_top_iff (Submodule.range_mkQ _), Submodule.ker_mkQ,
    sup_eq_left.mpr hxle]

end Depth

section Finiteness

variable {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
  [Module.Finite R M]

/-- The depth of a nonzero finite module over a Noetherian local ring is finite: it is at most the
dimension of the support (Stacks 00LK), hence at most the Krull dimension of the ring, which is
finite by Krull's height theorem. -/
private theorem depth_maximalIdeal_ne_top [IsLocalRing R] [Nontrivial M] :
    depth R (maximalIdeal R) M ≠ ⊤ := fun h =>
  ringKrullDim_ne_top (R := R) <| top_le_iff.mp <|
    calc (⊤ : WithBot ℕ∞) = ((depth R (maximalIdeal R) M : ℕ∞) : WithBot ℕ∞) := by simp [h]
      _ ≤ supportDim R M := Module.depth_le_supportDim R _ M fun hm =>
          Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
            (maximalIdeal_le_jacobson _) hm.symm
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- If `I • M ≠ M` then `I` and the annihilator of `M` generate a proper ideal: otherwise
`1 = a + b` with `a ∈ I` and `bM = 0` exhibits every element of `M` in `IM`. -/
private theorem sup_annihilator_ne_top {I : Ideal R} (h : I • (⊤ : Submodule R M) ≠ ⊤) :
    I ⊔ Module.annihilator R M ≠ ⊤ := by
  intro htop
  refine h (top_le_iff.mp fun m _ => ?_)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop.ge (Submodule.mem_top (x := (1 : R))))
  have hm : a • m = m := by
    rw [← add_zero (a • m), ← Module.mem_annihilator.mp hb m, ← add_smul, hab, one_smul]
  exact hm ▸ Submodule.smul_mem_smul ha Submodule.mem_top

omit [IsNoetherianRing R] in
/-- Localizing at a prime `𝔭 ⊇ I` does not decrease the depth: a weakly `M`-regular sequence in
`I` localizes to a weakly `M_𝔭`-regular sequence in `𝔭R_𝔭`. -/
private theorem depth_le_depth_localizedModule {I p : Ideal R} [p.IsPrime] (hIp : I ≤ p) :
    depth R I M ≤ depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
      (LocalizedModule p.primeCompl M) := by
  refine depth_le_of_forall_isWeaklyRegular_length_le I fun rs hmem hreg => ?_
  have hmem' : ∀ r ∈ rs.map (algebraMap R (Localization.AtPrime p)),
      r ∈ maximalIdeal (Localization.AtPrime p) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr (hIp (hmem a ha))
  simpa using length_le_depth_of_isWeaklyRegular _ hmem'
    (IsWeaklyRegular.of_isLocalizedModule _ p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) hreg)

omit [IsNoetherianRing R] in
/-- Localizing a local ring at its maximal ideal does not decrease the depth of a module along
the maximal ideal: `depth_𝔪(M) ≤ depth_{𝔪R_𝔪}(M_𝔪)`. This is the case `I = 𝔭 = 𝔪` of the
localization inequality above. -/
public theorem depth_maximalIdeal_le_depth_localizedModule_maximalIdeal [IsLocalRing R] :
    depth R (maximalIdeal R) M ≤
      depth (Localization.AtPrime (maximalIdeal R))
        (maximalIdeal (Localization.AtPrime (maximalIdeal R)))
        (LocalizedModule (maximalIdeal R).primeCompl M) :=
  depth_le_depth_localizedModule le_rfl

/-- The `I`-depth of a finite module `M` with `I • M ≠ M` is finite: a maximal ideal `𝔭` above
`I` and `Ann(M)` puts `M_𝔭` in the support, and the depth of `M_𝔭` is finite. -/
private theorem depth_ne_top (I : Ideal R) (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth R I M ≠ ⊤ := by
  obtain ⟨p, hpmax, hple⟩ := Ideal.exists_le_maximal _ (sup_annihilator_ne_top hIM)
  have : p.IsPrime := hpmax.isPrime
  have : Nontrivial (LocalizedModule p.primeCompl M) :=
    Module.mem_support_iff_of_finite (p := ⟨p, hpmax.isPrime⟩).mpr (le_sup_right.trans hple)
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
  exact fun h => depth_maximalIdeal_ne_top
    (top_le_iff.mp (h ▸ depth_le_depth_localizedModule (le_sup_left.trans hple)))

end Finiteness

section PartOne

variable {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
  [Module.Finite R M] (I : Ideal R) {x : R}

omit [IsNoetherianRing R] in
/-- The depth drops by at least one: prepending a nonzerodivisor `x ∈ I` to a weakly
`M/xM`-regular sequence in `I` gives a weakly `M`-regular sequence in `I` one longer, and `x`
alone already shows `1 ≤ depth_I(M)`. -/
private theorem depth_quotSMulTop_add_one_le (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    depth R I (QuotSMulTop x M) + 1 ≤ depth R I M := by
  have h1 : (1 : ℕ∞) ≤ depth R I M := by
    simpa using length_le_depth_of_isWeaklyRegular I (rs := [x]) (by simpa using hx)
      ((isWeaklyRegular_singleton_iff M x).mpr hreg)
  have h2 : depth R I (QuotSMulTop x M) ≤ depth R I M - 1 :=
    depth_le_of_forall_isWeaklyRegular_length_le I fun rs hmem hrs =>
      ENat.le_sub_of_add_le_right ENat.one_ne_top <| by
        simpa using length_le_depth_of_isWeaklyRegular I (rs := x :: rs)
          (List.forall_mem_cons.mpr ⟨hx, hmem⟩) (IsWeaklyRegular.cons hreg hrs)
  calc depth R I (QuotSMulTop x M) + 1 ≤ depth R I M - 1 + 1 := add_le_add h2 le_rfl
    _ = depth R I M := tsub_add_cancel_of_le h1

/-- The depth drops by at most one: the short exact sequence `0 → M →(x·) M → M/xM → 0` and
Stacks 00LX. -/
private theorem depth_le_depth_quotSMulTop_add_one (hreg : IsSMulRegular M x) :
    depth R I M ≤ depth R I (QuotSMulTop x M) + 1 := by
  have h := (Module.min_depth_le_depth_of_exact I (LinearMap.exact_lsmul_mkQ_smul_top M x) hreg
    (Submodule.mkQ_surjective _)).2.1
  rw [min_eq_right tsub_le_self] at h
  exact tsub_le_iff_right.mp h

/-- **Stacks 090R(1).** Dividing a finite module by a nonzerodivisor in `I` drops the `I`-depth
by exactly one. -/
private theorem depth_quotSMulTop_succ_eq (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    depth R I (QuotSMulTop x M) + 1 = depth R I M :=
  le_antisymm (depth_quotSMulTop_add_one_le I hx hreg) (depth_le_depth_quotSMulTop_add_one I hreg)

end PartOne

section PartTwo

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)

/-- The `I`-depth of a finite module `M` with `I • M ≠ M` is attained by an `M`-regular sequence
with all terms in `I`. The module varies along the induction on the depth, so it is quantified
inside. -/
private theorem exists_isRegular_length_eq (k : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M], I • (⊤ : Submodule R M) ≠ ⊤ → depth R I M = (k : ℕ∞) →
    ∃ ss : List R, (∀ s ∈ ss, s ∈ I) ∧ IsRegular M ss ∧ ss.length = k := by
  induction k with
  | zero =>
    intro M _ _ _ hIM _
    have := nontrivial_of_smul_top_ne_top I hIM
    exact ⟨[], by simp, IsRegular.nil R M, rfl⟩
  | succ k ih =>
    intro M _ _ _ hIM hd
    obtain ⟨x, hxI, hxreg⟩ := exists_mem_isSMulRegular_of_depth_ne_zero I (by rw [hd]; simp)
    have hd' : depth R I (QuotSMulTop x M) + 1 = (k : ℕ∞) + 1 := by
      rw [depth_quotSMulTop_succ_eq I hxI hxreg, hd, Nat.cast_add, Nat.cast_one]
    obtain ⟨ss, hmem, hreg, hlen⟩ :=
      ih (QuotSMulTop x M) ((smul_top_quotSMulTop_eq_top_iff I hxI).not.mpr hIM)
        (WithTop.add_right_cancel ENat.one_ne_top hd')
    exact ⟨x :: ss, List.forall_mem_cons.mpr ⟨hxI, hmem⟩, IsRegular.cons hxreg hreg,
      by simp [hlen]⟩

/-- **Stacks 090R(2).** An `M`-regular sequence with all terms in `I` extends to one of length
`depth_I(M)`, by induction along the given sequence. -/
private theorem exists_isRegular_append : ∀ (rs : List R) (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M], I • (⊤ : Submodule R M) ≠ ⊤ → (∀ r ∈ rs, r ∈ I) →
    IsRegular M rs → ∃ ss : List R, (∀ s ∈ ss, s ∈ I) ∧ IsRegular M (rs ++ ss) ∧
      ((rs ++ ss).length : ℕ∞) = depth R I M := by
  intro rs
  induction rs with
  | nil =>
    intro M _ _ _ hIM _ _
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (depth_ne_top I hIM)
    obtain ⟨ss, hmem, hreg, hlen⟩ := exists_isRegular_length_eq I k M hIM hk.symm
    exact ⟨ss, hmem, by simpa using hreg, by simp [hlen, hk]⟩
  | cons x t ih =>
    intro M _ _ _ hIM hmem hreg
    rw [isRegular_cons_iff] at hreg
    have hxI : x ∈ I := hmem x (List.mem_cons_self ..)
    obtain ⟨ss, hss, hreg', hlen⟩ := ih (QuotSMulTop x M)
      ((smul_top_quotSMulTop_eq_top_iff I hxI).not.mpr hIM)
      (fun r hr => hmem r (List.mem_cons_of_mem _ hr)) hreg.2
    refine ⟨ss, hss, IsRegular.cons hreg.1 hreg', ?_⟩
    rw [List.cons_append, List.length_cons, Nat.cast_add, Nat.cast_one, hlen,
      depth_quotSMulTop_succ_eq I hxI hreg.1]

end PartTwo

/-- **Stacks 090R.** For `R` Noetherian, `I ⊆ R` an ideal and `M` a finite `R`-module: dividing
by a nonzerodivisor in `I` drops the `I`-depth by exactly one, and, when `I • M ≠ M`, every
`M`-regular sequence with all terms in `I` extends to one of length `depth_I(M)`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (∀ x ∈ I, IsSMulRegular M x → depth R I (QuotSMulTop x M) + 1 = depth R I M) ∧
      (I • (⊤ : Submodule R M) ≠ ⊤ → ∀ rs : List R, (∀ r ∈ rs, r ∈ I) →
        RingTheory.Sequence.IsRegular M rs →
          ∃ ss : List R, (∀ s ∈ ss, s ∈ I) ∧ RingTheory.Sequence.IsRegular M (rs ++ ss) ∧
            ((rs ++ ss).length : ℕ∞) = depth R I M) :=
  ⟨fun _ hx hreg => depth_quotSMulTop_succ_eq I hx hreg,
    fun hIM rs hmem hreg => exists_isRegular_append I rs M hIM hmem hreg⟩

end Stacks.Depth.ModNonzerodivisor

end

/-!
# Depth drops by one modulo a nonzerodivisor

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module. If `x ∈ I` is a
nonzerodivisor on `M`, then

`depth_I(M/xM) + 1 = depth_I(M)`,

and, provided `I • M ≠ M`, every `M`-regular sequence with all terms in `I` is the beginning of
an `M`-regular sequence with all terms in `I` whose length is exactly `depth_I(M)`.

The first assertion is the two halves of an inequality. The short exact sequence
`0 → M →(x·) M → M/xM → 0` and the estimate `min {depth_I(M), depth_I(M) - 1} ≤ depth_I(M/xM)`
of Stacks 00LX show the depth drops by at most one; conversely, if `x₁, …, x_r ∈ I` is an
`M/xM`-regular sequence then `x, x₁, …, x_r` is an `M`-regular sequence, so it drops by at
least one. The second assertion follows formally: an `M`-regular sequence `x₁, …, x_r` in `I`
whose length is smaller than `depth_I(M)` leaves `depth_I(M/(x₁, …, x_r)M) = depth_I(M) - r`
positive by `r` applications of the first assertion, so some `x_{r+1} ∈ I` is a nonzerodivisor
on `M/(x₁, …, x_r)M`, and the process stops after `depth_I(M) - r` steps because `depth_I(M)` is
finite: choosing `𝔭 ∈ Supp(M) ∩ V(I)`, which is nonempty as `M/IM ≠ 0`, gives
`depth_I(M) ≤ depth_{𝔭R_𝔭}(M_𝔭) ≤ dim(R_𝔭) = height(𝔭) < ∞`.

## Main results

* `Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append`: the two assertions of
  Stacks 090R, in the order in which the source states them, so that the second is `.2`.

## Implementation notes

Four departures from the source's form, none of them weakening it.

The source states the case `I = 𝔪` of the maximal ideal of a Noetherian local ring, writing
`depth(M)`; both assertions are stated here for an arbitrary ideal `I` of an arbitrary Noetherian
ring, which is the same proof: Stacks 00LX holds in that generality, and the remaining steps use
nothing about `I` beyond the memberships `x ∈ I`.

The source writes `depth(M/xM) = depth(M) - 1`. In `ℕ∞` the subtraction is truncated, so the
displayed equality `depth_I(M/xM) + 1 = depth_I(M)` is the sharper of the two forms: it is
equivalent to the source's given `depth_I(M) ≥ 1`, which holds here because `x` is a
nonzerodivisor on `M` lying in `I`, and it additionally rules out `depth_I(M) = 0`.

The source's hypothesis "`M` nonzero" is used only through `I • M ≠ M`, which is what it amounts
to for `I` the maximal ideal of a local ring and `M` finite, and only the second assertion needs
it: for the first, both sides are `⊤` when `I • M = M`, since then `I • (M/xM) = M/xM` as well.
It is therefore attached to the second conjunct rather than to the statement. Both parameters
`x` and `rs` are bound inside the conclusion for the same reason, so that neither assertion
carries the other's hypotheses.

"Extended to an `M`-regular sequence of length `depth(M)`" is spelled as the existence of a list
`ss` with `rs ++ ss` regular, rather than as a `List.IsPrefix`, so that the extending terms are
named and the requirement that they too lie in `I` can be stated. The quotient `M/xM` is
Mathlib's `QuotSMulTop x M` and "nonzerodivisor on `M`" is `IsSMulRegular M x`; regularity of a
sequence is `RingTheory.Sequence.IsRegular`, which already demands `M/(x₁, …, x_r)M ≠ 0`, so the
source's convention that a regular sequence is one with nonzero final quotient is Mathlib's.

Faithfulness. (1) No hypothesis is dead. `IsNoetherianRing R` and `Module.Finite R M` are the
source's and are consumed by Stacks 00LX, which is false without them. Inside the first conjunct,
`x ∈ I` is needed — over `R = k[x, y]` with `I = (y)` and `M = R` one has `depth_I(R) = 1` and
`depth_I(R/xR) = 1`, not `0` — and so is `IsSMulRegular M x`: over `R = k⟦x⟧` with `I = (x)` and
`M = R/xR` both depths are `0`. Inside the second conjunct all three hypotheses are needed:
without `I • M ≠ M` take `R = M = ℤ` and `I = ⊤`, where `depth_I(M) = ⊤` and no finite list has
that length; without `∀ r ∈ rs, r ∈ I` take `R = k⟦x, y⟧`, `I = (x)` and `rs = [x, y]`, which is
`R`-regular of length `2 > 1 = depth_I(R)`; without `IsRegular M rs` take `R = k⟦x⟧`, `I = (x)`,
`M = R` and `rs = [0]`, where the only candidate `ss` is `[]` and `[0]` is not `R`-regular.
(2) The scalars are the source's: `M` and `M/xM` are `R`-modules, the depths are taken over `R`
along the same ideal `I` of `R`, and the regular sequences are drawn from `I` itself with the
quotients `M/(x₁, …, x_i)M` formed over `R`; no localization or base change intervenes.
(3) Both assertions pin their objects rather than merely bounding them: the first is an equality
of values of `Module.depth` (Stacks 00LI) at the module `QuotSMulTop x M` named by `x`, and the
second pins the extension by requiring `rs` to be a literal prefix of the produced sequence and
its length to equal `depth_I(M)` on the nose, not merely to be at least `rs.length`.
(4) The instantiation is not degenerate: for `R = k⟦x, y⟧`, `I = 𝔪` and `M = R` the first
assertion reads `depth_𝔪(R/xR) + 1 = 1 + 1 = 2 = depth_𝔪(R)`, and the second extends the
`R`-regular sequence `rs = [x]` by `ss = [y]` to `[x, y]`, of length `2 = depth_𝔪(R)`.

## References

* [StacksProject 090R](https://stacks.math.columbia.edu/tag/090R)

## Tags

depth, regular sequence, nonzerodivisor, Noetherian ring
-/

@[expose] public section

namespace Module

/-- **Depth drops by one modulo a nonzerodivisor, and regular sequences extend to length equal
to the depth.** Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module.

1. If `x ∈ I` is a nonzerodivisor on `M`, then `depth_I(M/xM) + 1 = depth_I(M)`.
2. If `I • M ≠ M`, then every `M`-regular sequence `rs` with all terms in `I` extends to an
   `M`-regular sequence `rs ++ ss` with all terms in `I` and `(rs ++ ss).length = depth_I(M)`.

The source states this for `I` the maximal ideal of a Noetherian local ring and `M` nonzero,
and writes (1) as `depth(M/xM) = depth(M) - 1`; the equality with `+ 1` on the left is the
sharper form in `ℕ∞`, where subtraction is truncated. -/
@[stacks 090R "Stated for an arbitrary ideal of a Noetherian ring; `M` nonzero is used only as \
  `I • M ≠ M`, and only by part (2), so both parameters are bound inside the conclusion.",
  sga "2 III 2.6"]
public theorem depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append {R : Type*}
    [CommRing R] [IsNoetherianRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    (∀ x ∈ I, IsSMulRegular M x → depth R I (QuotSMulTop x M) + 1 = depth R I M) ∧
      (I • (⊤ : Submodule R M) ≠ ⊤ → ∀ rs : List R, (∀ r ∈ rs, r ∈ I) →
        RingTheory.Sequence.IsRegular M rs →
          ∃ ss : List R, (∀ s ∈ ss, s ∈ I) ∧ RingTheory.Sequence.IsRegular M (rs ++ ss) ∧
            ((rs ++ ss).length : ℕ∞) = depth R I M) :=
  Stacks.Depth.ModNonzerodivisor.solution I M

end Module

end

/-!
# Depth is at most the dimension of `R/𝔭` for an associated prime `𝔭`

Proof of `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` (Stacks 0BK4): for
`(R, 𝔪)` a Noetherian local ring, `M` a finite `R`-module and `𝔭 ∈ Ass(M)`,

`depth_𝔪(M) ≤ dim(R/𝔭)`.

Both sides are read in `Spec(R)`: `dim(R/𝔭)` is the coheight of `𝔭`, and `depth_𝔪(M)` is the
length of an `M`-regular sequence in `𝔪`, so the inequality is the statement that `𝔭` admits a
chain of primes above it as long as any such sequence. That chain is built one prime at a time by
the source's induction, whose step is `exists_lt_mem_associatedPrimes_quotSMulTop`: a module of
positive depth with `𝔭` associated has a nonzerodivisor `x ∈ 𝔪`, which therefore avoids `𝔭`, and
any prime `𝔮` minimal over `𝔭 + (x)` is then strictly above `𝔭` and is associated to `M/xᵏM` for
some `k ≥ 1` (Stacks 0CN5), a module of depth one less (Stacks 090R(1)). Iterating the step
`depth_𝔪(M)` times produces the chain, and the iteration terminates because the depth is
*attained* by a regular sequence, hence finite.

## Main results

* `Stacks.Depth.AssociatedPrimeBound.solution`: `depth(M) ≤ dim(R/𝔭)` for an associated prime `𝔭`
  of a finite module `M` over a Noetherian local ring.

## Implementation notes

The induction is carried out in `ℕ∞` on `Order.coheight 𝔭` rather than in `WithBot ℕ∞` on
`ringKrullDim (R ⧸ 𝔭)`, and the translation between the two is made once, in `solution`. This
removes the base case: `0 ≤ coheight 𝔭` is trivial, where `0 ≤ dim(R ⧸ 𝔭)` needs `R ⧸ 𝔭` to be
nonzero, and it removes the `WithBot` arithmetic from the step. The bridge
`ringKrullDim (R ⧸ 𝔭) = coheight 𝔭` is `ringKrullDim_quotient` together with
`V(𝔭) = Set.Ici 𝔭`, which holds by definition; Mathlib has no lemma for it.

The source finishes by computing `dim(R/𝔭 + (x)) = dim(R/𝔭) - 1` (Stacks 00KW) and picking a
minimal prime `𝔮` over `𝔭 + (x)` realizing that dimension, an argument it leaves out. Neither
step is needed: `𝔮` contains `x` and `𝔭` does not, so `𝔭 < 𝔮`, and the one-step estimate
`Order.coheight_add_one_le` already gives `coheight 𝔮 + 1 ≤ coheight 𝔭`, which is the only
consequence of the omitted argument that the induction uses. So *any* minimal prime over
`𝔭 + (x)` will do, and one exists because `𝔭 + (x) ≤ 𝔪` is not the unit ideal.

Two facts about `Module.depth` (Stacks 00LI) and `associatedPrimes` that Mathlib does not
state — the first for lack of the definition — are proved here as private lemmas: that the
depth of a nonzero finite module over a Noetherian local ring is attained by a regular sequence
in `𝔪`, which is Stacks 090R(2) fed with the empty sequence; and that a nonzerodivisor on `M`
lies in no associated prime of `M`. A module of positive depth has a nonzerodivisor in `𝔪` by
`exists_mem_isSMulRegular_of_depth_ne_zero` above.

## References

* [StacksProject 0BK4](https://stacks.math.columbia.edu/tag/0BK4)
-/

@[expose] public section

namespace Stacks.Depth.AssociatedPrimeBound

open Ideal IsLocalRing Module RingTheory.Sequence



section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A module with an associated prime is nonzero: a zero module has no associated primes. -/
private theorem nontrivial_of_mem_associatedPrimes {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) : Nontrivial M := by
  rcases subsingleton_or_nontrivial M with _ | hn
  · simp [associatedPrimes.eq_empty_of_subsingleton] at hp
  · exact hn

/-- The depth of a nonzero finite module over a Noetherian local ring is attained: it is the
length of some `M`-regular sequence with all terms in the maximal ideal. In particular it is
finite. -/
@[ega "0 16.5.9" "special case", sga "2 III 2.6" "special case"]
private theorem exists_isRegular_length_eq_depth [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] :
    ∃ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M rs ∧
      (rs.length : ℕ∞) = depth R (maximalIdeal R) M := by
  obtain ⟨rs, hmem, hreg, hlen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append (maximalIdeal R) M).2
      (Module.maximalIdeal_smul_top_ne_top _) [] (by simp) (IsRegular.nil R M)
  rw [List.nil_append] at hreg hlen
  exact ⟨rs, hmem, hreg, hlen⟩

/-- An element that is a nonzerodivisor on `M` lies in no associated prime of `M`. -/
private theorem notMem_of_isSMulRegular [IsNoetherianRing R] {x : R} (hx : IsSMulRegular M x)
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) : x ∉ p := fun hxp => by
  have hmem : x ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) := Set.mem_biUnion hp hxp
  rw [biUnion_associatedPrimes_eq_compl_regular] at hmem
  exact hmem hx

/-- **The descent step of Stacks 0BK4.** Let `𝔭` be an associated prime of a finite module `M` of
positive depth over a Noetherian local ring `(R, 𝔪)`. Then some `y ∈ 𝔪` and some prime `𝔮`
*strictly above* `𝔭` satisfy `𝔮 ∈ Ass(M/yM)` and `depth_𝔪(M/yM) + 1 = depth_𝔪(M)`.

This carries the whole content of the induction of Stacks 0BK4: positive depth provides a
nonzerodivisor `x ∈ 𝔪` on `M`, which then avoids `𝔭` because an associated prime consists of
zerodivisors; any prime `𝔮` minimal over `𝔭 + (x)` — one exists since `𝔭 + (x) ≤ 𝔪` — contains
`x` and hence is strictly above `𝔭`, and is associated to `M/xᵏM` for some `k ≥ 1` by Stacks
0CN5, a module whose depth is one less by Stacks 090R(1). The witness is `y = xᵏ`. -/
private theorem exists_lt_mem_associatedPrimes_quotSMulTop [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] {p : Ideal R} (hp : p ∈ associatedPrimes R M)
    (hd : 1 ≤ depth R (maximalIdeal R) M) :
    ∃ (q : Ideal R) (y : R), p < q ∧ q ∈ associatedPrimes R (QuotSMulTop y M) ∧
      depth R (maximalIdeal R) (QuotSMulTop y M) + 1 = depth R (maximalIdeal R) M := by
  obtain ⟨x, hxm, hxreg⟩ := Stacks.Depth.ModNonzerodivisor.exists_mem_isSMulRegular_of_depth_ne_zero
    (maximalIdeal R) (M := M) (zero_lt_one.trans_le hd).ne'
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (J := maximalIdeal R)
    (sup_le (le_maximalIdeal hp.isPrime.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hxm))
  obtain ⟨k, hk, hqass⟩ :=
    exists_mem_associatedPrimes_quotSMulTop_pow_of_mem_minimalPrimes x hp hq
  refine ⟨q, x ^ k, lt_of_le_of_ne (le_sup_left.trans hq.1.2) ?_, hqass,
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append (maximalIdeal R) M).1
      _ (Ideal.pow_mem_of_mem _ hxm k hk) (hxreg.pow k)⟩
  exact fun hpq => notMem_of_isSMulRegular hxreg hp
    (hpq ▸ hq.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

/-- **The induction of Stacks 0BK4, over a fixed ring.** If `n ≤ depth_𝔪(M)`, then every
associated prime `𝔭` of `M` has at least `n` primes strictly above it, i.e.
`n ≤ coheight 𝔭`. The module varies along the induction, `M` being replaced by `M/yM`, so it is
quantified over inside, while the ring stays fixed. -/
private theorem le_coheight_of_le_depth {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R)
      (hp : p ∈ associatedPrimes R M), (n : ℕ∞) ≤ depth R (maximalIdeal R) M →
      (n : ℕ∞) ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
  induction n with
  | zero =>
    intro M _ _ _ p hp _
    simp
  | succ n ih =>
    intro M _ _ _ p hp hd
    obtain ⟨q, y, hpq, hqass, hdrop⟩ := exists_lt_mem_associatedPrimes_quotSMulTop hp
      (le_trans (by simp) hd)
    have hn : (n : ℕ∞) ≤ depth R (maximalIdeal R) (QuotSMulTop y M) := by
      rw [← hdrop] at hd
      push_cast at hd
      exact (WithTop.add_le_add_iff_right (z := (1 : ℕ∞)) ENat.one_ne_top).mp hd
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := Nat.cast_add_one n
      _ ≤ Order.coheight (⟨q, hqass.isPrime⟩ : PrimeSpectrum R) + 1 :=
        add_le_add (ih _ q hqass hn) le_rfl
      _ ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
        Order.coheight_add_one_le (PrimeSpectrum.asIdeal_lt_asIdeal _ _ |>.mp hpq)

/-- **Stacks 0BK4.** Let `(R, 𝔪)` be a Noetherian local ring and `M` a finite `R`-module. If `𝔭`
is an associated prime of `M`, then `depth(M) ≤ dim(R/𝔭)`, the depth being taken along `𝔪`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have : Nontrivial M := nontrivial_of_mem_associatedPrimes hp
  have : p.IsPrime := hp.isPrime
  obtain ⟨rs, -, -, hlen⟩ := exists_isRegular_length_eq_depth (R := R) (M := M)
  rw [← hlen, ← coheight_eq_ringKrullDim_quotient ⟨p, hp.isPrime⟩]
  exact_mod_cast le_coheight_of_le_depth rs.length M p hp hlen.le

end Stacks.Depth.AssociatedPrimeBound

end

/-!
# Depth is at most the dimension of `R/𝔭` for an associated prime `𝔭`

Let `(R, 𝔪)` be a Noetherian local ring and `M` a finite `R`-module. Every associated prime of
`M` cuts out a closed subscheme of `Spec(R)` at least as big as the depth of `M`:

`depth(M) ≤ dim(R/𝔭)` for all `𝔭 ∈ Ass(M)`.

The source's route is an induction on `depth(M)`. If `𝔪 ∈ Ass(M)` there is a nonzero `x ∈ M`
killed by `𝔪`, so `depth(M) = 0` and there is nothing to prove; this also settles
`depth(M) ≤ 1`, since then `𝔪 ∉ Ass(M)` and every `𝔭 ∈ Ass(M)` is a non-maximal prime, so
`dim(R/𝔭) ≥ 1`. For `depth(M) > 1` pick `x ∈ 𝔪` a nonzerodivisor on `M`; then `x ∉ 𝔭` (an
associated prime consists of zerodivisors), so `dim(R/𝔭 + (x)) = dim(R/𝔭) - 1` and some prime
`𝔮` minimal over `𝔭 + (x)` has `dim(R/𝔮) = dim(R/𝔭) - 1`. Such a `𝔮` is an associated prime of
`M/xⁿM` for suitable `n ≥ 1` (Stacks 0CN5), and `depth(M/xⁿM) = depth(M) - 1` (Stacks 090R), so
the induction hypothesis gives `dim(R/𝔮) ≥ depth(M/xⁿM)` and hence the claim.

## Main results

* `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`: the inequality above.

## Implementation notes

The depth is `Module.depth R (IsLocalRing.maximalIdeal R) M` (Stacks 00LI), with values in `ℕ∞`,
coerced into `WithBot ℕ∞`, where `ringKrullDim (R ⧸ 𝔭)` lives on the nose; this is the coercion
convention of the siblings `Module.depth_le_supportDim` (Stacks 00LK) and Stacks 0BUS. The source
writes the inequality as `dim(R/𝔭) ≥ depth(M)`; it is stated here as `≤` with the smaller
quantity on the left, as Mathlib does. No finiteness of either side is asserted separately: both
are elements of `WithBot ℕ∞` and the inequality is the whole content. In particular the statement
does not presuppose `𝔪 • M ≠ M`, which `𝔭 ∈ Ass(M)` forces anyway through `M ≠ 0` and Nakayama,
and which is what keeps the left-hand side below `⊤`.

Locality is not removable, and neither is the maximal ideal replaceable by an arbitrary ideal
`I`: over `R = k[x, y]` with `M = R/(x, y) ⊕ R`, `I = (x - 1, y - 1)` and `𝔭 = (x, y) ∈ Ass(M)`
one has `I • M ≠ M` and `depth_I(M) = 1`, since `x - 1` is a nonzerodivisor on `M`, while
`dim(R/𝔭) = 0`. What survives without locality is the same inequality under the extra hypothesis
`𝔭 ≤ I`: choosing a prime `𝔮 ⊇ I`, the localization `M_𝔮` is nonzero with `𝔭R_𝔮 ∈ Ass(M_𝔮)` and
`depth_I(M) ≤ depth(M_𝔮) ≤ dim(R_𝔮/𝔭R_𝔮) ≤ dim(R/𝔭)`, the middle step being this lemma.

Faithfulness. (1) Every hypothesis is used by the conclusion. `IsLocalRing R` is what makes
`depth` refer to `𝔪` at all, and it is not droppable even in the presence of the other
hypotheses (counterexample above). `Module.Finite R M` fails without: for `R` a discrete
valuation ring and `M = Frac(R)` one has `𝔭 = (0) ∈ Ass(M)`, since `M` is torsion free, and
`dim(R/𝔭) = 1`, while `𝔪 • M = M` makes `depth(M) = ⊤`. It is Nakayama, hence finiteness,
that keeps the left-hand side finite at all. `hp` fails without: for `R = k[[x, y]]` and `M = R`
the prime `𝔭 = (x, y)`, not associated to `R` because `Ass(R) = {(0)}` for a domain, has
`dim(R/𝔭) = 0 < 2 = depth(R)`. `IsNoetherianRing R` is used throughout the source's route: the
finiteness of `Ass(M)` produces the nonzerodivisor `x ∈ 𝔪` by prime avoidance, Artin–Rees
produces the `n` of Stacks 0CN5, and Stacks 090R is quoted for `M/xⁿM`; whether it is removable
is not claimed here in either direction. (2) The scalars and base are the source's: `M` is an
`R`-module, the depth is taken along the maximal ideal of `R` itself, and `𝔭` is an ideal of `R`
with the quotient `R ⧸ 𝔭` formed over `R`; nothing is localized at `𝔭` — the inequality for
`depth(M_𝔭)` is the different statement Stacks 0FCC. (3) The source names no canonical map here;
both sides are pinned as the functions `Module.depth R (IsLocalRing.maximalIdeal R) M` and
`ringKrullDim (R ⧸ 𝔭)`, for the given `𝔭` rather than for some associated prime, so the
statement is the numerical inequality itself and not an existence claim. (4) The instantiation
is not degenerate: for `R` a discrete valuation ring and `M = R` the associated prime `𝔭 = (0)`
is not the maximal ideal and the inequality reads `1 ≤ 1`; over `R = k[[x, y]]` with
`M = R ⊕ R/(x, y)` and `𝔭 = (0) ∈ Ass(M)` it reads `0 ≤ 2` and is strict, so neither side is
forced to `0` nor to `⊤`.

## References

* [StacksProject 0BK4](https://stacks.math.columbia.edu/tag/0BK4)

## Tags

depth, associated prime, Krull dimension, Noetherian local ring
-/

namespace Module

/-- **Stacks 0BK4**. Let `(R, 𝔪)` be a Noetherian local ring and `M` a finite `R`-module. If `𝔭`
is an associated prime of `M`, then `depth(M) ≤ dim(R/𝔭)`, the depth being taken along `𝔪`.

The source states this as `dim(R/𝔭) ≥ depth(M)`. -/
@[stacks 0BK4, ega "0 16.4.6" "(iii), first inequality"]
public theorem depth_le_ringKrullDim_quotient_of_mem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
  Stacks.Depth.AssociatedPrimeBound.solution hp

end Module
