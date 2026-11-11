module

public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthTwo
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Local cohomology vanishes below the depth

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module with `IM ≠ M`. One of
the two inequalities making up the equality of parts (1) and (3) of [Stacks, Lemma 0AVZ] is that
`H^i_{V(I)}(M) = 0` for every `i < depth_I(M)`. That inequality is proved here, in every degree.

The mechanism is the one already used for the degrees `0` and `1` in
`StacksFrontier/RingTheory/LocalCohomology/DepthVanishing/DepthTwo.lean`, run as an induction along
a regular sequence rather than unrolled twice. For `f ∈ I` a nonzerodivisor on `M`, the short exact
sequence `0 → M →^f M → M/fM → 0` has a connecting map `H^{i-1}_{V(I)}(M/fM) ⟶ H^i_{V(I)}(M)`; if
the source vanishes then multiplication by `f` is injective on `H^i_{V(I)}(M)`, and a module
supported in `V(I)` on which some element of `I` acts injectively is zero. Since the tail of an
`M`-regular sequence is an `M/fM`-regular sequence one shorter, induction on the length of the
sequence gives the vanishing in all degrees below it, the negative degrees being covered directly
by `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_neg`. The passage from a length
bound to a depth bound is Tag 090R, which extends the empty sequence to an `M`-regular sequence in
`I` of length exactly `depth_I(M)`.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomology_of_isRegular` — **`H^i_{V(I)}(M) = 0` for
  `i < r`** whenever `I` contains an `M`-regular sequence of length `r`.
* `Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth` — **the depth form**:
  `H^i_{V(I)}(M) = 0` for `i < n` whenever `n ≤ depth_I(M)`.
* `Stacks.LocalCohomology.depth_le_sInf_nontrivial_localCohomologyWithSupportIn` — the same
  statement read as an inequality of extended naturals: `depth_I(M)` is at most the least degree
  in which `H^i_{V(I)}(M)` is nonzero.
* `Stacks.LocalCohomology.isZero_localCohomology_closedPoint_of_lt_depth` and
  `Stacks.LocalCohomology.subsingleton_localCohomology_closedPoint_of_lt_depth` — the
  specialisation to `M = A` over a Noetherian local ring, with the support written as the
  singleton `{closedPoint A}` rather than as `V(𝔪)`.

## Implementation notes

No Stacks attribute is placed, for the reason already recorded in `DepthTwo.lean`: tag 0AVZ
asserts the equality of three quantities together with an `Ext`-vanishing statement, and what is
proved here is one inequality between the first and the third, so an attribute here would attach
the tag to a proper part of it. The tag is carried, clause by clause and then whole, by the
covering set described in the module docstring of
`StacksFrontier/RingTheory/LocalCohomology/DepthVanishing/DepthEqLocalCohomology.lean`; the
`depth_I(M) ≤ inf {i | H^i_{V(I)}(M) ≠ 0}` half proved here is one of its two inputs.
The declarations of `DepthTwo.lean` are kept rather than restated as
corollaries: they are the degree-by-degree form, they are what Hartshorne's connectedness theorem
[Stacks, Lemma 0BLR] consumes, and this file imports them for the two base steps.

The closed-point forms exist because that is the spelling in which chapter 58 uses this result:
the support there is `{closedPoint A}`, not `V(𝔪)`, and the two are identified by
`zeroLocus_maximalIdeal`.

### What this leaves of the purity chain above it

[Stacks, Lemma 0BLM] — in the local Lefschetz situation
(`Stacks.FundamentalGroup.LocalLefschetzSituation`, tag 0BLF), a finite étale cover of the
punctured spectrum extends over `Spec A` once `depth(A) ≥ 3` and the cover restricted to the
hypersurface section already extends — reduces to [Stacks, Lemma 0BLS], the same conclusion with
the depth hypothesis replaced by: some power of the hypersurface equation `f` kills `H^1_𝔪(A)` and
some power kills `H^2_𝔪(A)`. The reduction is exactly
`subsingleton_localCohomology_closedPoint_of_lt_depth A 3 hdepth i hi` for `i = 1, 2`, which this
file supplies: a subsingleton is killed by `f ^ 0`. The other two inputs of that reduction are
the local cohomology functor (tag 0EF4, formalized as
`Stacks.LocalCohomology.localCohomologyWithSupportIn`) and 0BLS itself, which carries the
mathematical content: it is proved from the full faithfulness of restriction of finite étale
covers to the hypersurface section ([Stacks, Lemma 0BM6]). Tag 0BLS is formalized, in the
coreflection model of local cohomology, as
`…LocalLefschetzSituation.exists_finiteEtale_extension_of_localCohomology_annihilated`
in `StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.ExtensionFromHypersurface`.

## References

* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
* [Stacks Project, Tag 0BLM](https://stacks.math.columbia.edu/tag/0BLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **An `M`-regular sequence of length `r` inside `I` kills `H^i_{V(I)}(M)` for every `i < r`.**

Induction on the sequence. The negative degrees vanish outright. In degree `i ≥ 0`, writing the
sequence as `f :: t`, the tail `t` is `M/fM`-regular of length `r - 1`, so the inductive hypothesis
gives `H^{i-1}_{V(I)}(M/fM) = 0`; hence the connecting map of `0 → M →^f M → M/fM → 0` into
`H^i_{V(I)}(M)` vanishes, multiplication by `f` is injective there, and a module supported in
`V(I)` on which an element of `I` acts injectively is zero. -/
theorem isZero_localCohomology_of_isRegular (I : Ideal A) (rs : List A)
    (hrsI : ∀ r ∈ rs, r ∈ I) (M : ModuleCat.{max u v} A)
    (hreg : RingTheory.Sequence.IsRegular (M : Type (max u v)) rs)
    (i : ℤ) (hi : i < rs.length) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  induction rs generalizing M i with
  | nil => exact isZero_localCohomologyWithSupportIn_of_neg.{u, v} _ M i (by simpa using hi)
  | cons f t ih =>
    rcases lt_or_ge i 0 with hneg | _
    · exact isZero_localCohomologyWithSupportIn_of_neg.{u, v} _ M i hneg
    rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
    obtain ⟨hregf, hregt⟩ := hreg
    have hfI : f ∈ I := hrsI f (by simp)
    have htI : ∀ r ∈ t, r ∈ I := fun r hr ↦ hrsI r (by simp [hr])
    have hlt : i - 1 < (t.length : ℤ) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi
      omega
    set T := PrimeSpectrum.zeroLocus (I : Set A) with hT
    have hS := smulShortComplex_shortExact.{u, v} hregf
    have hδ : localCohomologyδ.{u, v} T hS (i - 1) i (by ring) = 0 :=
      (ih htI (ModuleCat.of A (QuotSMulTop f (M : Type (max u v)))) hregt (i - 1)
        hlt).eq_of_src _ _
    have hmono : Mono (localCohomologyMap.{u, v} A T i (smulShortComplex.{u, v} f M).f) :=
      (mono_localCohomologyMap_f_iff.{u, v} T hS (i - 1) i (by ring)).mpr hδ
    have hval : localCohomologyMap.{u, v} A T i (smulShortComplex.{u, v} f M).f =
        f • 𝟙 (localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
      localCohomologyMap_smul_id A T i M f
    rw [hval] at hmono
    exact isZero_of_mono_smul_id.{u, v} I hfI _
      (support_localCohomologyWithSupportIn_subset.{u, v} T _ i) hmono

/-- **`H^i_{V(I)}(M) = 0` below the depth.** Let `A` be Noetherian, `I ⊆ A` an ideal and `M` a
finite `A`-module with `IM ≠ M`. If `n ≤ depth_I(M)` then `H^i_{V(I)}(M) = 0` for every `i < n`.

This is the inequality `depth_I(M) ≤ (least `i` with `H^i_{V(I)}(M) ≠ 0`)` of
[Stacks, Lemma 0AVZ], in all degrees; the degrees `i ≤ 1` are
`Stacks.LocalCohomology.isZero_localCohomology_le_one_of_two_le_depth`. The regular sequence
realizing the depth comes from Tag 090R. -/
theorem isZero_localCohomology_of_lt_depth (I : Ideal A)
    (M : ModuleCat.{max u v} A) [Module.Finite A (M : Type (max u v))]
    (hIM : I • (⊤ : Submodule A (M : Type (max u v))) ≠ ⊤)
    (n : ℕ) (hdepth : (n : ℕ∞) ≤ Module.depth A I (M : Type (max u v)))
    (i : ℤ) (hi : i < n) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  have hnt : Nontrivial (M : Type (max u v)) := by
    rcases subsingleton_or_nontrivial (M : Type (max u v)) with hsub | h
    · refine absurd ?_ hIM
      refine top_unique fun x _ ↦ ?_
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    · exact h
  have hnil : RingTheory.Sequence.IsRegular (M : Type (max u v)) [] :=
    RingTheory.Sequence.IsRegular.nil A (M : Type (max u v))
  obtain ⟨ss, hssI, hssreg, hsslen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I
      (M : Type (max u v))).2 hIM [] (by simp) hnil
  rw [List.nil_append] at hssreg hsslen
  have hlen : (n : ℤ) ≤ (ss.length : ℤ) := by
    have h : ((n : ℕ) : ℕ∞) ≤ ((ss.length : ℕ) : ℕ∞) := hsslen ▸ hdepth
    exact_mod_cast (by exact_mod_cast h : n ≤ ss.length)
  exact isZero_localCohomology_of_isRegular.{u, v} I ss hssI M hssreg i (hi.trans_le hlen)

/-- **The depth is at most the first nonvanishing local-cohomology degree.** For `A` Noetherian,
`I ⊆ A` an ideal and `M` a finite `A`-module with `IM ≠ M`,
`depth_I(M) ≤ inf {i | H^i_{V(I)}(M) ≠ 0}` in `ℕ∞`, the infimum of the empty set being `⊤`.

This is one of the two inequalities of the equality of parts (1) and (3) of
[Stacks, Lemma 0AVZ]. The reverse inequality — that `H^i_{V(I)}(M)` really is nonzero in degree
`depth_I(M)` — is not proved here. -/
theorem depth_le_sInf_nontrivial_localCohomologyWithSupportIn (I : Ideal A)
    (M : ModuleCat.{max u v} A) [Module.Finite A (M : Type (max u v))]
    (hIM : I • (⊤ : Submodule A (M : Type (max u v))) ≠ ⊤) :
    Module.depth A I (M : Type (max u v)) ≤
      sInf {m : ℕ∞ | ∃ i : ℕ, m = (i : ℕ∞) ∧
        Nontrivial (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) (i : ℤ))} := by
  refine le_sInf ?_
  rintro m ⟨i, rfl, hnt⟩
  by_contra hcon
  rw [not_le] at hcon
  have hle : ((i + 1 : ℕ) : ℕ∞) ≤ Module.depth A I (M : Type (max u v)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Order.add_one_le_of_lt hcon
  have hz := isZero_localCohomology_of_lt_depth.{u, v} I M hIM (i + 1) hle (i : ℤ)
    (by exact_mod_cast Nat.lt_succ_self i)
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  exact hxy ((ModuleCat.isZero_iff_subsingleton.mp hz).elim x y)

/-- **`H^i_𝔪(A) = 0` below the depth, with the support written as the closed point.** For `A` a
Noetherian local ring and `n ≤ depth(A)`, the local cohomology of `A` supported at the closed
point of `Spec A` vanishes in every degree `i < n`.

This is the spelling in which the local Lefschetz situation of [Stacks, Tag 0BLF] uses the
statement; `V(𝔪) = {𝔪}` is `zeroLocus_maximalIdeal`. -/
theorem isZero_localCohomology_closedPoint_of_lt_depth (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (n : ℕ)
    (hdepth : (n : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A)
    (i : ℤ) (hi : i < n) :
    IsZero (localCohomologyWithSupportIn A {IsLocalRing.closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) i) := by
  have hsmul : (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A A) =
      IsLocalRing.maximalIdeal A := by simp
  have h := isZero_localCohomology_of_lt_depth.{u, u} (IsLocalRing.maximalIdeal A)
    (ModuleCat.of A A) (by rw [hsmul]; exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top)
    n hdepth i hi
  rwa [zeroLocus_maximalIdeal] at h

/-- **The subsingleton form of the previous statement.** `H^i_𝔪(A)` has at most one element for
`i < n ≤ depth(A)`, over a Noetherian local ring `A`.

In this form the statement is the local-cohomology input of [Stacks, Lemma 0BLM]: there one needs
some power of the hypersurface equation to kill `H^1_𝔪(A)` and `H^2_𝔪(A)` when `depth(A) ≥ 3`, and
the zeroth power kills a subsingleton. -/
theorem subsingleton_localCohomology_closedPoint_of_lt_depth (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (n : ℕ)
    (hdepth : (n : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A)
    (i : ℤ) (hi : i < n) :
    Subsingleton (localCohomologyWithSupportIn A {IsLocalRing.closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) i) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_localCohomology_closedPoint_of_lt_depth A n hdepth i hi)

end Stacks.LocalCohomology

end
