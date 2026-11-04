module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.QuotSMulTop
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported

/-!
# Local cohomology below the depth

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module with `IM ≠ M`. Part of
[Stacks, Lemma 0AVZ] is that `H^i_I(M) = 0` for `i < depth_I(M)`. This file proves the two cases
`i = 0` and `i = 1`, which are the ones Hartshorne's connectedness theorem
([Stacks, Lemma 0BLR]) consumes: a Noetherian local ring of depth at least two has
`H^0_𝔪(A) = H^1_𝔪(A) = 0`.

The mechanism is the long exact sequence of
`StacksFrontier/RingTheory/LocalCohomology/DepthVanishing/Triangulated.lean` applied to
`0 → M →^f M → M/fM → 0` for `f ∈ I` a nonzerodivisor on `M`, together with two facts from
`Supported.lean`: local cohomology vanishes in negative degrees, and `H^i_I(M)` is supported in
`V(I)`. The first makes the connecting map into `H^0_I(M)` vanish, so that multiplication by `f`
is injective on `H^0_I(M)`; being supported in `V(I)`, that module is killed by a power of `f`,
hence is zero. Repeating the argument one degree up — now with `H^0_I(M/fM) = 0`, which is the
case already proved applied to the second term of a regular sequence — gives `H^1_I(M) = 0`.

## Main definitions

* `Stacks.LocalCohomology.smulShortComplex` — the short complex `M →^f M → M/fM`.

## Main results

* `Stacks.LocalCohomology.smulShortComplex_shortExact` — it is short exact when `f` is a
  nonzerodivisor on `M`.
* `Stacks.LocalCohomology.isZero_localCohomology_zero_of_isSMulRegular` — **`H^0_{V(I)}(M) = 0`**
  when some `f ∈ I` is a nonzerodivisor on `M`.
* `Stacks.LocalCohomology.isZero_localCohomology_one_of_isSMulRegular` — **`H^1_{V(I)}(M) = 0`**
  when in addition some `g ∈ I` is a nonzerodivisor on `M/fM`.
* `Stacks.LocalCohomology.isZero_localCohomology_le_one_of_two_le_depth` — **the depth form**:
  `H^0_{V(I)}(M) = H^1_{V(I)}(M) = 0` when `depth_I(M) ≥ 2`.
* `Stacks.LocalCohomology.isZero_localCohomology_le_one_of_two_le_depth_local` — its
  specialisation to a Noetherian local ring of depth at least two, which is the form
  [Stacks, Lemma 0BLR] consumes.

## Implementation notes

No Stacks attribute for tag 0AVZ is placed, and this is deliberate. Tag 0AVZ asserts the equality
of *three* quantities — `depth_I(M)`, the least `i` with `Ext^i_A(A/I, M) ≠ 0`, and the least `i`
with `H^i_I(M) ≠ 0` — together with a vanishing statement for `Ext^i_A(N, M)` for every finite `N`
annihilated by a power of `I`. What is proved here is the single implication
`depth_I(M) ≥ 2 ⇒ H^0_I(M) = H^1_I(M) = 0`, i.e. two instances of one inequality between the first
and the third quantity, so an attribute here would attach the tag to a proper part of it. The tag
is carried, clause by clause and then whole, by the covering set described in the module docstring
of `StacksFrontier/RingTheory/LocalCohomology/DepthVanishing/DepthEqLocalCohomology.lean`.

Likewise no Stacks attribute for tag 0BLR: the three declarations of that tag are statements about
the punctured spectra of `A`, `A^h` and `A^sh`, none of which is proved here. This file supplies
the depth input of the first of them.

The regular sequence of length two underlying the depth form is extracted from
`Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` (Tag 090R), whose second
assertion extends the empty sequence to one of length exactly `depth_I(M)`.

## References

* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### The short exact sequence of multiplication by a nonzerodivisor -/

/-- The short complex `M →^f M → M/fM`, where the first map is multiplication by `f`. -/
def smulShortComplex (r : A) (M : ModuleCat.{max u v} A) :
    ShortComplex (ModuleCat.{max u v} A) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of A (QuotSMulTop r (M : Type (max u v)))
  f := r • 𝟙 M
  g := ModuleCat.ofHom (Submodule.mkQ (r • (⊤ : Submodule A (M : Type (max u v)))))
  zero := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_pointwise_smul x r ⊤ Submodule.mem_top)

/-- The first map of `smulShortComplex` is multiplication by `r`. -/
lemma smulShortComplex_f (r : A) (M : ModuleCat.{max u v} A) :
    (smulShortComplex.{u, v} r M).f = r • 𝟙 M := rfl

/-- **`0 → M →^f M → M/fM → 0` is exact** when `f` is a nonzerodivisor on `M`. -/
lemma smulShortComplex_shortExact {r : A} {M : ModuleCat.{max u v} A}
    (hr : IsSMulRegular (M : Type (max u v)) r) :
    (smulShortComplex.{u, v} r M).ShortExact := by
  have hex : ∀ x : (M : Type (max u v)),
      (Submodule.mkQ (r • (⊤ : Submodule A (M : Type (max u v))))) x = 0 →
      ∃ y : (M : Type (max u v)), r • y = x := by
    intro x hx
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hx
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x r ⊤).mp hx
    exact ⟨y, hy⟩
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    exact hex
  · exact (ModuleCat.mono_iff_injective _).mpr hr
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-! ### Vanishing of `H⁰` and `H¹` -/

variable [IsNoetherianRing A]

/-- If `f ∈ I` is a nonzerodivisor on `M` and `H^i_{V(I)}(M/fM) = 0`, then `H^{i+1}_{V(I)}(M) = 0`:
the connecting map vanishes, so `f` is injective on the module, which is supported in `V(I)`. -/
private theorem isZero_localCohomology_succ_of_isZero_quotSMulTop (I : Ideal A) {f : A}
    (hf : f ∈ I) (M : ModuleCat.{max u v} A) (hreg : IsSMulRegular (M : Type (max u v)) f)
    (i j : ℤ) (h : i + 1 = j)
    (hzero : IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (smulShortComplex.{u, v} f M).X₃) i)) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) j) := by
  have hS := smulShortComplex_shortExact.{u, v} hreg
  have hmono : Mono (localCohomologyMap.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) j
      (f • 𝟙 M)) :=
    (mono_localCohomologyMap_f_iff.{u, v} _ hS i j h).mpr (hzero.eq_of_src _ _)
  rw [localCohomologyMap_smul_id] at hmono
  exact isZero_of_mono_smul_id.{u, v} I hf _
    (support_localCohomologyWithSupportIn_subset.{u, v} _ _ j) hmono

/-- **`H^0_{V(I)}(M) = 0` when some `f ∈ I` is a nonzerodivisor on `M`.** The connecting map into
`H^0` comes from `H^{-1}` of the quotient, which vanishes, so multiplication by `f` is injective
on `H^0_{V(I)}(M)`; that module is supported in `V(I)`, so a power of `f` kills it. -/
theorem isZero_localCohomology_zero_of_isSMulRegular (I : Ideal A) {f : A} (hf : f ∈ I)
    (M : ModuleCat.{max u v} A) (hreg : IsSMulRegular (M : Type (max u v)) f) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 0) :=
  isZero_localCohomology_succ_of_isZero_quotSMulTop.{u, v} I hf M hreg (-1) 0 (by ring)
    (isZero_localCohomologyWithSupportIn_of_neg.{u, v} _ _ (-1) (by norm_num))

/-- **`H^1_{V(I)}(M) = 0`** when `f ∈ I` is a nonzerodivisor on `M` and `g ∈ I` is a
nonzerodivisor on `M/fM`. The vanishing of `H^0_{V(I)}(M/fM)` kills the connecting map into
`H^1_{V(I)}(M)`, and the argument of the previous lemma applies one degree up. -/
theorem isZero_localCohomology_one_of_isSMulRegular (I : Ideal A) {f g : A} (hf : f ∈ I)
    (hg : g ∈ I) (M : ModuleCat.{max u v} A) (hreg : IsSMulRegular (M : Type (max u v)) f)
    (hreg' : IsSMulRegular (QuotSMulTop f (M : Type (max u v))) g) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 1) :=
  isZero_localCohomology_succ_of_isZero_quotSMulTop.{u, v} I hf M hreg 0 1 (by ring)
    (isZero_localCohomology_zero_of_isSMulRegular.{u, v} I hg
      (ModuleCat.of A (QuotSMulTop f (M : Type (max u v)))) hreg')

/-- **Depth at least two kills `H^0` and `H^1`.** Let `A` be Noetherian, `I ⊆ A` an ideal and `M`
a finite `A`-module with `IM ≠ M` and `depth_I(M) ≥ 2`. Then `H^i_{V(I)}(M) = 0` for `i ≤ 1`.

This is the case `i ≤ 1` of the inequality between parts (1) and (3) of [Stacks, Lemma 0AVZ], and
it is the depth input of Hartshorne's connectedness theorem [Stacks, Lemma 0BLR]. -/
theorem isZero_localCohomology_le_one_of_two_le_depth (I : Ideal A)
    (M : ModuleCat.{max u v} A) [Module.Finite A (M : Type (max u v))]
    (hIM : I • (⊤ : Submodule A (M : Type (max u v))) ≠ ⊤)
    (hdepth : 2 ≤ Module.depth A I (M : Type (max u v))) (i : ℤ) (hi : i ≤ 1) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  have hnt : Nontrivial (M : Type (max u v)) := by
    rcases subsingleton_or_nontrivial (M : Type (max u v)) with hsub | h
    · refine absurd ?_ hIM
      refine top_unique fun x _ ↦ ?_
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    · exact h
  obtain ⟨ss, hssI, hssreg, hsslen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I
      (M : Type (max u v))).2 hIM [] (by simp)
      (RingTheory.Sequence.IsRegular.nil A _)
  rw [List.nil_append] at hssreg hsslen
  have hlen : 2 ≤ ss.length := by
    have : ((2 : ℕ) : ℕ∞) ≤ (ss.length : ℕ∞) := hsslen ▸ hdepth
    exact_mod_cast this
  match ss, hssreg, hssI, hlen with
  | f :: g :: t, hssreg, hssI, _ =>
    rw [RingTheory.Sequence.isRegular_cons_iff, RingTheory.Sequence.isRegular_cons_iff] at hssreg
    obtain ⟨hregf, hregg, -⟩ := hssreg
    have hfI : f ∈ I := hssI f (by simp)
    have hgI : g ∈ I := hssI g (by simp)
    rcases lt_or_ge i 0 with hneg | hpos
    · exact isZero_localCohomologyWithSupportIn_of_neg.{u, v} _ M i hneg
    · interval_cases i
      · exact isZero_localCohomology_zero_of_isSMulRegular.{u, v} I hfI M hregf
      · exact isZero_localCohomology_one_of_isSMulRegular.{u, v} I hfI hgI M hregf hregg

/-- **The depth form for a Noetherian local ring.** If `A` is a Noetherian local ring with
`depth(A) ≥ 2`, then `H^0_𝔪(A) = H^1_𝔪(A) = 0`.

This is the input that the proof of Hartshorne's connectedness theorem [Stacks, Lemma 0BLR] takes
from [Stacks, Lemma 0AVZ]: there one shows that a disconnected punctured spectrum forces `H^0_𝔪(A)`
or `H^1_𝔪(A)` to be nonzero, and concludes `depth(A) ≤ 1`. -/
theorem isZero_localCohomology_le_one_of_two_le_depth_local (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) (i : ℤ) (hi : i ≤ 1) :
    IsZero (localCohomologyWithSupportIn A
      (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) i) := by
  have hsmul : (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A A) =
      IsLocalRing.maximalIdeal A := by simp
  exact isZero_localCohomology_le_one_of_two_le_depth.{u, u} (IsLocalRing.maximalIdeal A)
    (ModuleCat.of A A) (by rw [hsmul]; exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top)
    hdepth i hi

end Stacks.LocalCohomology

end
