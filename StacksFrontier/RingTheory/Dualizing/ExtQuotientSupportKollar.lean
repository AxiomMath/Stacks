module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.DualExtSupportDepthCriterion
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# The support of `Ext^{-2}(A/fA, ω)` under Kollár's fourth condition

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω`, let `f ∈ 𝔪` be
a nonzerodivisor and write `Ā = A ⧸ fA`. Assume the fourth condition of [Stacks, Tag 0F2B]:

> every prime `𝔭 ∋ f` with `dim(A/𝔭) = 2` satisfies `depth(A_𝔭) ≥ 2`.

Then the support of the finite `A`-module `Ext^{-2}_A(Ā, ω)` consists of the closed point and of
finitely many primes `𝔭 ∋ f` with `dim(A/𝔭) = 1`.

## The argument

The source's. By [Stacks, Tag 0DWZ] part (4) a prime `𝔭` lies in the support of
`Ext^0 ⊕ Ext^{-1} ⊕ Ext^{-2}` exactly when `depth_{A_𝔭}(Ā_𝔭) + dim(A/𝔭) ≤ 2`, and the support of
the single summand `Ext^{-2}` is contained in that of the sum because the projection onto that
summand is surjective. So for `𝔭` in the support

`depth_{A_𝔭}(Ā_𝔭) + dim(A/𝔭) ≤ 2`.

The depth of the zero module is `⊤`, so the inequality already forces `Ā_𝔭 ≠ 0`, that is
`𝔭 ∈ Supp(Ā) = Supp(A) ∩ V(f)`, whence `f ∈ 𝔭`. If moreover `𝔭` is not the closed point then
`dim(A/𝔭) ≥ 1`, so `dim(A/𝔭)` is `1` or `2`, and `2` is impossible: it forces
`depth_{A_𝔭}(Ā_𝔭) = 0`, while `Ā_𝔭 ≅ A_𝔭 ⧸ f A_𝔭` and `f` stays a nonzerodivisor of `A_𝔭`, so
[Stacks, Tag 090R] over `A_𝔭` gives `depth(A_𝔭) = depth(A_𝔭 ⧸ f A_𝔭) + 1 = 1`, contradicting the
fourth condition. Finally a prime `𝔭 ≠ 𝔪` of the support is minimal over the annihilator of
`Ext^{-2}`: a prime `𝔮 ⊆ 𝔭` of the support with `𝔮 ≠ 𝔭` would have `dim(A/𝔮) ≥ dim(A/𝔭) + 1 = 2`
and would not be the closed point either, which the previous paragraph forbids. The minimal
primes over an ideal of a Noetherian ring are finitely many.

## Main results

* `Dualizing.mem_support_pi_moduleExtInto_of_mem_support_moduleExtInto` — the support of one dual
  Ext module is contained in the support of the partial sum of the dual Ext modules up to its
  degree.
* `Dualizing.depth_add_coheight_le_of_mem_support_moduleExtInto` — [Stacks, Tag 0DWZ] part (4)
  read on a single dual Ext module, with the dimension of `A/𝔭` spelled as the coheight of `𝔭`.
* `Dualizing.support_quotient_span_singleton` — `Supp(A ⧸ fA) = Supp(A) ∩ V(f)`.
* `Dualizing.localizedModuleQuotientSpanEquiv` — the localization of `A ⧸ fA` at a prime `𝔭` is
  `A_𝔭 ⧸ f A_𝔭`.
* `Dualizing.depth_localizedModule_quotient_span_add_one_eq` — [Stacks, Tag 090R] for that
  quotient over `A_𝔭`.
* `Dualizing.mem_of_mem_support_moduleExtInto_quotient` — every prime of the support contains `f`.
* `Dualizing.ringKrullDim_quotient_eq_one_of_mem_support_moduleExtInto_quotient` — every prime of
  the support other than the closed point has one-dimensional quotient.
* `Dualizing.finite_support_moduleExtInto_quotient_diff_closedPoint` — the support minus the
  closed point is finite.

## Implementation notes

`Ext^{-i}_A(M, ω)` is `Dualizing.moduleExtInto M ω (-i)` and the partial sum
`Ext^0 ⊕ ⋯ ⊕ Ext^{-i}` is the dependent product over `Fin (i + 1)`, the spelling [Stacks, Tag
0DWZ] part (4) is stated at in this library. The projection onto the last factor is
`LinearMap.proj (Fin.last i)`, whose target is literally the `i`-th dual Ext module because
`(Fin.last i).val` reduces to `i`.

The hypothesis `h4` is phrased with `Module.depth (Localization.AtPrime 𝔭) _ (Localization.AtPrime
𝔭)` and the conclusion of [Stacks, Tag 0DWZ] part (4) with `LocalizedModule 𝔭.primeCompl (A ⧸ fA)`;
`Dualizing.localizedModuleQuotientSpanEquiv` bridges the two. It is built from
`Submodule.toLocalizedQuotient'`, which exhibits `A_𝔭 ⧸ (fA)_𝔭` as a localization of `A ⧸ fA`, and
is upgraded from an `A`-linear to an `A_𝔭`-linear equivalence by
`IsLocalization.linearMap_compatibleSMul`, since `Module.depth` over `A_𝔭` is only invariant under
`A_𝔭`-linear equivalences.

Dimensions of quotients are compared through coheights in `Spec(A)`: `ringKrullDim (A ⧸ 𝔭)` lives
in `WithBot ℕ∞` while depth lives in `ℕ∞`, and `Order.coheight_add_one_le` is the strict
monotonicity used for the minimality argument.

## References

* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public section

open CategoryTheory
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### The support of a single dual Ext module -/

/-- The support of `Ext^{-i}(M, K)` is contained in the support of the partial sum
`Ext^0(M, K) ⊕ ⋯ ⊕ Ext^{-i}(M, K)`, because the projection onto the last factor is surjective. -/
theorem mem_support_pi_moduleExtInto_of_mem_support_moduleExtInto
    {A : Type u} {M : Type (max v u)} [CommRing A] [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℕ) (p : PrimeSpectrum A)
    (hp : p ∈ Module.support A (moduleExtInto M K (-(i : ℤ)))) :
    p ∈ Module.support A ((j : Fin (i + 1)) → moduleExtInto M K (-(j : ℤ))) := by
  classical
  refine Module.support_subset_of_surjective
    (LinearMap.proj (R := A) (ι := Fin (i + 1))
      (φ := fun j : Fin (i + 1) => moduleExtInto M K (-(j : ℤ))) (Fin.last i))
    (fun y => ⟨Pi.single (Fin.last i) y, Pi.single_eq_same _ _⟩) hp

/-- **[Stacks, Tag 0DWZ] part (4) for a single dual Ext module.** If `𝔭` lies in the support of
`Ext^{-i}(M, ω)` then `depth_{A_𝔭}(M_𝔭) + dim(A/𝔭) ≤ i`, with `dim(A/𝔭)` read as the coheight of
`𝔭` in `Spec(A)` so that both summands live in `ℕ∞`. -/
theorem depth_add_coheight_le_of_mem_support_moduleExtInto
    {A : Type u} {M : Type (max v u)} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsNormalizedDualizingComplex.{u, v} K)
    (i : ℕ) (p : PrimeSpectrum A)
    (hp : p ∈ Module.support A (moduleExtInto M K (-(i : ℤ)))) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) + Order.coheight p ≤ (i : ℕ∞) := by
  have h := (mem_support_pi_moduleExtInto_iff_depth_add_ringKrullDim_le.{u, v} K hK p i).mp
    (mem_support_pi_moduleExtInto_of_mem_support_moduleExtInto.{u, v} K i p hp)
  rw [← coheight_eq_ringKrullDim_quotient p] at h
  exact_mod_cast h

/-! ### The quotient by a principal ideal -/

/-- **The support of `A ⧸ fA`** is the intersection of the support of `A` with the zero locus of
`f`; in particular every prime in it contains `f`. -/
theorem support_quotient_span_singleton {A : Type u} [CommRing A] (f : A) :
    Module.support A (A ⧸ Ideal.span {f}) =
      Module.support A A ∩ PrimeSpectrum.zeroLocus {f} :=
  (Submodule.quotEquivOfEq _ _ (show f • (⊤ : Submodule A A) = Ideal.span {f} by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul,
        Ideal.mul_top])).support_eq.symm.trans
    (Module.support_quotSMulTop (M := A) f)

/-- **Localizing `A ⧸ fA` at a prime `𝔭` gives `A_𝔭 ⧸ f A_𝔭`.** The quotient of the localization
is a localization of the quotient by `Submodule.toLocalizedQuotient'`, and the localized ideal
`(fA)_𝔭` is the ideal generated by the image of `f`.

The equivalence is `A_𝔭`-linear, not merely `A`-linear: an `A`-linear map between modules over
the localization is automatically linear over the localization, which is
`IsLocalization.linearMap_compatibleSMul`. -/
noncomputable def localizedModuleQuotientSpanEquiv {A : Type u} [CommRing A] (f : A)
    (p : Ideal A) [p.IsPrime] :
    LocalizedModule p.primeCompl (A ⧸ Ideal.span {f}) ≃ₗ[Localization.AtPrime p]
      QuotSMulTop (algebraMap A (Localization.AtPrime p) f) (Localization.AtPrime p) :=
  have hloc : (Ideal.span {f} : Submodule A A).localized' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap A (Localization.AtPrime p)) =
      algebraMap A (Localization.AtPrime p) f • (⊤ : Submodule (Localization.AtPrime p)
        (Localization.AtPrime p)) := by
    have hspan : (Ideal.span {f} : Submodule A A) = Submodule.span A {f} := rfl
    rw [show (algebraMap A (Localization.AtPrime p) f) •
          (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p)) =
          Ideal.span {algebraMap A (Localization.AtPrime p) f} by
        rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top],
      hspan, Submodule.localized'_span]
    simp [Ideal.span]
  ((IsLocalizedModule.linearEquiv p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (A ⧸ Ideal.span {f}))
      ((Ideal.span {f} : Submodule A A).toLocalizedQuotient' (Localization.AtPrime p)
        p.primeCompl (Algebra.linearMap A (Localization.AtPrime p)))).restrictScalars
    (Localization.AtPrime p)).trans (Submodule.quotEquivOfEq _ _ hloc)

/-- **[Stacks, Tag 090R] for `A ⧸ fA` localized at a prime `𝔭` containing `f`.** The image of a
nonzerodivisor `f ∈ 𝔭` is a nonzerodivisor of `A_𝔭` lying in its maximal ideal, so quotienting by
it drops the depth of `A_𝔭` by exactly one; the quotient is the localization of `A ⧸ fA` by
`Dualizing.localizedModuleQuotientSpanEquiv`. -/
theorem depth_localizedModule_quotient_span_add_one_eq {A : Type u} [CommRing A]
    [IsNoetherianRing A] (f : A) (p : Ideal A) [p.IsPrime] (hfp : f ∈ p)
    (hfreg : IsSMulRegular A f) :
    Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl (A ⧸ Ideal.span {f})) + 1 =
      Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) := by
  have hgm : algebraMap A (Localization.AtPrime p) f ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p f).mpr hfp
  have hgreg : IsSMulRegular (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) f) :=
    hfreg.of_isLocalization (Localization.AtPrime p) p.primeCompl
  rw [Module.depth_eq_depth_of_linearEquiv _ (localizedModuleQuotientSpanEquiv f p)]
  exact (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)).1 _ hgm hgreg

/-! ### Arithmetic in `ℕ∞` -/

/-- If `d + c ≤ 2` with `c ≠ 0`, then either `c = 1` or `c = 2` and `d = 0`. -/
private lemma eq_one_or_eq_two_and_eq_zero_of_add_le_two {d c : ℕ∞} (h : d + c ≤ 2)
    (hc : c ≠ 0) : c = 1 ∨ (c = 2 ∧ d = 0) := by
  induction d using ENat.recTopCoe with
  | top => rw [top_add] at h; simp at h
  | coe n =>
    induction c using ENat.recTopCoe with
    | top => rw [add_top] at h; simp at h
    | coe m =>
      rw [← Nat.cast_add] at h
      have h2 : n + m ≤ 2 := by exact_mod_cast h
      have hm : m ≠ 0 := by simpa using hc
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · left
        have : m = 1 := by omega
        simp [this]
      · right
        have hm2 : m = 2 := by omega
        have hn0 : n = 0 := by omega
        subst hm2
        subst hn0
        simp

/-! ### The support of `Ext^{-2}(A ⧸ fA, ω)` -/

/-- **Every prime in the support of `Ext^{-2}(A ⧸ fA, ω)` contains `f`.** By [Stacks, Tag 0DWZ]
part (4) the depth of `(A ⧸ fA)_𝔭` is at most `2`, hence finite, so `(A ⧸ fA)_𝔭` is nonzero and
`𝔭` lies in the support of `A ⧸ fA`, which is the zero locus of `f`. -/
theorem mem_of_mem_support_moduleExtInto_quotient {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω) (f : A) (p : PrimeSpectrum A)
    (hp : p ∈ Module.support A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2))) :
    f ∈ p.asIdeal := by
  have hkey := depth_add_coheight_le_of_mem_support_moduleExtInto.{u, u}
    (M := A ⧸ Ideal.span {f}) ω hω 2 p hp
  have hsupp : p ∈ Module.support A (A ⧸ Ideal.span {f}) := by
    rw [Module.mem_support_iff]
    by_contra hns
    have : Subsingleton (LocalizedModule p.asIdeal.primeCompl (A ⧸ Ideal.span {f})) :=
      not_nontrivial_iff_subsingleton.mp hns
    rw [Module.depth_eq_top_of_subsingleton, top_add] at hkey
    simp at hkey
  rw [support_quotient_span_singleton] at hsupp
  exact hsupp.2 (Set.mem_singleton f)

/-- **Every prime in the support of `Ext^{-2}(A ⧸ fA, ω)` other than the closed point has
one-dimensional quotient.** This is the step of [Stacks, Tag 0F2B] that uses the fourth condition
`h4`: by [Stacks, Tag 0DWZ] part (4) the dimension of `A/𝔭` is at most `2`, and it is at least `1`
because `𝔭` is not the closed point; were it `2`, the depth of `(A ⧸ fA)_𝔭` would vanish, so
[Stacks, Tag 090R] over `A_𝔭` would make `depth(A_𝔭) = 1`, which `h4` forbids. -/
theorem ringKrullDim_quotient_eq_one_of_mem_support_moduleExtInto_quotient {A : Type u}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω) (f : A)
    (_hfm : f ∈ IsLocalRing.maximalIdeal A) (hfreg : IsSMulRegular A f)
    (h4 : ∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
      2 ≤ Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
    (p : PrimeSpectrum A)
    (hp : p ∈ Module.support A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)))
    (hpne : p ≠ IsLocalRing.closedPoint A) :
    ringKrullDim (A ⧸ p.asIdeal) = 1 := by
  have hfp : f ∈ p.asIdeal := mem_of_mem_support_moduleExtInto_quotient ω hω f p hp
  have hkey := depth_add_coheight_le_of_mem_support_moduleExtInto.{u, u}
    (M := A ⧸ Ideal.span {f}) ω hω 2 p hp
  have hle : p ≤ IsLocalRing.closedPoint A :=
    IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal
  have hcne : Order.coheight p ≠ 0 :=
    Order.coheight_ne_zero.mpr fun hmax => hpne (le_antisymm hle (hmax hle))
  rcases eq_one_or_eq_two_and_eq_zero_of_add_le_two hkey hcne with hc1 | ⟨hc2, hd0⟩
  · rw [← coheight_eq_ringKrullDim_quotient p, hc1]
    rfl
  · exfalso
    have hdim2 : ringKrullDim (A ⧸ p.asIdeal) = 2 := by
      rw [← coheight_eq_ringKrullDim_quotient p, hc2]
      rfl
    have h090 := depth_localizedModule_quotient_span_add_one_eq f p.asIdeal hfp hfreg
    rw [hd0, zero_add] at h090
    have hbad := h4 p.asIdeal p.isPrime hfp hdim2
    rw [← h090] at hbad
    simp at hbad

/-- **The support of `Ext^{-2}(A ⧸ fA, ω)` is finite away from the closed point.** Such a prime
`𝔭` is minimal over the annihilator of `Ext^{-2}(A ⧸ fA, ω)`: a prime of the support strictly
inside `𝔭` would be distinct from the closed point and would have `dim(A/·) ≥ 2`, contradicting
`Dualizing.ringKrullDim_quotient_eq_one_of_mem_support_moduleExtInto_quotient`. An ideal of a
Noetherian ring has finitely many minimal primes over it. -/
theorem finite_support_moduleExtInto_quotient_diff_closedPoint {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω) (f : A)
    (hfm : f ∈ IsLocalRing.maximalIdeal A) (hfreg : IsSMulRegular A f)
    (h4 : ∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
      2 ≤ Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) :
    (Module.support A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) \
      {IsLocalRing.closedPoint A}).Finite := by
  classical
  have hfin : Module.Finite A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) :=
    moduleExtInto_finite.{u, u} (M := A ⧸ Ideal.span {f}) ω hω 2
  have hsub : Module.support A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) \
      {IsLocalRing.closedPoint A} ⊆ PrimeSpectrum.asIdeal ⁻¹'
        (Module.annihilator A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2))).minimalPrimes := by
    rintro q ⟨hq, hqne⟩
    simp only [Set.mem_singleton_iff] at hqne
    obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
      (Module.annihilator_le_of_mem_support hq)
    have hrp : r.IsPrime := hr.1.1
    have hrsupp : (⟨r, hrp⟩ : PrimeSpectrum A) ∈
        Module.support A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) :=
      Module.mem_support_iff_of_finite.mpr hr.1.2
    have hrne : (⟨r, hrp⟩ : PrimeSpectrum A) ≠ IsLocalRing.closedPoint A := by
      intro hrc
      refine hqne (PrimeSpectrum.ext (le_antisymm ?_ ?_))
      · exact IsLocalRing.le_maximalIdeal_of_isPrime q.asIdeal
      · exact le_trans (le_of_eq (congrArg PrimeSpectrum.asIdeal hrc).symm) hrq
    have hcoh : ∀ s : PrimeSpectrum A,
        s ∈ Module.support A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) →
        s ≠ IsLocalRing.closedPoint A → Order.coheight s = 1 := fun s hs hsne => by
      have := (coheight_eq_ringKrullDim_quotient s).trans
        (ringKrullDim_quotient_eq_one_of_mem_support_moduleExtInto_quotient ω hω f hfm hfreg h4
          s hs hsne)
      exact_mod_cast this
    have hcq := hcoh q hq hqne
    have hcr := hcoh ⟨r, hrp⟩ hrsupp hrne
    rcases eq_or_lt_of_le (show (⟨r, hrp⟩ : PrimeSpectrum A) ≤ q from hrq) with heq | hlt
    · rw [Set.mem_preimage, ← congrArg PrimeSpectrum.asIdeal heq]
      exact hr
    · exfalso
      have hstep := Order.coheight_strictAnti hlt (by simp [hcq])
      rw [hcq, hcr] at hstep
      exact absurd hstep (lt_irrefl 1)
  exact Set.Finite.subset
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A
      (Module.annihilator A (moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)))).preimage
      fun _ _ _ _ h => PrimeSpectrum.ext h) hsub

end Dualizing

end
