module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Data.ENat.Monoid
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Serre.Criterion
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# Serre's condition on an effective Cartier divisor

Let `X` be a locally Noetherian scheme satisfying Serre's condition `(S_k)` and let `D ⊆ X` be
an effective Cartier divisor.  Then `D` satisfies `(S_{k-1})`, provided `k ≥ 1`.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_hasPropertySk`: **Stacks Tag 0B3R.**
* `AlgebraicGeometry.hasPropertySk_two_of_isNormal`: a locally Noetherian normal scheme
  satisfies `(S₂)`, which is the half of Serre's criterion for normality that Tag 0B3S needs.
* `AlgebraicGeometry.isNormal_effectiveCartierDivisor_hasPropertySk_one`: **Stacks Tag 0B3S.**

## The argument

`(S_k)` is the pointwise inequality `min (k, dim 𝒪) ≤ depth 𝒪` on stalks, so the statement is
local.  At a point `y` of `D` with image `x` in `X`, Tag 01WS
(`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`) gives an affine chart `U` on which
`D` is `Spec (A / (f))` with `A = Γ(X, U)` and `f` a nonzerodivisor, and the stalk of `D` at `y`
becomes the localization of `A / (f)` at the prime of `y`, which is the quotient of `R = 𝒪_{X,x}`
by the image of `f`.  Dividing a Noetherian local ring by a nonzerodivisor of the maximal ideal
drops both the depth and the Krull dimension by exactly one
(`Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` and
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`), and
`min (k, ·)` commutes with `· + 1`, so the inequality at `x` for `k` becomes the inequality at
`y` for `k - 1`.

## Implementation notes

The closed subscheme `D` is locally Noetherian because its inclusion is a closed immersion, hence
locally of finite type, into a locally Noetherian scheme
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`); that instance has to be supplied
explicitly in the statement, since `HasPropertySk` takes it as an instance argument.

Transporting the inequality through the chart is done by the two congruence lemmas
`hasPropertySkAt_iff_of_ringEquiv` and `hasPropertySkAt_iff_of_stalkMap`, which say the pointwise
form of `(S_k)` only depends on the local ring up to isomorphism, respectively is invariant along
a morphism inducing an isomorphism on the stalk.

## References

* [Stacks Project, Tag 0B3R](https://stacks.math.columbia.edu/tag/0B3R)
* [Stacks Project, Tag 0B3S](https://stacks.math.columbia.edu/tag/0B3S)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors
open scoped Pointwise

universe u

namespace AlgebraicGeometry



private def hasPropertySkAt (Y : Scheme.{u}) (y : Y) (k : ℕ) : Prop :=
  min (k : WithBot ℕ∞) (ringKrullDim (Y.presheaf.stalk y)) ≤
    (Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) : WithBot ℕ∞)

private alias hasPropertySkAt_iff_of_ringEquiv := minDepth_iff_of_ringEquiv

private lemma hasPropertySkAt_iff_of_stalkMap {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (y : Y) [IsIso (f.stalkMap y)] (k : ℕ) :
    hasPropertySkAt Y y k ↔ hasPropertySkAt Z (f y) k :=
  hasPropertySkAt_iff_of_ringEquiv k (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.symm

private noncomputable def localizationAtPrimeQuotientEquiv {A : Type*} [CommRing A]
    (J : Ideal A) (q : Ideal (A ⧸ J)) [q.IsPrime] :
    (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))) ⧸
        J.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)))) ≃+*
      Localization.AtPrime q := by
  let p := q.comap (Ideal.Quotient.mk J)
  let _ : p.IsPrime := inferInstance
  have hsub : Submonoid.map (Ideal.Quotient.mk J) p.primeCompl = q.primeCompl := by
    change Submonoid.map (Ideal.Quotient.mk J)
      (Submonoid.comap (Ideal.Quotient.mk J) q.primeCompl) = q.primeCompl
    exact Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective q.primeCompl
  let _ : IsLocalization (Submonoid.map (Ideal.Quotient.mk J) p.primeCompl)
      (Localization.AtPrime q) := by
    rw [hsub]
    infer_instance
  let ψ : Localization.AtPrime p →+* Localization.AtPrime q :=
    IsLocalization.map (M := p.primeCompl) (Localization.AtPrime q)
      (Ideal.Quotient.mk J)
      (Submonoid.le_comap_map _)
  have hsurj : Function.Surjective ψ :=
    IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q) (g := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ψ = J.map (algebraMap A (Localization.AtPrime p)) := by
    change RingHom.ker (IsLocalization.map (Localization.AtPrime q)
      (Ideal.Quotient.mk J) (Submonoid.le_comap_map _)) = _
    rw [IsLocalization.ker_map (Localization.AtPrime q)
      (Ideal.Quotient.mk J) rfl]
    simp [Ideal.mk_ker]
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

/-- The quotient of a local ring by a principal ideal generated by a non-unit is local. -/
private lemma isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {f}) :=
  have : Nontrivial (R ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_of_lt (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hf))
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top))
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private lemma hasPropertySk_quotient_span_singleton {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (k : ℕ) (hk : 1 ≤ k) (f : R)
    (hf : f ∈ IsLocalRing.maximalIdeal R) (hfreg : f ∈ nonZeroDivisors R)
    [IsLocalRing (R ⧸ Ideal.span {f})]
    (hR : min (k : WithBot ℕ∞) (ringKrullDim R) ≤
      (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞)) :
    min ((k - 1 : ℕ) : WithBot ℕ∞) (ringKrullDim (R ⧸ Ideal.span {f})) ≤
      (Module.depth (R ⧸ Ideal.span {f})
        (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {f})) (R ⧸ Ideal.span {f}) : WithBot ℕ∞) := by
  classical
  let Q := R ⧸ Ideal.span {f}
  have hspan : (f • (⊤ : Submodule R R) : Submodule R R) = Ideal.span {f} := by
    rw [← Submodule.ideal_span_singleton_smul]
    simp
  let e : QuotSMulTop f R ≃ₗ[R] Q :=
    Submodule.quotEquivOfEq _ _ hspan
  have hdrop := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal R) R).1 f hf
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hfreg)
  have hdrop' : Module.depth R (IsLocalRing.maximalIdeal R) Q + 1 =
      Module.depth R (IsLocalRing.maximalIdeal R) R := by
    rwa [← Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal R) e]
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R Q) = IsLocalRing.maximalIdeal Q := by
    simpa only [Q, Ideal.Quotient.algebraMap_eq] using
      IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective
  have hdropQ : Module.depth Q (IsLocalRing.maximalIdeal Q) Q + 1 =
      Module.depth R (IsLocalRing.maximalIdeal R) R := by
    rw [← hmax, ← Module.depth_eq_depth_map_algebraMap Ideal.Quotient.mk_surjective, hdrop']
  have hdim : ringKrullDim Q + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      hfreg hf
  have hdropQB :
      (Module.depth Q (IsLocalRing.maximalIdeal Q) Q : WithBot ℕ∞) + 1 =
        (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) :=
    mod_cast hdropQ
  have hkcast : (k : WithBot ℕ∞) = ((k - 1 : ℕ) : WithBot ℕ∞) + 1 :=
    mod_cast (Nat.sub_add_cancel hk).symm
  have hbound : min ((k - 1 : ℕ) : WithBot ℕ∞) (ringKrullDim Q) + 1 ≤
      (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) := by
    calc
      _ = min (((k - 1 : ℕ) : WithBot ℕ∞) + 1) (ringKrullDim Q + 1) :=
        (min_add_add_right _ _ _).symm
      _ = min (k : WithBot ℕ∞) (ringKrullDim R) := by rw [← hkcast, ← hdim]
      _ ≤ _ := hR
  exact ENat.WithBot.add_le_add_one_right_iff.mp (hbound.trans_eq hdropQB.symm)

/-- An effective Cartier divisor of an `(Sₖ)` locally Noetherian scheme is
`(Sₖ₋₁)` for `k ≥ 1`. -/
@[stacks 0B3R]
theorem isEffectiveCartierDivisor_hasPropertySk
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I)
    (k : ℕ) (hk : 1 ≤ k) (hX : HasPropertySk X k) :
    @HasPropertySk I.subscheme
      (LocallyOfFiniteType.isLocallyNoetherian I.subschemeι) (k - 1) := by
  show ∀ y : I.subscheme, hasPropertySkAt I.subscheme y (k - 1)
  intro y
  let x : X := I.subschemeι y
  have hxSupport : x ∈ I.supportSet := by
    rw [I.mem_supportSet_iff_mem_support]
    show x ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hxSupport
  let A := Γ(X, U)
  let mk : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk _
  let P := pullback I.subschemeι U.ι
  have hyRange : y ∈ Set.range (pullback.fst I.subschemeι U.ι).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    simpa [Scheme.Hom.opensRange] using hxU
  obtain ⟨z, hz⟩ := Set.mem_range.mp hyRange
  let u : U := (pullback.snd I.subschemeι U.ι).base z
  have hpull : (I.subschemeι.base.hom) ((pullback.fst I.subschemeι U.ι).base.hom z) =
      (U.ι.base.hom) ((pullback.snd I.subschemeι U.ι).base.hom z) := by
    have hh := congrArg (fun g : P ⟶ X => g.base.hom z)
      (pullback.condition (f := I.subschemeι) (g := U.ι))
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using hh
  have hu : (u : X) = x := by
    show (U.ι.base.hom) ((pullback.snd I.subschemeι U.ι).base.hom z) =
      (I.subschemeι.base.hom) y
    rw [← hz]
    exact hpull.symm
  let qpt : PrimeSpectrum (A ⧸ Ideal.span {f}) := e.hom z
  have hspec : hU.primeIdealOf u = qpt.comap mk := by
    have hh := congrArg (fun g ↦ g.base.hom z) he
    show (hU.isoSpec.hom.base.hom) ((pullback.snd I.subschemeι U.ι).base.hom z) =
      (Spec.map (CommRingCat.ofHom mk)).base.hom ((e.hom).base.hom z)
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using hh
  let p : Ideal A := qpt.asIdeal.comap mk
  let _ : p.IsPrime := (qpt.comap mk).2
  let _ : IsNoetherianRing A :=
    (inferInstance : IsLocallyNoetherian X).component_noetherian ⟨U, hU⟩
  let _ : Algebra A (X.presheaf.stalk (u : X)) :=
    X.presheaf.algebra_section_stalk ⟨(u : X), u.2⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk (u : X)) p := by
    show IsLocalization.AtPrime (X.presheaf.stalk (u : X)) (qpt.comap mk).asIdeal
    simpa only [← hspec] using hU.isLocalization_stalk u
  let R := Localization.AtPrime p
  let eX := IsLocalization.algEquiv p.primeCompl R (X.presheaf.stalk (u : X))
  have hXu : hasPropertySkAt X (u : X) k := by rw [hu]; exact hX x
  have hR : min (k : WithBot ℕ∞) (ringKrullDim R) ≤
      (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) :=
    (hasPropertySkAt_iff_of_ringEquiv k eX.toRingEquiv).mpr hXu
  let fR : R := algebraMap A R f
  have hfmax : fR ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R p f).2 (by
      show mk f ∈ qpt.asIdeal
      simp [mk])
  have hfreg : fR ∈ nonZeroDivisors R :=
    IsLocalization.map_nonZeroDivisors_le p.primeCompl R
      (Submonoid.mem_map.mpr ⟨f, isRegular_iff_mem_nonZeroDivisors.mp hf, rfl⟩)
  let Q := R ⧸ Ideal.span {fR}
  have _ : IsLocalRing Q := isLocalRing_quotient_span_singleton hfmax
  have hRQ := hasPropertySk_quotient_span_singleton k hk fR hfmax hfreg hR
  let eQ : Q ≃+* Localization.AtPrime qpt.asIdeal := by
    have hspan : (Ideal.span {f}).map (algebraMap A R) = Ideal.span {fR} := by
      simp [Ideal.map_span, fR]
    exact (Ideal.quotEquivOfEq hspan.symm).trans
      (localizationAtPrimeQuotientEquiv (Ideal.span {f}) qpt.asIdeal)
  have hSpec : hasPropertySkAt (Spec (.of (A ⧸ Ideal.span {f}))) qpt (k - 1) :=
    (hasPropertySkAt_iff_of_ringEquiv (k - 1)
      (Spec.stalkIso (.of (A ⧸ Ideal.span {f})) qpt).commRingCatIsoToRingEquiv).mpr
        ((hasPropertySkAt_iff_of_ringEquiv (k - 1) eQ).mp hRQ)
  simpa only [hz] using
    (hasPropertySkAt_iff_of_stalkMap (pullback.fst I.subschemeι U.ι) z (k - 1)).mp
      ((hasPropertySkAt_iff_of_stalkMap e.hom z (k - 1)).mpr hSpec)

/-- **A locally Noetherian normal scheme satisfies Serre's condition `(S₂)`.**  This is one half
of Serre's criterion for normality, Tag 031S, transported from the ring of sections of an affine
open to the stalk: both sides of the defining inequality only depend on the local ring, and the
stalk at a point of an affine open `U` is a localization of `Γ(X, U)` at a prime. -/
@[ega "IV 5.8.6" "necessity of (S2)", ega "IV 7.3.9" "normality implies S2"]
theorem hasPropertySk_two_of_isNormal (X : Scheme.{u}) [IsLocallyNoetherian X] [IsNormal X] :
    HasPropertySk X 2 := by
  intro x
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  have hnormal : IsNormalRing Γ(X, U) :=
    ((isNormal_tfae X).out 1 2 rfl rfl).mp inferInstance U
  have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hS2 :=
    (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
      (R := Γ(X, U))).mp (isNormalRing_iff.mp hnormal) |>.2
  have hprime : (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime :=
    (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
  let _ := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U.1)
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x)
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
  have e : Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
  refine (hasPropertySkAt_iff_of_ringEquiv 2 e).mp ?_
  simpa using hS2 (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- **Stacks Project, Tag 0B3S.**  An effective Cartier divisor on a locally Noetherian normal
scheme satisfies Serre's condition `(S₁)`: the scheme satisfies `(S₂)` by Serre's criterion, and
Tag 0B3R drops the index by one. -/
@[stacks 0B3S, ega "IV 21.7.3" "normal ⇒ (S_1)"]
theorem isNormal_effectiveCartierDivisor_hasPropertySk_one (X : Scheme.{u})
    [IsLocallyNoetherian X] [IsNormal X] (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) :
    letI : IsLocallyNoetherian I.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
    HasPropertySk I.subscheme 1 :=
  isEffectiveCartierDivisor_hasPropertySk I hI 2 (by omega) (hasPropertySk_two_of_isNormal X)

end AlgebraicGeometry

end
