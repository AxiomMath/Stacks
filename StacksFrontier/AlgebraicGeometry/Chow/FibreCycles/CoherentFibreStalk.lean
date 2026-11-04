module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentLength
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.AssociatedPointsStalk
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCoherentSheaf
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of the restriction of a coherent sheaf to a locally principal closed subscheme

Let `g : X ⟶ Y` be a closed immersion whose ideal sheaf is principal at a point `x` of `X`, with
local equation `t` in the local ring `A = 𝒪_{Y, g x}`, and let `F` be a coherent `𝒪_Y`-module
with stalk `M = F_{g x}`. The stalk of `g^* F` at `x` is `M / tM`, and its length over the local
ring of `X` is the length of `M / tM` over `A`. When the maximal ideal of `A` is not an
associated prime of `M` and `M / tM` has finite length, the module form of Stacks Tag 02QG turns
that length into a sum over the minimal points of the support of `M`.

## Main results

* `Stacks.Chow.length_stalk_pullback_eq_length_quotSMulTop` — the stalk of the pullback is
  `M / tM`, at the level of lengths.
* `Stacks.Chow.sheafMultiplicity_pullback_eq_toNat_length_quotSMulTop` — the same as an identity
  of multiplicities, the shape the coefficient of a cycle is read in.
* `Stacks.Chow.mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp` — a prime of `A` lies in the
  support of `M` exactly when the corresponding point of `Y` lies in the support of `F`.
* `Stacks.Chow.minimal_moduleSupport_stalk_iff_mem_minimalPrimes_reducedSupport` — consequently
  the minimal points of the support of `M` are the minimal primes over the stalk of the ideal
  sheaf of the reduced support of `F`.
* `Stacks.Chow.notMem_associatedPrimes_stalk_of_notMem_associatedPoints` — the condition on
  associated points of `F`, read in the local ring.
* `Stacks.Chow.length_quotSMulTop_eq_finsum_minimal_support_of_notMem_associatedPrimes` — the
  module form of Stacks Tag 02QG with the hypotheses the geometry supplies: no associated prime
  at the maximal ideal, and a zero-dimensional quotient.
* `Stacks.Chow.sheafMultiplicity_pullback_eq_finsum_minimal_support` — the two put together: the
  multiplicity of `g^* F` at `x` is the sum over the minimal points of the support of `M`.

## Implementation notes

The identification of the stalk of a pullback with a tensor product is Stacks Tag 0098,
`AlgebraicGeometry.RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`. It is
stated for a morphism of ringed spaces, which spells the stalk of a sheaf of modules differently
from the way a scheme does, so the module structure on the stalk of the pullback has to be
supplied explicitly where the two spellings meet; the statements below are therefore phrased
with the instance named, exactly as
`Stacks.Chow.length_localizedModule_stalk_eq_length_stalk` is phrased without it.

Regularity of the local equation is derived rather than assumed: an associated prime of `M`
containing `t` lies in the support of `M / tM`, which is zero-dimensional, so it is the maximal
ideal — excluded by the hypothesis on associated points. With `t` regular the support of `M` is
one-dimensional, which is the hypothesis of Tag 02QG in the form
`Stacks.Chow.length_quotSMulTop_eq_sum_of_regular_of_supportDim_eq_one`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### The length of a base change along a surjection with principal kernel -/

/-- For a surjection of rings with principal kernel `(t)`, the base change of a module `M` is
`M / tM`, and the two have the same length. -/
private theorem length_tensor_eq_length_quotSMulTop {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] (t : A)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {t}) :
    Module.length B (B ⊗[A] M) = Module.length A (QuotSMulTop t M) := by
  have e : B ⊗[A] M ≃ₗ[A] M ⧸ (RingHom.ker (algebraMap A B) • (⊤ : Submodule A M)) :=
    (TensorProduct.congr
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hsurj).symm.toLinearEquiv
      (LinearEquiv.refl A M)).trans (TensorProduct.quotTensorEquivQuotSMul M _)
  rw [← Module.length_eq_of_surjective hsurj, e.length_eq, hker,
    Submodule.ideal_span_singleton_smul]

/-! ### The stalk of a pullback along a locally principal closed immersion -/

/-- **Stacks Tag 0098 at a locally principal closed immersion.** The stalk of `g^* F` at `x` has,
over the local ring of `X` at `x`, the length of `F_{g x} / t F_{g x}` over the local ring of `Y`
at `g x`, for `t` any generator of the kernel of the stalk map of `g`. -/
theorem length_stalk_pullback_eq_length_quotSMulTop {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsPreimmersion g] (F : Y.Modules) (x : X) (t : Y.presheaf.stalk (g x))
    (ht : RingHom.ker (g.stalkMap x).hom = Ideal.span {t}) :
    Module.length (X.presheaf.stalk x) (((Scheme.Modules.pullback g).obj F).presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (g x)) (QuotSMulTop t (F.presheaf.stalk (g x))) := by
  let A := Y.presheaf.stalk (g x)
  let B := X.presheaf.stalk x
  let G := (Scheme.Modules.pullback g).obj F
  let _ : Algebra A B := (g.stalkMap x).hom.toAlgebra
  obtain ⟨e, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom F x
  exact (@LinearEquiv.length_eq B (G.presheaf.stalk x) inferInstance inferInstance
    (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x) (B ⊗[A] F.presheaf.stalk (g x)) inferInstance inferInstance
    e).trans (length_tensor_eq_length_quotSMulTop t (g.stalkMap_surjective x) ht)

/-- The multiplicity of `g^* F` at `x` is the colength of a local equation of `g` on the stalk of
`F` at `g x`: the integer form of
`Stacks.Chow.length_stalk_pullback_eq_length_quotSMulTop`. -/
theorem sheafMultiplicity_pullback_eq_toNat_length_quotSMulTop {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsPreimmersion g] (F : Y.Modules) (x : X) (t : Y.presheaf.stalk (g x))
    (ht : RingHom.ker (g.stalkMap x).hom = Ideal.span {t}) :
    sheafMultiplicity ((Scheme.Modules.pullback g).obj F) x =
      ((Module.length (Y.presheaf.stalk (g x))
        (QuotSMulTop t (F.presheaf.stalk (g x)))).toNat : ℤ) :=
  congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (length_stalk_pullback_eq_length_quotSMulTop g F x t ht)

/-- A local equation of a closed immersion lies in the maximal ideal: it is killed by the stalk
map, which lands in a nonzero ring. -/
theorem mem_maximalIdeal_of_span_eq_ker_stalkMap {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (t : Y.presheaf.stalk (g x)) (ht : RingHom.ker (g.stalkMap x).hom = Ideal.span {t}) :
    t ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g x)) := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro hunit
  have ht0 : (g.stalkMap x).hom t = 0 :=
    RingHom.mem_ker.mp (ht ▸ Ideal.subset_span (Set.mem_singleton t))
  exact not_isUnit_zero (ht0 ▸ hunit.map (g.stalkMap x).hom)

/-! ### The support of a stalk and the support of the sheaf -/

/-- **A prime of `𝒪_{Y, ξ}` lies in the support of `F_ξ` exactly when the point of `Y` it names
lies in the support of `F`.** Both sides say that the localization of `F_ξ` at the prime is
nonzero, the right-hand one through the identification of that localization with the stalk of `F`
at the point. -/
theorem mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsQuasicoherent] {ξ : Y} (q : PrimeSpectrum (Y.presheaf.stalk ξ)) :
    q ∈ Module.support (Y.presheaf.stalk ξ) (F.presheaf.stalk ξ) ↔
      Y.fromSpecStalk ξ q ∈ SheafOfModules.supp F := by
  have h : Y.fromSpecStalk ξ q ⤳ ξ := Scheme.range_fromSpecStalk.subset ⟨q, rfl⟩
  let _ : Algebra (Y.presheaf.stalk ξ) (Y.presheaf.stalk (Y.fromSpecStalk ξ q)) :=
    (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc : IsLocalization.AtPrime
      (Y.presheaf.stalk (Y.fromSpecStalk ξ q)) q.asIdeal :=
    isLocalization_stalk_of_specializes h q rfl
  let _ := Stacks.ModuleStalkSpecialization.stalkModule F ξ
  let _ := Stacks.ModuleStalkSpecialization.stalkModule F (Y.fromSpecStalk ξ q)
  let _ := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
  have hmod : IsLocalizedModule.AtPrime q.asIdeal
      (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_of_eq
      (IsLocalization.AtPrime.under_maximalIdeal _ _)
      (Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F h)
  refine (Module.mem_support_iff (p := q)).trans (Iff.trans ?_
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F (Y.fromSpecStalk ξ q)).symm)
  exact (IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
    (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h)
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl
      (F.presheaf.stalk ξ))).toEquiv.nontrivial_congr.symm

/-- **The minimal points of the support of the stalk are the minimal primes over the stalk of the
ideal sheaf of the reduced support.** The two sets of primes coincide by
`Stacks.Chow.mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp`, and every prime of the local
ring is prime, so the two notions of minimality agree. -/
theorem minimal_moduleSupport_stalk_iff_mem_minimalPrimes_reducedSupport {Y : Scheme.{u}}
    (F : Y.Modules) [F.IsCoherent] {ξ : Y} (q : PrimeSpectrum (Y.presheaf.stalk ξ)) :
    Minimal (· ∈ Module.support (Y.presheaf.stalk ξ) (F.presheaf.stalk ξ)) q ↔
      q.asIdeal ∈ (IdealSheafData.stalk (reducedSupport F) ξ).minimalPrimes := by
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hiff : ∀ p : PrimeSpectrum (Y.presheaf.stalk ξ),
      p ∈ Module.support (Y.presheaf.stalk ξ) (F.presheaf.stalk ξ) ↔
        IdealSheafData.stalk (reducedSupport F) ξ ≤ p.asIdeal := by
    intro p
    rw [mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp F p,
      le_iff_fromSpecStalk_mem_support, coe_support_reducedSupport]
  constructor
  · exact fun hq => ⟨⟨q.isPrime, (hiff q).mp hq.1⟩, fun p hp hpq =>
      hq.2 (y := ⟨p, hp.1⟩) ((hiff ⟨p, hp.1⟩).mpr hp.2) hpq⟩
  · exact fun hq => ⟨(hiff q).mpr hq.1.2, fun p hp hpq =>
      hq.2 ⟨p.isPrime, (hiff p).mp hp⟩ hpq⟩

/-! ### The condition on associated points in the local ring -/

/-- The condition on associated points, read in the local ring: if `ξ` is not an associated point
of `F`, the maximal ideal of `𝒪_{Y, ξ}` is not an associated prime of `F_ξ`. -/
theorem notMem_associatedPrimes_stalk_of_notMem_associatedPoints {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (F : Y.Modules) (ξ : Y)
    (hξ : ξ ∉ Stacks.Divisors.associatedPoints F) :
    IsLocalRing.maximalIdeal (Y.presheaf.stalk ξ) ∉
      associatedPrimes (Y.presheaf.stalk ξ) (F.presheaf.stalk ξ) := by
  intro h
  obtain ⟨hp, z, hz⟩ := isAssociatedPrime_iff.mp h
  refine hξ ⟨hp, z, ?_⟩
  rw [Submodule.colon_span]
  exact hz.symm

/-! ### The local length identity -/

/-- A prime in the support of `M` that contains `t` lies in the support of `M / tM`. -/
private theorem mem_support_quotSMulTop_of_mem {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (t : R) {p : PrimeSpectrum R} (hp : p ∈ Module.support R M)
    (htp : t ∈ p.asIdeal) : p ∈ Module.support R (QuotSMulTop t M) := by
  rw [Module.support_quotSMulTop]
  exact ⟨hp, by simpa using htp⟩

/-- A local equation whose quotient is zero-dimensional is a nonzerodivisor, once the maximal
ideal is not an associated prime: an associated prime containing `t` lies in the support of
`M / tM`, which is the maximal ideal alone. -/
theorem isSMulRegular_of_notMem_associatedPrimes_of_supportDim_quotSMulTop_eq_zero
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (t : R)
    (hM : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M)
    (hquot : Module.supportDim R (QuotSMulTop t M) = 0) :
    IsSMulRegular M t := by
  by_contra hreg
  have hmem : t ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact hreg
  obtain ⟨p, hp, htp⟩ := Set.mem_iUnion₂.mp hmem
  have hann : Module.annihilator R M ≤ p := by
    have h := hp.annihilator_le
    rwa [Submodule.annihilator_top] at h
  have hpsupp : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈
      Module.support R (QuotSMulTop t M) := by
    refine mem_support_quotSMulTop_of_mem t ?_ htp
    rw [Module.support_eq_zeroLocus]
    exact hann
  rw [support_of_supportDim_eq_zero R _ hquot, PrimeSpectrum.zeroLocus_eq_singleton] at hpsupp
  have hpm : p = IsLocalRing.maximalIdeal R := congrArg PrimeSpectrum.asIdeal hpsupp
  exact hM (hpm ▸ hp)

/-- **The module form of Stacks Tag 02QG with the hypotheses the geometry supplies.** For a finite
module `M` over a Noetherian local ring and an element `t` of the maximal ideal with `M / tM`
zero-dimensional and the maximal ideal not an associated prime of `M`, the length of `M / tM` is
the sum, over the minimal points `q` of the support of `M`, of the colength of `(t, q)` times the
length of `M` localized at `q`. -/
@[ega "IV 3.4.1.2" "special case"]
theorem length_quotSMulTop_eq_finsum_minimal_support_of_notMem_associatedPrimes
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (t : R)
    (ht : t ∈ IsLocalRing.maximalIdeal R)
    (hM : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M)
    (hquot : Module.supportDim R (QuotSMulTop t M) = 0) :
    Module.length R (QuotSMulTop t M) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        Module.length R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
  have hregular :=
    isSMulRegular_of_notMem_associatedPrimes_of_supportDim_quotSMulTop_eq_zero t hM hquot
  have hdim : Module.supportDim R M = 1 := by
    have h := Module.supportDim_quotSMulTop_succ_eq_supportDim hregular ht
    rw [hquot, zero_add] at h
    exact h.symm
  exact length_quotSMulTop_eq_sum_of_regular_of_supportDim_eq_one t hregular ht hdim

/-- At a point of the support, the colength of a local equation together with that point is
finite once the quotient by the local equation has zero-dimensional support. -/
private theorem length_quotient_span_sup_ne_top {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (t : R)
    (hquot : Module.supportDim R (QuotSMulTop t M) ≤ 0) (q : PrimeSpectrum R)
    (hq : q ∈ Module.support R M) :
    Module.length R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) ≠ ⊤ := by
  refine Module.length_ne_top_iff.mpr (AlgebraicGeometry.finite_length_of_supportDim_le_zero ?_)
  have hs : Module.support R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) ⊆
      Module.support R (QuotSMulTop t M) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    intro p hp
    have hp' : Ideal.span {t} ⊔ q.asIdeal ≤ p.asIdeal := hp
    exact mem_support_quotSMulTop_of_mem t
      (Module.mem_support_mono (le_sup_right.trans hp') hq)
      (hp' (Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)))
  exact (Order.krullDim_le_of_strictMono
    (fun p : Module.support R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) =>
      (⟨p.val, hs p.property⟩ : Module.support R (QuotSMulTop t M)))
    (fun _ _ h => h)).trans hquot

/-- The local length identity of Stacks Tag 02QG read in the integers: the minimal points of the
support are finite in number and every summand is finite, so `ENat.toNat` distributes over the
sum and over each product. -/
theorem toNat_finsum_minimal_support {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (t : R)
    (hquot : Module.supportDim R (QuotSMulTop t M) ≤ 0) :
    (((∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        Module.length R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        ((Module.length R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) := by
  have hfin : {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q}.Finite :=
    AlgebraicGeometry.finite_minimal_support
  have hterms : ∀ q ∈ hfin.toFinset, Module.length R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) *
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := fun q hq =>
    WithTop.mul_ne_top
      (length_quotient_span_sup_ne_top t hquot q (hfin.mem_toFinset.mp hq).1)
      (AlgebraicGeometry.localized_length_ne_top q (hfin.mem_toFinset.mp hq))
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    ENat.toNat_sum hterms, Nat.cast_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [ENat.toNat_mul, Nat.cast_mul]

/-! ### The multiplicity of a restriction as a sum over the support of the stalk -/

/-- The quotient of the stalk of `F` at `g x` by a local equation of `g` has zero-dimensional
support as soon as the stalk of `g^* F` at `x` has finite length: the two have the same length,
by `Stacks.Chow.length_stalk_pullback_eq_length_quotSMulTop`, and a nonzero module of finite
length over a local ring is supported at the closed point alone. -/
theorem supportDim_quotSMulTop_stalk_eq_zero_of_isFiniteLength {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsPreimmersion g] (F : Y.Modules) [F.IsCoherent] (x : X)
    (t : Y.presheaf.stalk (g x)) (ht : RingHom.ker (g.stalkMap x).hom = Ideal.span {t})
    (hx : x ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F))
    (hfin : IsFiniteLength (X.presheaf.stalk x)
      (((Scheme.Modules.pullback g).obj F).presheaf.stalk x)) :
    Module.supportDim (Y.presheaf.stalk (g x))
      (QuotSMulTop t (F.presheaf.stalk (g x))) = 0 := by
  have _ : Module.Finite (Y.presheaf.stalk (g x)) (F.presheaf.stalk (g x)) :=
    Scheme.Modules.finite_stalk_of_isCoherent F (g x)
  have hlen := length_stalk_pullback_eq_length_quotSMulTop g F x t ht
  have _ : Nontrivial (((Scheme.Modules.pullback g).obj F).presheaf.stalk x) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk ((Scheme.Modules.pullback g).obj F) x).mp hx
  have _ : Nontrivial (QuotSMulTop t (F.presheaf.stalk (g x))) := by
    refine not_subsingleton_iff_nontrivial.mp fun hs => ?_
    have h0 : Module.length (X.presheaf.stalk x)
        (((Scheme.Modules.pullback g).obj F).presheaf.stalk x) = 0 := by
      rw [hlen]
      exact Module.length_eq_zero_iff.mpr hs
    exact not_subsingleton _ (Module.length_eq_zero_iff.mp h0)
  exact supportDim_eq_zero_of_isFiniteLength
    (Module.length_ne_top_iff.mp (hlen ▸ Module.length_ne_top_iff.mpr hfin))

/-- **The multiplicity of the restriction of `F` to a locally principal closed subscheme, as a
sum over the support of the stalk.** At a point `x` where the stalk of `g^* F` has finite length,
and under the condition that `g x` is not an associated point of `F`, the multiplicity of `g^* F`
at `x` is the sum, over the minimal points `q` of the support of `M = F_{g x}`, of the colength
of `(t, q)` times the length of `M` localized at `q`.

This is the sheaf counterpart of
`Stacks.Chow.exists_localEquation_cycleAssociatedToZeroFiber_apply_eq_sum_minimalPrimes`: the
left-hand side is the coefficient of the cycle of `g^* F`, and the right-hand side is what the
components of the support of `F` through `g x` contribute to it. -/
theorem sheafMultiplicity_pullback_eq_toNat_finsum_minimal_support {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (g : X ⟶ Y) [IsPreimmersion g] (F : Y.Modules) [F.IsCoherent] (x : X)
    (t : Y.presheaf.stalk (g x)) (ht : RingHom.ker (g.stalkMap x).hom = Ideal.span {t})
    (hassoc : g x ∉ Stacks.Divisors.associatedPoints F)
    (hx : x ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F))
    (hfin : IsFiniteLength (X.presheaf.stalk x)
      (((Scheme.Modules.pullback g).obj F).presheaf.stalk x)) :
    sheafMultiplicity ((Scheme.Modules.pullback g).obj F) x =
      ∑ᶠ q ∈ {q : PrimeSpectrum (Y.presheaf.stalk (g x)) |
          Minimal (· ∈ Module.support (Y.presheaf.stalk (g x)) (F.presheaf.stalk (g x))) q},
        ((Module.length (Y.presheaf.stalk (g x))
            (Y.presheaf.stalk (g x) ⧸ (Ideal.span {t} ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk (g x)))).toNat : ℤ) := by
  have _ : Module.Finite (Y.presheaf.stalk (g x)) (F.presheaf.stalk (g x)) :=
    Scheme.Modules.finite_stalk_of_isCoherent F (g x)
  have hquot := supportDim_quotSMulTop_stalk_eq_zero_of_isFiniteLength g F x t ht hx hfin
  rw [sheafMultiplicity_pullback_eq_toNat_length_quotSMulTop g F x t ht,
    length_quotSMulTop_eq_finsum_minimal_support_of_notMem_associatedPrimes t
      (mem_maximalIdeal_of_span_eq_ker_stalkMap g x t ht)
      (notMem_associatedPrimes_stalk_of_notMem_associatedPoints F (g x) hassoc) hquot]
  exact toNat_finsum_minimal_support t hquot.le

end Stacks.Chow

end
