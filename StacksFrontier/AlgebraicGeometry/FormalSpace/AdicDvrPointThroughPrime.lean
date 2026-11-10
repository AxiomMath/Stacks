module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicDvrPointOfPrime

/-!
# An adic point out of a complete discrete valuation ring with prescribed kernel and closed point

Let `S` be a scheme contained in a big fppf site `B` and let `A` be a Noetherian ring with an
adic topology, presented over `S` by a quotient system `D`. Given primes `𝔮 ⊆ 𝔪` of `A` with `𝔪`
containing an ideal of definition and `𝔮` not containing it, there is a complete discrete
valuation ring `W`, presented over `S`, and a continuous homomorphism `A → W` over `S` with kernel
exactly `𝔮` and closed point `𝔪` (the preimage of the maximal ideal of `W` is `𝔪`) whose formal
spectrum map `Spf W ⟶ Spf A` is representable by algebraic spaces.

This refines `AlgebraicGeometry.FormalSpace.exists_adic_completeDvr_point_of_isPrime`, where the
closed point of the discrete valuation point is some maximal ideal over `𝔮` chosen in the proof:
here it is required to lie over the given `𝔪`. The argument is the same, Stacks 00PH applied to
the Noetherian local domain `(A/𝔮)_𝔪` instead of a localization at an arbitrary maximal ideal,
followed by the maximal-adic completion (Stacks 0AP1).

## Main results

* `Rig.exists_dvr_ker_eq_of_le_isPrime`: the discrete valuation point with prescribed kernel and
  closed point.
* `AlgebraicGeometry.FormalSpace.exists_adic_completeDvr_point_of_le_isPrime`: the adic point.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Cardinal

universe u

namespace Rig

/-- A homomorphism to a local ring carrying `𝔪` into the maximal ideal and its complement to
units has closed point `𝔪`. -/
private theorem comap_maximalIdeal_eq_of_isUnit {A R : Type*} [CommRing A] [CommRing R]
    [IsLocalRing R] {m : Ideal A} (φ : A →+* R) (hmax : ∀ x ∈ m, φ x ∈ IsLocalRing.maximalIdeal R)
    (hunit : ∀ x ∉ m, IsUnit (φ x)) : (IsLocalRing.maximalIdeal R).comap φ = m := by
  ext x
  refine ⟨fun h => ?_, fun hx => Ideal.mem_comap.mpr (hmax x hx)⟩
  by_contra hx
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h) (hunit x hx)

/-- **The discrete valuation point of a pair of primes.** Let `A` be a Noetherian ring, let
`𝔮 ⊆ 𝔪` be primes and let `I₀ ⊆ 𝔪` be an ideal not contained in `𝔮`. Then there is a discrete
valuation ring `R` no larger than `A` and a homomorphism `A → R` with kernel exactly `𝔮` which
carries `𝔪` into the maximal ideal of `R`, the complement of `𝔪` to units, and `I₀` to a nonzero
ideal: a discrete valuation ring
dominating the Noetherian local domain `(A/𝔮)_𝔪`, which is not a field because `I₀` is nonzero
in it (Stacks 00PH). -/
theorem exists_dvr_ker_eq_of_le_isPrime {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I₀ q m : Ideal A} [hq : q.IsPrime] [hm : m.IsPrime] (hqm : q ≤ m) (hIm : I₀ ≤ m)
    (hqI : ¬ I₀ ≤ q) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), RingHom.ker φ = q ∧ (∀ x ∈ m, φ x ∈ IsLocalRing.maximalIdeal R) ∧
        (∀ x ∉ m, IsUnit (φ x)) ∧ Ideal.map φ I₀ ≠ ⊥ ∧ #R ≤ #A := by
  classical
  let mq : Ideal (A ⧸ q) := m.map (Ideal.Quotient.mk q)
  have _ : mq.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker] using hqm)
  obtain ⟨x₀, hx₀I, hx₀q⟩ := IsConcreteLE.not_le_iff_exists.mp hqI
  have hqne : mq ≠ ⊥ := by
    intro hbot
    refine hx₀q (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    have hx₀ : Ideal.Quotient.mk q x₀ ∈ mq := Ideal.mem_map_of_mem _ (hIm hx₀I)
    rwa [hbot, Ideal.mem_bot] at hx₀
  let L := Localization.AtPrime mq
  have hinjL : Function.Injective (algebraMap (A ⧸ q) L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors mq)
  have _ : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors (M := mq.primeCompl)
    (S := L) (Ideal.primeCompl_le_nonZeroDivisors mq)
  have hmemL : ∀ y ∈ mq, algebraMap (A ⧸ q) L y ∈ IsLocalRing.maximalIdeal L := fun y hy =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ mq y).mpr hy
  have hnotField : ¬ IsField L := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro hbot
    obtain ⟨y, hymq, hy0⟩ := IsConcreteLE.not_le_iff_exists.mp fun h => hqne (le_bot_iff.mp h)
    rw [Ideal.mem_bot] at hy0
    refine hy0 (hinjL ?_)
    have hy := hmemL y hymq
    rw [hbot, Ideal.mem_bot] at hy
    simpa using hy
  have key : ∀ (T : Type u) [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsLocalRing T],
      ¬ IsField T → ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
        (_ : IsDiscreteValuationRing R) (ψ : T →+* R), Function.Injective ψ ∧
        (∀ y ∈ IsLocalRing.maximalIdeal T, ψ y ∈ IsLocalRing.maximalIdeal R) ∧ #R ≤ #T := by
    intro T _ _ _ _ hT
    obtain ⟨R, hRdvr, -, hRloc⟩ :=
      Stacks.DiscreteValuationRing.Existence.solution (R := T) (FractionRing T)
        (L := FractionRing T) hT
    have hinj : Function.Injective (algebraMap T R) := fun a b hab => by
      apply FaithfulSMul.algebraMap_injective T (FractionRing T)
      rw [IsScalarTower.algebraMap_apply T R (FractionRing T),
        IsScalarTower.algebraMap_apply T R (FractionRing T), hab]
    have hcard : #(↥R) ≤ #T :=
      (Cardinal.mk_le_of_injective (f := fun x : ↥R => (x : FractionRing T))
        Subtype.val_injective).trans
        (IsLocalization.cardinalMk_le (R := T) (L := FractionRing T) (nonZeroDivisors T))
    refine ⟨R, inferInstance, inferInstance, hRdvr, algebraMap T R, hinj, fun y hy => ?_, hcard⟩
    rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
    exact fun hu => hy (hRloc.map_nonunit _ hu)
  obtain ⟨R, _, _, hRdvr, ψL, hinjR, hlocR, hcardR⟩ := key L hnotField
  let ψ : A ⧸ q →+* R := ψL.comp (algebraMap (A ⧸ q) L)
  have hψinj : Function.Injective ψ := hinjR.comp hinjL
  have hcomap : mq.comap (Ideal.Quotient.mk q) = m := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have hker : RingHom.ker (ψ.comp (Ideal.Quotient.mk q)) = q := by
    ext z
    rw [RingHom.mem_ker, RingHom.comp_apply, ← map_zero ψ, hψinj.eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨R, inferInstance, inferInstance, hRdvr, ψ.comp (Ideal.Quotient.mk q), hker,
    fun x hx => hlocR _ (hmemL _ (Ideal.mem_map_of_mem _ hx)), fun x hx => ?_, ?_,
    hcardR.trans ((IsLocalization.cardinalMk_le (R := A ⧸ q) (L := L) mq.primeCompl).trans
      Cardinal.mk_quotient_le)⟩
  · have hx' : Ideal.Quotient.mk q x ∈ mq.primeCompl := fun h => hx (by rwa [← hcomap])
    exact (IsLocalization.map_units L ⟨_, hx'⟩).map ψL
  · rw [Ne, Ideal.map_eq_bot_iff_le_ker, hker]
    exact hqI

/-- If a power of `I` lies in `J` and `J` lies in a prime `p`, then `I` lies in `p`. -/
private theorem le_of_pow_subset_of_le {A : Type*} [CommRing A] {I J p : Ideal A} [p.IsPrime]
    {n : ℕ} (hn : ((I ^ n : Ideal A) : Set A) ⊆ J) (hJp : J ≤ p) : I ≤ p := fun x hx =>
  Ideal.IsPrime.mem_of_pow_mem ‹p.IsPrime› (n + 1)
    (hJp (hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hx (n + 1)))))

end Rig

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An adic point of `Spf A` out of a complete discrete valuation ring with prescribed kernel
and closed point.** Let `A` be a Noetherian ring with an adic topology, presented over `S` by a
quotient system `D`, and let `𝔮 ⊆ 𝔪` be primes of `A` with `𝔪` containing the ideal of
definition `J` and `𝔮` not containing it. Then there are a complete discrete valuation ring `W`
with its maximal-adic topology, presented over `S` by a quotient system `DW`, and a continuous
homomorphism `χ : A → W` over `S` with kernel `𝔮` and closed point `𝔪` (the preimage of the
maximal ideal of `W` is `𝔪`) whose formal spectrum map `Spf W ⟶ Spf A` is representable by
algebraic spaces.

This is `exists_adic_completeDvr_point_of_isPrime` with the closed point of the discrete
valuation point prescribed: `Rig.exists_dvr_ker_eq_of_le_isPrime` replaces the discrete valuation
ring dominating a localization at an arbitrary maximal ideal over `𝔮`, and the rest of the
argument, the maximal-adic completion and the representability of its formal spectrum map, is
unchanged. -/
theorem exists_adic_completeDvr_point_of_le_isPrime {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) (D : QuotientSystem B S hS A)
    {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) {J : Ideal A}
    (hJ : TopologicalRing.IsIdealOfDefinition J) (hJm : J ≤ m) (hqJ : ¬ J ≤ q) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : TopologicalSpace W) (_ : IsTopologicalRing W) (_ : IsLinearTopology W W),
      _root_.IsAdic (IsLocalRing.maximalIdeal W) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        ∃ (_ : TopologicalRing.IsWeaklyAdmissible W) (DW : QuotientSystem B S hS W)
          (χ : ContinuousHom D DW),
          RingHom.ker χ.toRingHom = q ∧
            (IsLocalRing.maximalIdeal W).comap χ.toRingHom = m ∧
            Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
              (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hA) χ).hom := by
  classical
  have hAw := Rig.weaklyAdmissible_of_isAdicRing hA
  obtain ⟨I₀, hI₀def, hI₀adic, -⟩ := exists_idealOfDefinition_isAdicComplete hA
  obtain ⟨n, hn⟩ := hI₀def.2 (J : Set A) (hJ.1.mem_nhds J.zero_mem)
  obtain ⟨k, hk⟩ := hJ.2 (I₀ : Set A) (hI₀def.1.mem_nhds I₀.zero_mem)
  have hI₀m : I₀ ≤ m := Rig.le_of_pow_subset_of_le hn hJm
  have hqI₀ : ¬ I₀ ≤ q := fun hle => hqJ (Rig.le_of_pow_subset_of_le hk hle)
  obtain ⟨R, _, _, _, φ, hker, hmax, hunit, hI₀ne, hRcard⟩ :=
    Rig.exists_dvr_ker_eq_of_le_isPrime hqm hI₀m hqI₀
  set W : Type u := AdicCompletion (IsLocalRing.maximalIdeal R) R
  obtain ⟨hWdom, hWdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := R)).mp
      ⟨inferInstance, inferInstance⟩
  have : IsDomain W := hWdom
  have : IsDiscreteValuationRing W := hWdvr
  let : TopologicalSpace W := (IsLocalRing.maximalIdeal W).adicTopology
  have hWtopring : IsTopologicalRing W :=
    (IsLocalRing.maximalIdeal W).ringFilterBasis.isTopologicalRing
  have hWlin : IsLinearTopology W W := (IsLocalRing.maximalIdeal W).isLinearTopology
  have hWtop : _root_.IsAdic (IsLocalRing.maximalIdeal W) := rfl
  have hWcomplete : IsAdicComplete (IsLocalRing.maximalIdeal W) W := inferInstance
  have hWweak : TopologicalRing.IsWeaklyAdmissible W :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hWtop hWcomplete
  have hWcard : #W < B.cutoff := mk_adicCompletion_lt_cutoff _
    (hRcard.trans_lt (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hA D))
  have hinj : Function.Injective (algebraMap R W) :=
    AdicCompletion.of_injective (IsLocalRing.maximalIdeal R) R
  set ψ : A →+* W := (algebraMap R W).comp φ with hψdef
  have hψker : RingHom.ker ψ = q := by
    rw [hψdef, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj,
      ← RingHom.ker_eq_comap_bot, hker]
  have hψmap : Ideal.map ψ I₀ = Ideal.map (algebraMap R W) (Ideal.map φ I₀) := by
    rw [hψdef, Ideal.map_map]
  have hψne : Ideal.map ψ I₀ ≠ ⊥ := by
    rwa [hψmap, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  have hψmax : ∀ x ∈ m, ψ x ∈ IsLocalRing.maximalIdeal W := fun x hx =>
    (IsLocalRing.maximalIdeal_comap (algebraMap R W)).ge (hmax x hx)
  have hψle : Ideal.map ψ I₀ ≤ IsLocalRing.maximalIdeal W :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => hψmax x (hI₀m hx)
  have hψproper : Ideal.map ψ I₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal W).ne_top hψle
  have hψmapadic : _root_.IsAdic (Ideal.map ψ I₀) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hψne hπ
    have heq : Ideal.map ψ I₀ = IsLocalRing.maximalIdeal W ^ n := by
      rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
        Ideal.span_singleton_pow]
    have hnpos : 0 < n := by
      by_contra! h
      exact hψproper (by simpa [Nat.eq_zero_of_le_zero h] using heq)
    rw [heq]
    exact is_ideal_adic_pow hWtop hnpos
  have hψadic : RingHom.IsAdic ψ := ⟨I₀, hI₀adic, hψmapadic⟩
  obtain ⟨DW, χ, hχ⟩ := exists_quotientSystem_continuousHom hAw D ψ
    (continuous_of_isAdic_of_map_le hI₀adic hWtop ψ hψle) hWcard
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, hWtopring, hWlin, hWtop,
    hWcomplete, hWweak, DW, χ, by rw [hχ, hψker], ?_, ?_⟩
  · rw [hχ]
    exact Rig.comap_maximalIdeal_eq_of_isUnit ψ hψmax fun x hx => (hunit x hx).map (algebraMap R W)
  · exact isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hAw hWweak
      D DW (hasLargeSite_of_mk_lt_cutoff DW hWcard) χ
      (RingHom.isTaut_of_isAdic χ.toRingHom (by rwa [hχ]))

end AlgebraicGeometry.FormalSpace

end
