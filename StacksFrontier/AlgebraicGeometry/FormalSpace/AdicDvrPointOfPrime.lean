module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts

/-!
# An adic point out of a complete discrete valuation ring through a given prime

Let `S` be a scheme contained in a big fppf site `B` and let `A` be a Noetherian ring with an
adic topology, presented over `S` by a quotient system `D`. For a prime `𝔮` of `A` not containing
some ideal of definition there is a complete discrete valuation ring `W`, presented over `S`, and
a continuous homomorphism `A → W` over `S` with kernel exactly `𝔮` whose formal spectrum map
`Spf W ⟶ Spf A` is adic, that is representable by algebraic spaces.

This is the step of the proof of Stacks 0GH6 which, given a prime `𝔮` away from the ideal of
definition, chooses a maximal ideal `𝔪 ⊇ 𝔮 + I` and, by Stacks 00PH, a discrete valuation ring
dominating `(A/𝔮)_𝔪`; here it is completed (Stacks 0AP1) so that the point is an adic morphism
out of the formal spectrum of a complete discrete valuation ring, the input that
rig-surjectivity (Definition 0AQQ) accepts.

## Main results

* `Rig.exists_dvr_ker_eq_of_isPrime`: the discrete valuation point of a prime.
* `AlgebraicGeometry.FormalSpace.exists_adic_completeDvr_point_of_isPrime`: the adic point.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Cardinal

universe u

/-- A proper ideal stays proper after adding an ideal contained in the Jacobson radical. -/
private theorem Ideal.sup_ne_top_of_le_jacobson_bot {A : Type*} [CommRing A] {q I : Ideal A}
    (hq : q ≠ ⊤) (hI : I ≤ (⊥ : Ideal A).jacobson) : q ⊔ I ≠ ⊤ := by
  intro htop
  have h1 : (1 : A) ∈ q ⊔ I := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, a, ha, hxa⟩ := Submodule.mem_sup.mp h1
  have h2 := Ideal.mem_jacobson_bot.mp (hI ha) (-1)
  have h3 : a * (-1) + 1 = x := by linear_combination -hxa
  rw [h3] at h2
  exact hq (Ideal.eq_top_of_isUnit_mem q hx h2)

/-- A prime containing one ideal of definition contains every ideal of definition. -/
private theorem TopologicalRing.IsIdealOfDefinition.le_of_isPrime {A : Type*} [CommRing A]
    [TopologicalSpace A] {I J p : Ideal A} [hp : p.IsPrime]
    (hI : TopologicalRing.IsIdealOfDefinition I) (hJ : TopologicalRing.IsIdealOfDefinition J)
    (hJp : J ≤ p) : I ≤ p := by
  obtain ⟨n, hn⟩ := hI.2 (J : Set A) (hJ.1.mem_nhds J.zero_mem)
  exact fun x hx => hp.mem_of_pow_mem (n + 1)
    (hJp (hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hx (n + 1)))))

/-- In a discrete valuation ring with its maximal-adic topology, every nonzero proper ideal is
an ideal of definition of the topology. -/
private theorem IsDiscreteValuationRing.isAdic_of_ne_bot_of_ne_top {W : Type*} [CommRing W]
    [IsDomain W] [IsDiscreteValuationRing W] [TopologicalSpace W] [IsTopologicalRing W]
    (hW : _root_.IsAdic (IsLocalRing.maximalIdeal W)) {I : Ideal W} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) :
    _root_.IsAdic I := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hπ
  have heq : I = IsLocalRing.maximalIdeal W ^ n := by
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_pow]
  have hnpos : 0 < n := by
    by_contra! h
    exact h1 (by simpa [Nat.eq_zero_of_le_zero h] using heq)
  rw [heq]
  exact is_ideal_adic_pow hW hnpos

namespace Rig

/-- **The discrete valuation point of a prime away from an ideal of definition.** Let `A` be a
Noetherian ring with a topology, `I₀` an ideal of definition for which `A` is complete, and `𝔮`
a prime not containing `I₀`. Then there is a discrete valuation ring `R` no larger than `A` and a
homomorphism `A → R` with kernel exactly `𝔮` carrying every ideal of definition into the maximal
ideal of `R`, and `I₀` to a nonzero ideal.

The proof chooses a maximal ideal `𝔪 ⊇ 𝔮 + I₀`, which is proper because `I₀` lies in the
Jacobson radical, and dominates the Noetherian local domain `(A/𝔮)_𝔪` by a discrete valuation
ring inside its fraction field (Stacks 00PH); the composite `A → A/𝔮 → R` has kernel `𝔮`
because `A/𝔮 → R` is injective. -/
theorem exists_dvr_ker_eq_of_isPrime {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsNoetherianRing A] {I₀ : Ideal A}
    (hI₀ : TopologicalRing.IsIdealOfDefinition I₀) [IsAdicComplete I₀ A]
    (q : Ideal A) [hq : q.IsPrime] (hqI : ¬ I₀ ≤ q) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), RingHom.ker φ = q ∧
        (∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
          Ideal.map φ I ≤ IsLocalRing.maximalIdeal R) ∧ Ideal.map φ I₀ ≠ ⊥ ∧ #R ≤ #A := by
  classical
  obtain ⟨m, hm, hmle⟩ := Ideal.exists_le_maximal _
    (Ideal.sup_ne_top_of_le_jacobson_bot hq.ne_top (IsAdicComplete.le_jacobson_bot I₀))
  have hqm : q ≤ m := le_sup_left.trans hmle
  have hIm : I₀ ≤ m := le_sup_right.trans hmle
  have _ : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
  let mq : Ideal (A ⧸ q) := m.map (Ideal.Quotient.mk q)
  have _ : mq.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker] using hqm)
  obtain ⟨x₀, hx₀I, hx₀q⟩ := IsConcreteLE.not_le_iff_exists.mp hqI
  have hqne : mq ≠ ⊥ := by
    intro hbot
    refine hx₀q (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    have hx₀ := Ideal.mem_map_of_mem (Ideal.Quotient.mk q) (hIm hx₀I)
    rwa [show m.map (Ideal.Quotient.mk q) = mq from rfl, hbot, Ideal.mem_bot] at hx₀
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
  have hker : RingHom.ker (ψ.comp (Ideal.Quotient.mk q)) = q := by
    rw [RingHom.ker_comp_of_injective _ hψinj, Ideal.mk_ker]
  refine ⟨R, inferInstance, inferInstance, hRdvr, ψ.comp (Ideal.Quotient.mk q), hker,
    fun I hI => ?_, ?_,
    hcardR.trans ((IsLocalization.cardinalMk_le (R := A ⧸ q) (L := L) mq.primeCompl).trans
      Cardinal.mk_quotient_le)⟩
  · have := hm.isPrime
    exact Ideal.map_le_iff_le_comap.mpr fun z hz =>
      hlocR _ (hmemL _ (Ideal.mem_map_of_mem _ (hI.le_of_isPrime hI₀ hIm hz)))
  · rw [Ne, Ideal.map_eq_bot_iff_le_ker, hker]
    exact hqI

end Rig

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An adic point of `Spf A` out of a complete discrete valuation ring with prescribed kernel.**
Let `A` be a Noetherian ring with an adic topology, presented over `S` by a quotient system `D`,
and let `𝔮` be a prime of `A` not containing the ideal of definition `J`. Then there are a
complete discrete valuation ring `W` with its maximal-adic topology, presented over `S` by a
quotient system `DW`, and a continuous homomorphism `χ : A → W` over `S` with kernel `𝔮` whose
formal spectrum map `Spf W ⟶ Spf A` is representable by algebraic spaces.

The discrete valuation ring of `Rig.exists_dvr_ker_eq_of_isPrime` is replaced by its
maximal-adic completion, again a discrete valuation ring (Stacks 0AP1) into which it injects, so
the kernel is unchanged. The composite `A → W` is adic, the image of an ideal of definition being
a nonzero proper ideal of `W`, hence taut, and Stacks 0AN5 makes its formal spectrum map
representable. -/
theorem exists_adic_completeDvr_point_of_isPrime {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) (D : QuotientSystem B S hS A)
    (q : Ideal A) [q.IsPrime] {J : Ideal A} (hJ : TopologicalRing.IsIdealOfDefinition J)
    (hqJ : ¬ J ≤ q) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : TopologicalSpace W) (_ : IsTopologicalRing W) (_ : IsLinearTopology W W),
      _root_.IsAdic (IsLocalRing.maximalIdeal W) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        ∃ (_ : TopologicalRing.IsWeaklyAdmissible W) (DW : QuotientSystem B S hS W)
          (χ : ContinuousHom D DW),
          RingHom.ker χ.toRingHom = q ∧
            Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
              (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hA) χ).hom := by
  classical
  have hAw := Rig.weaklyAdmissible_of_isAdicRing hA
  obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hA
  have _ : IsAdicComplete I₀ A := hI₀complete
  obtain ⟨R, _, _, _, φ, hker, hmax, hI₀ne, hRcard⟩ :=
    Rig.exists_dvr_ker_eq_of_isPrime hI₀def q fun hle => hqJ (hJ.le_of_isPrime hI₀def hle)
  have hRcard' : #R < B.cutoff :=
    hRcard.trans_lt (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hA D)
  set W : Type u := AdicCompletion (IsLocalRing.maximalIdeal R) R with hWdef
  obtain ⟨_, _⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := R)).mp
      ⟨inferInstance, inferInstance⟩
  let : TopologicalSpace W := (IsLocalRing.maximalIdeal W).adicTopology
  have hWtopring : IsTopologicalRing W :=
    (IsLocalRing.maximalIdeal W).ringFilterBasis.isTopologicalRing
  have hWlin : IsLinearTopology W W := (IsLocalRing.maximalIdeal W).isLinearTopology
  have hWtop : _root_.IsAdic (IsLocalRing.maximalIdeal W) := rfl
  have hWcomplete : IsAdicComplete (IsLocalRing.maximalIdeal W) W := inferInstance
  have hWweak : TopologicalRing.IsWeaklyAdmissible W :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hWtop hWcomplete
  have hWcard : #W < B.cutoff := mk_adicCompletion_lt_cutoff _ hRcard'
  have hinj : Function.Injective (algebraMap R W) :=
    AdicCompletion.of_injective (IsLocalRing.maximalIdeal R) R
  set ψ : A →+* W := (algebraMap R W).comp φ with hψdef
  have hψmap : Ideal.map ψ I₀ = Ideal.map (algebraMap R W) (Ideal.map φ I₀) := by
    rw [hψdef, Ideal.map_map]
  have hψle : Ideal.map ψ I₀ ≤ IsLocalRing.maximalIdeal W := by
    rw [hψmap]
    refine (Ideal.map_mono (hmax I₀ hI₀def)).trans
      (Ideal.map_le_iff_le_comap.mpr (le_of_eq ?_))
    rw [IsLocalRing.maximalIdeal_comap]
  have hψadic : RingHom.IsAdic ψ := ⟨I₀, hI₀adic,
    IsDiscreteValuationRing.isAdic_of_ne_bot_of_ne_top hWtop
      (by rw [hψmap, Ne, Ideal.map_eq_bot_iff_of_injective hinj]; exact hI₀ne)
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal W).ne_top hψle)⟩
  obtain ⟨DW, χ, hχ⟩ := exists_quotientSystem_continuousHom hAw D ψ
    (continuous_of_isAdic_of_map_le hI₀adic hWtop ψ hψle) hWcard
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, hWtopring, hWlin, hWtop,
    hWcomplete, hWweak, DW, χ, by rw [hχ, hψdef, RingHom.ker_comp_of_injective _ hinj, hker], ?_⟩
  exact isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hAw hWweak
    D DW (hasLargeSite_of_mk_lt_cutoff DW hWcard) χ
    (RingHom.isTaut_of_isAdic χ.toRingHom (by rw [hχ]; exact hψadic))

end AlgebraicGeometry.FormalSpace

end
