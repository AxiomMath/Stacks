module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.AffineFieldFactors
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerAlgebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerUnramified

/-!
# A tame cover becomes unramified in codimension one after a Kummer base change

Let `A` be a Noetherian domain and `φ ∈ A` a nonzero element generating a prime ideal, with
local ring `O = A_{(φ)}`, a discrete valuation ring. Let `B` be a finite étale `A_φ`-algebra which
is a domain, with fraction field `L` tamely ramified over `O`, and let `e ≥ 1` be invertible in
`κ(φ)` and divisible by all ramification indices of `L` over `O`. If `A' = A[x]/(x^e - φ)` is a
domain, then the base change `A'_φ ⊗_{A_φ} B` is unramified over `Spec A'` in codimension one.

## Main results

* `AlgebraicGeometry.Abhyankar.isUnramifiedInCodimensionOne_baseChange`: the statement above.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Polynomial
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

/-- The prime `(x)` of `A[x]/(x^e - φ)` contracts to `(φ)`. -/
theorem comap_span_root (A : Type u) [CommRing A] (φ : A) (e : ℕ) [NeZero e] :
    (Ideal.span {root A φ e}).comap (algebraMap A (standardTamelyRamifiedAlgebra A φ e)) =
      Ideal.span {φ} := by
  rw [← ker_toQuot, RingHom.comap_ker]
  have : (toQuot A φ e).comp (algebraMap A _) = Ideal.Quotient.mk (Ideal.span {φ}) :=
    RingHom.ext (toQuot_algebraMap A φ e)
  rw [this, Ideal.mk_ker]

/-- **The base change to the Kummer algebra is unramified in codimension one.** Let `A` be a
Noetherian domain, `φ ≠ 0` with `(φ)` prime and local ring `O`, `B` a domain finite étale over
`A_φ` with fraction field `L` tamely ramified over `O`, and `e ≥ 1` invertible in `κ(φ)` and
divisible by the ramification indices of `L`. If `A' = A[x]/(x^e - φ)` is a domain, then
`A'_φ ⊗_{A_φ} B` is unramified over `Spec A'` in codimension one. -/
theorem isUnramifiedInCodimensionOne_baseChange {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {φ : A} (hφ0 : φ ≠ 0) [hp : (Ideal.span {φ}).IsPrime]
    {e : ℕ} [NeZero e] [IsDomain (standardTamelyRamifiedAlgebra A φ e)]
    {O K L : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O]
    [IsLocalization.AtPrime O (Ideal.span {φ})] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra O L]
    [IsScalarTower O K L]
    (htame : IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo O K L)
    (hue : IsUnit (e : ResidueField O))
    (hdiv : ∀ m : Ideal (integralClosure O L), m.IsMaximal → m.LiesOver (maximalIdeal O) →
      Ideal.ramificationIdx' (maximalIdeal O) m ∣ e)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra (Localization.Away φ) B]
    [Algebra.IsIntegral (Localization.Away φ) B] [Algebra B L] [IsFractionRing B L]
    (hBL : ∀ a : A, algebraMap B L (algebraMap _ B (algebraMap A (Localization.Away φ) a)) =
      algebraMap O L (algebraMap A O a)) :
    letI := (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ e)) φ).toAlgebra
    Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec (.of (standardTamelyRamifiedAlgebra A φ e)))
        (PrimeSpectrum.basicOpen (algebraMap A _ φ)))
      (AffineFieldFactors.coverMap (R := .of (standardTamelyRamifiedAlgebra A φ e))
        (algebraMap A _ φ) (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ e) φ)
          ⊗[Localization.Away φ] B)) := by
  classical
  intro Z hZ hD hV K'' L'' _ _ _ _ _ _ _ _ _ hFF
  let C := standardTamelyRamifiedAlgebra A φ e
  let x : C := root A φ e
  let ζ := Z.genericPoint
  have := ζ.isPrime
  let O' := (Spec (.of C)).presheaf.stalk ζ
  let : Algebra C O' := StructureSheaf.stalkAlgebra C ζ
  have : IsLocalization.AtPrime O' ζ.asIdeal := StructureSheaf.IsLocalization.to_stalk C ζ
  have := hD
  have := hV
  have hgζ : algebraMap A C φ ∈ ζ.asIdeal := by
    by_contra h
    exact hZ ⟨⟨ζ, h⟩, rfl⟩
  have hxmem : ∀ Q : Ideal C, Q.IsPrime → algebraMap A C φ ∈ Q → x ∈ Q := fun Q hQ h ↦
    hQ.mem_of_pow_mem e (by rwa [root_pow])
  have hxζ : x ∈ ζ.asIdeal := hxmem _ ζ.isPrime hgζ
  have hxp : (Ideal.span {x}).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    have : IsDomain (A ⧸ Ideal.span {φ}) := (Ideal.Quotient.isDomain_iff_prime _).mpr hp
    exact (quotRootEquiv A φ e).toMulEquiv.isDomain
  have hCO' : Function.Injective (algebraMap C O') :=
    IsLocalization.injective O' (Ideal.primeCompl_le_nonZeroDivisors ζ.asIdeal)
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero (root_mem_nonZeroDivisors A e hφ0)
  have hζ : ζ.asIdeal = Ideal.span {x} := by
    have hdisj : Disjoint (ζ.asIdeal.primeCompl : Set C) (Ideal.span {x}) := by
      rw [Set.disjoint_left]
      intro c hc hcx
      exact hc ((Ideal.span_singleton_le_iff_mem _).mpr hxζ hcx)
    have hPprime := IsLocalization.isPrime_of_isPrime_disjoint ζ.asIdeal.primeCompl O' _ hxp hdisj
    have hPne : (Ideal.span {x}).map (algebraMap C O') ≠ ⊥ := by
      rwa [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp hCO',
        le_bot_iff, Ideal.span_singleton_eq_bot]
    have hmax := Ideal.IsPrime.isMaximal hPprime hPne
    have h1 := IsLocalization.under_map_of_isPrime_disjoint ζ.asIdeal.primeCompl O' hxp hdisj
    rwa [IsLocalRing.eq_maximalIdeal hmax,
      IsLocalization.AtPrime.under_maximalIdeal (S := O') ζ.asIdeal] at h1
  have hcomap : ζ.asIdeal.comap (algebraMap A C) = Ideal.span {φ} := by
    rw [hζ, comap_span_root]
  have hle : (Ideal.span {φ}).primeCompl ≤ (ζ.asIdeal.primeCompl).comap (algebraMap A C) := by
    intro a ha
    show algebraMap A C a ∉ ζ.asIdeal
    rwa [← Ideal.mem_comap, hcomap]
  let : Algebra O O' := (IsLocalization.map O' (algebraMap A C) hle : O →+* O').toAlgebra
  have hOO' : ∀ a, algebraMap O O' (algebraMap A O a) = algebraMap C O' (algebraMap A C a) :=
    fun a ↦ IsLocalization.map_eq hle a
  let π := algebraMap A O φ
  let ϖ := algebraMap C O' x
  have hπ : maximalIdeal O = Ideal.span {π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {φ}) O, Ideal.map_span,
      Set.image_singleton]
  have hϖ : maximalIdeal O' = Ideal.span {ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal ζ.asIdeal O', hζ, Ideal.map_span,
      Set.image_singleton]
  have hπϖ : algebraMap O O' π = ϖ ^ e := by
    rw [hOO', ← root_pow, map_pow]
  have hϖ0 : ϖ ≠ 0 := fun h ↦ hx0 (hCO' (h.trans (map_zero _).symm))
  have hOO'inj : Function.Injective (algebraMap O O') := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    by_contra hne
    have hker : RingHom.ker (algebraMap O O') ≠ ⊥ := fun h ↦ hne (by
      have : o ∈ RingHom.ker (algebraMap O O') := ho
      rwa [h] at this)
    have hmx := (RingHom.ker_isPrime (algebraMap O O')).isMaximal hker
    have hπmem : π ∈ RingHom.ker (algebraMap O O') := by
      rw [IsLocalRing.eq_maximalIdeal hmx, hπ]
      exact Ideal.mem_span_singleton_self π
    rw [RingHom.mem_ker, hπϖ] at hπmem
    exact pow_ne_zero e hϖ0 hπmem
  have hAO : Function.Injective (algebraMap A O) :=
    IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {φ}))
  let : Algebra O K'' := ((algebraMap O' K'').comp (algebraMap O O')).toAlgebra
  have : IsScalarTower O O' K'' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hOK'' : Function.Injective (algebraMap O K'') :=
    (IsFractionRing.injective O' K'').comp hOO'inj
  let : Algebra K K'' := (IsFractionRing.lift hOK'' : K →+* K'').toAlgebra
  have : IsScalarTower O K K'' := IsScalarTower.of_algebraMap_eq fun o ↦
    (IsFractionRing.lift_algebraMap hOK'' o).symm
  have hover : (Ideal.span {φ}).primesOver C = {ζ.asIdeal} := by
    ext Q
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hQ, hQo⟩
      have hφQ : algebraMap A C φ ∈ Q := by
        rw [← Ideal.mem_comap, ← Ideal.under_def, ← hQo.over]
        exact Ideal.mem_span_singleton_self φ
      have hle' : ζ.asIdeal ≤ Q := by
        rw [hζ, Ideal.span_singleton_le_iff_mem]
        exact hxmem Q hQ hφQ
      by_contra hne
      have hlt := Ideal.IsIntegral.comap_lt_comap (R := A) (lt_of_le_of_ne hle' (Ne.symm hne))
      rw [hcomap, ← Ideal.under_def, ← hQo.over] at hlt
      exact lt_irrefl _ hlt
    · rintro rfl
      exact ⟨inferInstance, ⟨hcomap.symm⟩⟩
  have hdec : ∀ w : O', ∃ (c : C) (o : O), w = algebraMap C O' c * algebraMap O O' o := by
    intro w
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl w
    obtain ⟨r, hr, c', hc'⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hover (t : C) t.2
    set u := IsLocalization.mk' O (1 : A) (⟨r, hr⟩ : (Ideal.span {φ}).primeCompl)
    have h1 : algebraMap C O' (algebraMap A C r) * algebraMap O O' u = 1 := by
      rw [← hOO', ← map_mul, IsLocalization.mk'_spec' O (1 : A) ⟨r, hr⟩, map_one, map_one]
    refine ⟨c * c', u, ?_⟩
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have := congrArg (algebraMap C O') hc'
    simp only [map_mul] at this ⊢
    linear_combination (-algebraMap C O' c) * h1 + algebraMap C O' c * algebraMap O O' u * this
  have hOK (o : O) :
      algebraMap O' K'' (algebraMap O O' o) = algebraMap K K'' (algebraMap O K o) := by
    rw [← IsScalarTower.algebraMap_apply O O' K'', IsScalarTower.algebraMap_apply O K K'']
  have hint : ∀ w : O', _root_.IsIntegral O (algebraMap O' K'' w) := by
    intro w
    obtain ⟨c, o, rfl⟩ := hdec w
    rw [map_mul]
    refine _root_.IsIntegral.mul ?_ ?_
    · exact IsIntegral.map_of_comp_eq (algebraMap A O) ((algebraMap O' K'').comp (algebraMap C O'))
        (RingHom.ext fun a ↦ by
          simp only [RingHom.comp_apply]
          rw [IsScalarTower.algebraMap_apply O O' K'', hOO'])
        (Algebra.IsIntegral.isIntegral (R := A) c)
    · rw [← IsScalarTower.algebraMap_apply]
      exact isIntegral_algebraMap
  let xt : K'' := algebraMap O' K'' ϖ
  have hxt : xt ^ e = algebraMap K K'' (algebraMap O K π) := by
    rw [← map_pow, ← hπϖ, hOK]
  have hπK : algebraMap O K π ≠ 0 := fun h ↦
    hφ0 (hAO ((IsFractionRing.injective O K (h.trans (map_zero _).symm)).trans (map_zero _).symm))
  have hroot : aeval xt (X ^ e - Polynomial.C (algebraMap O K π)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hxt, sub_self]
  have hxtint : _root_.IsIntegral K xt := ⟨_, monic_X_pow_sub_C _ (NeZero.ne e), hroot⟩
  have hCF : ∀ c : C, algebraMap O' K'' (algebraMap C O' c) ∈ IntermediateField.adjoin K {xt} := by
    intro c
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    induction p using Polynomial.induction_on with
    | C a =>
      have : Ideal.Quotient.mk (Ideal.span {X ^ e - Polynomial.C φ}) (Polynomial.C a) =
          algebraMap A C a := rfl
      rw [this, ← hOO', hOK]
      exact IntermediateField.algebraMap_mem _ _
    | add p q hp hq => rw [map_add, map_add, map_add]; exact add_mem hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul]
      exact mul_mem h (IntermediateField.subset_adjoin K _ (Set.mem_singleton _))
  have htop : IntermediateField.adjoin K {xt} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w₁, w₂, -, rfl⟩ := IsFractionRing.div_surjective (A := O') z
    have hw : ∀ w : O', algebraMap O' K'' w ∈ IntermediateField.adjoin K {xt} := by
      intro w
      obtain ⟨c, o, rfl⟩ := hdec w
      rw [map_mul, hOK]
      exact mul_mem (hCF c) (IntermediateField.algebraMap_mem _ _)
    exact div_mem (hw w₁) (hw w₂)
  have : FiniteDimensional K K'' := by
    have := IntermediateField.adjoin.finiteDimensional hxtint
    rw [htop] at this
    exact Module.Finite.equiv (IntermediateField.topEquiv (F := K) (E := K'')).toLinearEquiv
  have heK : (e : K) ≠ 0 := by
    intro h
    apply hue.ne_zero
    rw [← map_natCast (algebraMap O K), ← map_zero (algebraMap O K)] at h
    rw [← map_natCast (IsLocalRing.residue O), IsFractionRing.injective O K h, map_zero]
  have : Algebra.IsSeparable K K'' := by
    have hsep : IsSeparable K xt := by
      refine (separable_X_pow_sub_C (algebraMap O K π) heK hπK).of_dvd (minpoly.dvd K xt hroot)
    have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K K'').mpr hsep
    rw [htop] at this
    exact Algebra.IsSeparable.of_algHom K _
      (IntermediateField.topEquiv (F := K) (E := K'')).symm.toAlgHom
  let Cφ := Localization.Away (algebraMap A C φ)
  let : Algebra (Localization.Away φ) Cφ :=
    (Localization.awayMap (algebraMap A C) φ).toAlgebra
  obtain ⟨ψ, hψ, hgen⟩ := AffineFieldFactors.exists_ringHom_of_isFieldFactorAt (R := .of C) ζ
    (by rw [Spec.fromSpecStalk_eq']; rfl) hFF
  have hψC : ∀ c : C, ψ (algebraMap Cφ (Cφ ⊗[Localization.Away φ] B) (algebraMap C Cφ c)) =
      algebraMap K'' L'' (algebraMap O' K'' (algebraMap C O' c)) := by
    intro c
    rw [hψ, IsScalarTower.algebraMap_apply O' K'' L'']
  let ψB : B →+* L'' := ψ.comp (Algebra.TensorProduct.includeRight.toRingHom)
  have hψBA : ∀ a : A, ψB (algebraMap _ B (algebraMap A (Localization.Away φ) a)) =
      algebraMap K'' L'' (algebraMap K K'' (algebraMap O K (algebraMap A O a))) := by
    intro a
    show ψ ((1 : Cφ) ⊗ₜ algebraMap _ B (algebraMap A (Localization.Away φ) a)) = _
    rw [← Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply (Localization.Away φ) Cφ (Cφ ⊗[Localization.Away φ] B)]
    have : algebraMap (Localization.Away φ) Cφ (algebraMap A (Localization.Away φ) a) =
        algebraMap C Cφ (algebraMap A C a) := by
      show Localization.awayMap (algebraMap A C) φ _ = _
      exact IsLocalization.map_eq _ _
    rw [this, hψC, ← hOO', hOK]
  have hfA : Function.Injective fun a : A ↦
      algebraMap K'' L'' (algebraMap K K'' (algebraMap O K (algebraMap A O a))) :=
    (algebraMap K'' L'').injective.comp ((algebraMap K K'').injective.comp
      ((IsFractionRing.injective O K).comp hAO))
  have hRinj : Function.Injective (ψB.comp (algebraMap (Localization.Away φ) B)) := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers φ)]
    intro a b
    simp only [RingHom.comp_apply, hψBA]
    have hAR : Function.Injective (algebraMap A (Localization.Away φ)) :=
      IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
    exact ⟨fun h ↦ by rw [hAR h], fun h ↦ by rw [hfA h]⟩
  have : IsDomain (Localization.Away φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  have hψBinj : Function.Injective ψB := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := Localization.Away φ)
    rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hRinj
  let ψL : L →+* L'' := IsFractionRing.lift hψBinj
  let : Algebra K L'' := ((algebraMap K'' L'').comp (algebraMap K K'')).toAlgebra
  have : IsScalarTower K K'' L'' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hψLK : ψL.comp (algebraMap K L) = algebraMap K L'' := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (IsLocalization.ringHom_ext
      (Ideal.span {φ}).primeCompl (RingHom.ext fun a ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply O K L, ← hBL, IsFractionRing.lift_algebraMap]
    exact hψBA a
  let ψLa : L →ₐ[K] L'' := { ψL with commutes' := fun k ↦ RingHom.congr_fun hψLK k }
  let t : L ⊗[K] K'' →ₐ[K] L'' := Algebra.TensorProduct.lift ψLa
    (IsScalarTower.toAlgHom K K'' L'') (fun _ _ ↦ Commute.all _ _)
  have htF : ∀ f, t (1 ⊗ₜ f) = algebraMap K'' L'' f := fun f ↦ by
    simp [t, Algebra.TensorProduct.lift_tmul]
  have htL : ∀ l, t (l ⊗ₜ 1) = ψL l := fun l ↦ by
    simp [t, Algebra.TensorProduct.lift_tmul, ψLa]
  have hgφ : IsUnit (((algebraMap O' K'').comp (algebraMap C O')) (algebraMap A C φ)) := by
    refine isUnit_iff_ne_zero.mpr fun h ↦ ?_
    have h' : algebraMap O' K'' ϖ ^ e = 0 := by rwa [← map_pow, ← hπϖ, hOO']
    exact pow_ne_zero e ((map_ne_zero_iff _ (IsFractionRing.injective O' K'')).mpr hϖ0) h'
  let ν : Cφ →+* K'' := IsLocalization.Away.lift (algebraMap A C φ) hgφ
  have hψν : ψ.comp (algebraMap Cφ (Cφ ⊗[Localization.Away φ] B)) =
      (algebraMap K'' L'').comp ν :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A C φ)) (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply]
      rw [hψC, IsLocalization.Away.lift_eq]
      rfl)
  let S : Subalgebra K'' L'' :=
    { t.range.toSubsemiring with algebraMap_mem' := fun f ↦ ⟨1 ⊗ₜ f, htF f⟩ }
  have hψS : ∀ y, ψ y ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul c b =>
      have hcb : c ⊗ₜ[Localization.Away φ] b = algebraMap Cφ _ c * (1 ⊗ₜ b) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
        rfl
      rw [hcb, map_mul]
      refine S.mul_mem ?_ ?_
      · rw [← RingHom.comp_apply, hψν, RingHom.comp_apply]
        exact S.algebraMap_mem _
      · refine ⟨algebraMap B L b ⊗ₜ 1, ?_⟩
        show t _ = _
        rw [htL, IsFractionRing.lift_algebraMap]
        rfl
    | add y z hy hz => rw [map_add]; exact S.add_mem hy hz
  have ht : Function.Surjective t := by
    intro l
    have hl : l ∈ Algebra.adjoin K'' (Set.range ψ) := by rw [hgen]; trivial
    exact Algebra.adjoin_le (Set.range_subset_iff.mpr hψS) hl
  exact isUnramifiedWithRespectTo_of_tensor htame (NeZero.pos e) hdiv hint π hπ ϖ hϖ hπϖ t ht htF

end AlgebraicGeometry.Abhyankar
