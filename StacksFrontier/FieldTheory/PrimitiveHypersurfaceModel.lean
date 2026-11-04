module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksFrontier.FieldTheory.IntegralPrimitiveElement

/-!
# A hypersurface model of a finitely generated extension of a perfect field

Let `K/k` be a finitely generated field extension of a perfect field which is not algebraic. Then
`K` has a separating transcendence basis `t₀, …, tₙ` (Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`, Stacks Tag 030W) and a primitive
element `y` of `K/k(t)` which, after clearing denominators, is integral over `k[t]` (Stacks Tag
0551, `Field.exists_integral_primitive_element_of_isFractionRing`). So `K` is the function field of
the hypersurface `P(t, Y) = 0` cut out by the monic minimal polynomial `P` of `y` over `k[t]`, and
`∂P/∂Y` does not vanish at `y`.

Every finitely generated `k`-subalgebra `B` of `K` lies in the localization of `k[t, y]` at a
single nonzero `g ∈ k[t]`. Hence a point of the hypersurface with `g ≠ 0` gives a point of `B`.

## Main results

* `Field.exists_primitive_hypersurface_model`: the separating basis `t`, the element `y` and its
  minimal polynomial `P`, monic, generating the kernel of evaluation, with nonvanishing derivative
  at `y`.
* `Field.exists_nonempty_algHom_of_hypersurface_model`: for a finitely generated subalgebra `B`
  there is `g ∈ k[t]`, nonzero at `t`, such that every `k`-algebra map `k[t][Y] → F` to a field
  killing `P` and not killing `g` yields a `k`-algebra map `B → F`.

## References

* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
-/

@[expose] public section

universe u

open Polynomial

namespace Field

/-- **A hypersurface model of a finitely generated extension of a perfect field.** Let `K/k` be a
finitely generated field extension of a perfect field which is not algebraic. Then there are a
separating transcendence basis `t₀, …, tₙ` of `K/k` and an element `y ∈ K` with
`K = k(t₀, …, tₙ, y)`, integral over `k[t]`, whose minimal polynomial `P ∈ k[t][Y]` is monic,
generates the kernel of evaluation `k[t][Y] → K` at `y`, and has a derivative that does not vanish
at `y`. -/
theorem exists_primitive_hypersurface_model (k K : Type u) [Field k] [PerfectField k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] {z : K} (hz : Transcendental k z) :
    ∃ (n : ℕ) (t : Fin (n + 1) → K) (y : K) (P : Polynomial (MvPolynomial (Fin (n + 1)) k)),
      AlgebraicIndependent k t ∧ P.Monic ∧
      (∀ f, eval₂ (MvPolynomial.aeval t).toRingHom y f = 0 ↔ P ∣ f) ∧
      eval₂ (MvPolynomial.aeval t).toRingHom y (derivative P) ≠ 0 ∧
      IntermediateField.adjoin k (Set.range t ∪ {y}) = ⊤ := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have : IsEmpty ((∅ : Finset K) : Set K) := by simp
    exact hz ((hs.isEmpty_iff_isAlgebraic.mp inferInstance).isAlgebraic z)
  obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by have := hne.card_pos; lia⟩
  let e : (s : Set K) ≃ Fin (n + 1) := s.equivFin.trans (finCongr hn)
  let t : Fin (n + 1) → K := fun i => (e.symm i : K)
  have ht : AlgebraicIndependent k t := hs.1.comp e.symm e.symm.injective
  have hrange : Set.range t = (s : Set K) :=
    (e.symm.surjective.range_comp _).trans Subtype.range_coe
  set M := IntermediateField.adjoin k (Set.range t) with hM
  have : Algebra.IsSeparable M K := by rwa [hM, hrange]
  have : Algebra.EssFiniteType M K := Algebra.EssFiniteType.of_comp k M K
  have : FiniteDimensional M K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let R0 := MvPolynomial (Fin (n + 1)) k
  let tM : Fin (n + 1) → M := fun i => ⟨t i, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
  let : Algebra R0 M := (MvPolynomial.aeval tM).toAlgebra
  have hval : ∀ f : R0, (algebraMap R0 M f : K) = MvPolynomial.aeval t f := by
    intro f
    show (IsScalarTower.toAlgHom k M K) (MvPolynomial.aeval tM f) = _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  have hinj : Function.Injective (algebraMap R0 M) := fun a b hab =>
    ht (by rw [← hval, ← hval, hab])
  have : FaithfulSMul R0 M := (faithfulSMul_iff_algebraMap_injective R0 M).mpr hinj
  have : IsFractionRing R0 M := by
    refine IsFractionRing.of_field R0 M fun w => ?_
    obtain ⟨r, hr, q, hq, hw⟩ := IntermediateField.mem_adjoin_iff_div.mp w.2
    rw [Algebra.adjoin_range_eq_range_aeval] at hr hq
    obtain ⟨a, rfl⟩ := hr
    obtain ⟨b, rfl⟩ := hq
    refine ⟨a, b, Subtype.ext ?_⟩
    rw [hw, IntermediateField.coe_div, hval, hval]
    rfl
  obtain ⟨F, β, hFm, hFmin, hβ⟩ :=
    Field.exists_integral_primitive_element_of_isFractionRing (R := R0) (K := M) (L := K)
  let : Algebra R0 K := ((algebraMap M K).comp (algebraMap R0 M)).toAlgebra
  have : IsScalarTower R0 M K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAeq : (MvPolynomial.aeval t).toRingHom = algebraMap R0 K :=
    RingHom.ext fun f => (hval f).symm
  have : Module.IsTorsionFree R0 K := by
    rwa [Module.isTorsionFree_iff_algebraMap_injective, ← hAeq]
  have hint : IsIntegral R0 β := ⟨F, hFm, by
    rw [← aeval_def, ← aeval_map_algebraMap M, hFmin, minpoly.aeval]⟩
  have hmin : minpoly R0 β = F := by
    apply map_injective (algebraMap R0 M) hinj
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' M hint, hFmin]
  refine ⟨n, t, β, F, ht, hFm, fun f => ?_, ?_, ?_⟩
  · rw [hAeq, ← aeval_def, ← hmin]
    exact minpoly.isIntegrallyClosed_dvd_iff hint f
  · rw [hAeq, ← aeval_def, ← aeval_map_algebraMap M, ← derivative_map, hFmin]
    exact (Algebra.IsSeparable.isSeparable M β).aeval_derivative_ne_zero (minpoly.aeval M β)
  · rw [← IntermediateField.adjoin_adjoin_left, ← hM, hβ, IntermediateField.restrictScalars_top]

/-- **Points of a hypersurface model give points.** Let `t` be algebraically independent over `k`
in `K` and let `y ∈ K` be such that `K = k(t, y)` and the kernel of evaluation
`k[t][Y] → K` at `y` is generated by a monic `P`. For every finitely generated `k`-subalgebra `B`
of `K` there is `g ∈ k[t]`, nonzero at `t`, such that every `k`-algebra map `k[t][Y] → F` to a
field killing `P` and not killing `g` gives a `k`-algebra map `B → F`. -/
theorem exists_nonempty_algHom_of_hypersurface_model {k K : Type u} [Field k] [Field K]
    [Algebra k K] {n : ℕ} {t : Fin (n + 1) → K} (ht : AlgebraicIndependent k t) {y : K}
    {P : Polynomial (MvPolynomial (Fin (n + 1)) k)} (hP : P.Monic)
    (hker : ∀ f, eval₂ (MvPolynomial.aeval t).toRingHom y f = 0 ↔ P ∣ f)
    (hgen : IntermediateField.adjoin k (Set.range t ∪ {y}) = ⊤)
    (B : Subalgebra k K) [Algebra.FiniteType k B] :
    ∃ g : MvPolynomial (Fin (n + 1)) k, MvPolynomial.aeval t g ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Algebra k F]
        (ψ : Polynomial (MvPolynomial (Fin (n + 1)) k) →ₐ[k] F),
        ψ P = 0 → ψ (C g) ≠ 0 → Nonempty (B →ₐ[k] F) := by
  classical
  let R0 := MvPolynomial (Fin (n + 1)) k
  let : Algebra R0 K := (MvPolynomial.aeval t).toAlgebra
  have hR0 : ∀ r : R0, algebraMap R0 K r = MvPolynomial.aeval t r := fun _ => rfl
  have hker' : ∀ f : R0[X], aeval y f = 0 ↔ P ∣ f := hker
  have hyint : IsIntegral R0 y := ⟨P, hP, (hker' P).mpr dvd_rfl⟩
  let S : Subalgebra R0 K := Algebra.adjoin R0 {y}
  have hSmem : ∀ z ∈ S, ∃ f : R0[X], z = aeval y f := fun z hz => by
    obtain ⟨f, rfl⟩ := (Algebra.adjoin_singleton_eq_range_aeval R0 y).le hz
    exact ⟨f, rfl⟩
  have hle : Algebra.adjoin k (Set.range t ∪ {y}) ≤ S.restrictScalars k := by
    rw [Algebra.adjoin_le_iff]
    rintro z (⟨i, rfl⟩ | rfl)
    · have : algebraMap R0 K (MvPolynomial.X i) = t i := by simp [hR0]
      rw [← this]
      exact S.algebraMap_mem _
    · exact Algebra.self_mem_adjoin_singleton R0 _
  have hden : ∀ z : K, ∃ g : R0, MvPolynomial.aeval t g ≠ 0 ∧ ∃ f : R0[X],
      MvPolynomial.aeval t g * z = aeval y f := by
    intro z
    have hz : z ∈ IntermediateField.adjoin k (Set.range t ∪ {y}) :=
      hgen ▸ IntermediateField.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    have hb' : b ∈ S := hle hb
    by_cases hb0 : b = 0
    · exact ⟨1, by simp, 0, by simp [hb0]⟩
    have hbS : (⟨b, hb'⟩ : S) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have hbint : IsIntegral R0 (⟨b, hb'⟩ : S) :=
      (isIntegral_algHom_iff S.val Subtype.val_injective).mp (adjoin_le_integralClosure hyint hb')
    have hcomap := Ideal.comap_ne_bot_of_integral_mem hbS (Ideal.mem_span_singleton_self _) hbint
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hr)
    have hcK : (c : K) * b = algebraMap R0 K r := congrArg Subtype.val hc
    obtain ⟨f, hf⟩ := hSmem _ (S.mul_mem c.2 (hle ha))
    refine ⟨r, fun h => hr0 (ht (by rw [h, map_zero])), f, ?_⟩
    rw [← hR0, ← hcK, ← hf]
    field_simp
  obtain ⟨SB, hSB⟩ := Algebra.FiniteType.out (R := k) (A := B)
  choose gs hgs fs hfs using fun b : B => hden b
  let g : R0 := ∏ b ∈ SB, gs b
  have hg : MvPolynomial.aeval t g ≠ 0 := by
    simp only [g, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun b _ => hgs b
  have hKden : ∀ z ∈ Algebra.adjoin k (B.val '' (SB : Set B)),
      ∃ m : ℕ, ∃ f : R0[X], MvPolynomial.aeval t g ^ m * z = aeval y f := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨b, hb, rfl⟩ := hz
      refine ⟨1, C (∏ b' ∈ SB.erase b, gs b') * fs b, ?_⟩
      rw [pow_one, map_mul, aeval_C, ← hfs, hR0, ← mul_assoc, ← map_mul,
        Finset.prod_erase_mul _ _ hb]
      rfl
    | algebraMap c =>
      refine ⟨0, C (algebraMap k R0 c), ?_⟩
      rw [pow_zero, one_mul, aeval_C, hR0, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
    | add z w _ _ hz hw =>
      obtain ⟨m, f, hf⟩ := hz
      obtain ⟨m', f', hf'⟩ := hw
      refine ⟨m + m', C (g ^ m') * f + C (g ^ m) * f', ?_⟩
      simp only [map_add, map_mul, aeval_C, hR0, map_pow, ← hf, ← hf']
      ring
    | mul z w _ _ hz hw =>
      obtain ⟨m, f, hf⟩ := hz
      obtain ⟨m', f', hf'⟩ := hw
      refine ⟨m + m', f * f', ?_⟩
      rw [map_mul, ← hf, ← hf']
      ring
  have hBden : ∀ b : B, ∃ m : ℕ, ∃ f : R0[X], MvPolynomial.aeval t g ^ m * b = aeval y f :=
    fun b => hKden b (by rw [← AlgHom.map_adjoin, hSB]; exact ⟨b, trivial, rfl⟩)
  refine ⟨g, hg, fun F _ _ ψ hψP hψg => ?_⟩
  let I : Ideal R0[X] := Ideal.span {P}
  let q : R0[X] →ₐ[k] K := (aeval y).restrictScalars k
  have hq : ∀ f, q f = 0 ↔ f ∈ I := fun f => (hker' f).trans Ideal.mem_span_singleton.symm
  let qbar : (R0[X] ⧸ I) →ₐ[k] K := Ideal.Quotient.liftₐ I q fun f hf => (hq f).mpr hf
  have hqbar : Function.Injective qbar := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hq f).mp ha)
  let γ : R0[X] ⧸ I := Ideal.Quotient.mk I (C g)
  have hqγ : qbar γ = MvPolynomial.aeval t g := by simp [qbar, γ, q, hR0]
  let T := Localization.Away γ
  let ι : T →ₐ[k] K := IsLocalization.Away.liftAlgHom γ (f := qbar)
    (by rw [hqγ]; exact isUnit_iff_ne_zero.mpr hg)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers γ) a
    have hx : qbar x = 0 := by
      have h := congrArg ι (IsLocalization.mk'_spec T x s)
      rw [map_mul, ha, zero_mul] at h
      simpa [ι] using h.symm
    show IsLocalization.mk' T x s = 0
    rw [hqbar (hx.trans (map_zero qbar).symm), IsLocalization.mk'_zero]
  have hB : B ≤ ι.range := by
    intro b hb
    obtain ⟨m, f, hf⟩ := hBden ⟨b, hb⟩
    refine ⟨IsLocalization.mk' T (Ideal.Quotient.mk I f) (⟨γ ^ m, m, rfl⟩ : Submonoid.powers γ), ?_⟩
    show ι _ = b
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift,
      IsLocalization.lift_mk'_spec]
    show q f = qbar (γ ^ m) * b
    rw [map_pow, hqγ]
    exact hf.symm
  let toT : B →ₐ[k] T :=
    (AlgEquiv.ofInjective ι hι).symm.toAlgHom.comp (Subalgebra.inclusion hB)
  let ψbar : (R0[X] ⧸ I) →ₐ[k] F := Ideal.Quotient.liftₐ I ψ fun f hf => by
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [map_mul, hψP, zero_mul]
  let ψT : T →ₐ[k] F := IsLocalization.Away.liftAlgHom γ (f := ψbar)
    (by rw [show ψbar γ = ψ (C g) from rfl]; exact isUnit_iff_ne_zero.mpr hψg)
  exact ⟨ψT.comp toT⟩

end Field
