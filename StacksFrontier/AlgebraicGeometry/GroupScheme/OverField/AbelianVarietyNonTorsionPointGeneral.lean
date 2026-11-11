module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyNonTorsionPointCharZero
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ReductionTorsionDivisible

/-!
# Points of infinite order on an abelian variety

Let `k` be an algebraically closed field which is not an algebraic extension of a finite field,
and `A` an abelian variety over `k` of positive dimension. Then `A(k)` has a point of infinite
order. This is the fact the proof of Stacks Tag 0AFB, part (a), uses without proof.

The proof is by specialization, in every characteristic. `A` and its group law are the base
change of a commutative group scheme `𝒜`, separated and of finite type, over a finitely generated
`ℤ`-subalgebra `R ⊆ k`, which can be taken infinite: in characteristic `p` it contains an element
transcendental over `𝔽_p` (`AlgebraicGeometry.exists_grpObj_model_of_finset`). An affine open
`Spec B ⊆ 𝒜` has infinitely many `k`-points, and a spread-out Noether normalization of `B` gives
infinitely many distinct points `P_n ∈ 𝒜(k)`, `P_n` coming from `𝒜(S_n)` for a subring
`S_n ⊆ k` such that `S_n[1/f]` is spanned by `d` elements over `R[1/f]`, with `f` and `d`
independent of `n` (`exists_span_points_of_infinite`).

Suppose every point of `A(k)` is torsion. Fix a maximal ideal `𝔪₀ ∌ f` of `R` of residue
characteristic `ℓ`. The part prime to `ℓ` of the order of `P_n` is bounded
(`AlgebraicGeometry.ordCompl_addOrderOf_le_natCard`), so `Q_n = c P_n` has `ℓ`-power order
`ℓ ^ e_n` for a fixed `c`; the `e_n` are unbounded since `A(k)[ℓ ^ E c]` is finite. As
`A(k)[ℓ]` is finite, one nonzero `z ∈ A(k)[ℓ]` is `ℓ ^ (e_n - 1) Q_n` for `n` with `e_n`
arbitrarily large. Then `z` comes from `𝒜(S₁)` for `S₁ = S_{n₁}[1/f]`, a reduced Jacobson ring,
so `z` is nontrivial at some closed point `𝔫` of `Spec S₁`
(`AlgebraicGeometry.eq_of_forall_isMaximal`). But for `N` depending only on `𝔫` and `d`, `z` is
`ℓ ^ N` times the `ℓ`-power torsion point `ℓ ^ (e_n - 1 - N) Q_n ∈ 𝒜(S_n)` for some `n`, so `z`
is trivial at `𝔫` (`AlgebraicGeometry.specOverMap_mk_comp_eq_one_of_eq_pow`): a contradiction.

## Main results

* `AlgebraicGeometry.exists_not_isOfFinAddOrder_of_model_of_infinite`: the statement for a model
  over an infinite finitely generated `ℤ`-domain.
* `Stacks.Groupoids.exists_not_isOfFinAddOrder`: a point of infinite order on `A ≠ 0` when `k` is
  algebraically closed and not algebraic over a finite prime field.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- A nonzero element of a domain of finite type over `ℤ` lies outside some maximal ideal: the
ring is Jacobson, so its Jacobson radical is its nilradical `0`. -/
theorem exists_isMaximal_not_mem_of_finiteType_int [IsDomain R] [Algebra.FiniteType ℤ R] {f : R}
    (hf : f ≠ 0) : ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ f ∉ 𝔪 := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  by_contra h
  push Not at h
  have hj : f ∈ (⊥ : Ideal R).jacobson := Ideal.mem_sInf.mpr fun m hm => h m hm.2
  rw [IsJacobsonRing.out' ⊥ Ideal.isRadical_bot] at hj
  exact hf hj

variable (𝒜 : Over (Spec (.of R)))

/-- **A commutative group scheme over an infinite finitely generated `ℤ`-domain with infinitely
many `k`-points and finite `N`-torsion has a `k`-point of infinite order**, `k` an algebraically
closed field containing the base. -/
theorem exists_not_isOfFinAddOrder_of_model_of_infinite [IsDomain R] [Algebra.FiniteType ℤ R]
    [Infinite R] [GrpObj 𝒜] [IsCommMonObj 𝒜] [LocallyOfFiniteType 𝒜.hom] [QuasiCompact 𝒜.hom]
    [IsSeparated 𝒜.hom] {k : Type u} [Field k] [IsAlgClosed k] [Algebra R k]
    (hk : Function.Injective (algebraMap R k)) [Infinite (specOver R k ⟶ 𝒜)]
    (htors : ∀ N : ℕ, N ≠ 0 →
      {x : Additive (specOver R k ⟶ 𝒜) | N • x = 0}.Finite) :
    ∃ x : Additive (specOver R k ⟶ 𝒜), ¬ IsOfFinAddOrder x := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨U, hU, hinf⟩ := exists_isAffineOpen_infinite_algHom 𝒜 (k := k)
  let := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
  have : Algebra.FiniteType R Γ(𝒜.left, U) := finiteType_affineSectionsRingHom 𝒜 hU
  obtain ⟨f, hf, d, u, ρ, hρ, hspan⟩ :=
    exists_span_points_of_infinite (B := Γ(𝒜.left, U)) hk hinf
  -- the points
  let P : ℕ → (specOver R k ⟶ 𝒜) := fun n => specOverMap (ρ n) ≫ affineChart 𝒜 hU
  have hP : Function.Injective P := by
    intro n n' h
    apply hρ
    have h1 := congrArg CommaMorphism.left h
    simp only [P, Over.comp_left, specOverMap_left, affineChart, Over.homMk_left] at h1
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).mp h1)
    exact AlgHom.ext fun b => congrArg (fun φ => φ.hom b) h2
  -- the bound on the part of the orders prime to the residue characteristic at `𝔪₀`
  obtain ⟨𝔪₀, h𝔪₀, hf𝔪₀⟩ := exists_isMaximal_not_mem_of_finiteType_int hf
  obtain ⟨ℓ, C, hℓ, hC⟩ : ∃ ℓ C : ℕ, ℓ.Prime ∧ ∀ n, IsOfFinAddOrder (Additive.ofMul (P n)) →
      ordCompl[ℓ] (addOrderOf (Additive.ofMul (P n))) ≤ C := by
    have : Finite (R ⧸ 𝔪₀) := finite_quotient_of_isMaximal_of_finiteType_int 𝔪₀
    let : Field (R ⧸ 𝔪₀) := Ideal.Quotient.field 𝔪₀
    have hℓ : (ringChar (R ⧸ 𝔪₀)).Prime := CharP.char_is_prime (R ⧸ 𝔪₀) _
    obtain ⟨F, _, _, _, hF⟩ := FiniteField.exists_algHom_of_finrank_le (R ⧸ 𝔪₀) d
    let : Algebra R F := ((algebraMap (R ⧸ 𝔪₀) F).comp (Ideal.Quotient.mk 𝔪₀)).toAlgebra
    have : IsScalarTower R (R ⧸ 𝔪₀) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine ⟨ringChar (R ⧸ 𝔪₀), Nat.card (specOver R F ⟶ 𝒜), hℓ, fun n hn => ?_⟩
    obtain ⟨O, _, _, _, _, β, gk, hgk, hgkβ, hcomap, _, _, _, hrank⟩ :=
      exists_isLocalRing_of_pow_smul_mem_span hk (ρ n) u (hspan n) 𝔪₀ hf𝔪₀
    obtain ⟨τ₀⟩ := hF (IsLocalRing.ResidueField O) hrank
    have hchar : CharP (IsLocalRing.ResidueField O) (ringChar (R ⧸ 𝔪₀)) :=
      charP_of_injective_algebraMap (algebraMap (R ⧸ 𝔪₀) _).injective _
    have hPn : P n = specOverMap gk ≫ (specOverMap β ≫ affineChart 𝒜 hU) := by
      simp only [P, ← hgkβ, ← specOverMap_comp, Category.assoc]
    rw [hPn] at hn ⊢
    exact ordCompl_addOrderOf_le_natCard 𝒜 gk hgk (τ₀.restrictScalars R) hℓ hchar _ hn
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  -- `c P_n` has `ℓ`-power order `ℓ ^ e n`
  set c := C.factorial with hc
  have hc0 : c ≠ 0 := Nat.factorial_ne_zero _
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hkill : ∀ n, ∃ e : ℕ, (ℓ ^ e * c) • Additive.ofMul (P n) = 0 := by
    intro n
    have hpos := (hcon (Additive.ofMul (P n))).addOrderOf_pos
    refine ⟨(addOrderOf (Additive.ofMul (P n))).factorization ℓ, ?_⟩
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (addOrderOf (Additive.ofMul (P n))) ℓ]
    exact Nat.mul_dvd_mul_left _
      (Nat.dvd_factorial (Nat.ordCompl_pos ℓ hpos.ne') (hC n (hcon _)))
  classical
  let e : ℕ → ℕ := fun n => Nat.find (hkill n)
  have he : ∀ n, (ℓ ^ e n * c) • Additive.ofMul (P n) = 0 := fun n => Nat.find_spec (hkill n)
  have hemin : ∀ n m, m < e n → (ℓ ^ m * c) • Additive.ofMul (P n) ≠ 0 :=
    fun n m hm => Nat.find_min (hkill n) hm
  have hexp : ∀ a b : ℕ, b ≤ a → ℓ ^ (a - b) * c * ℓ ^ b = ℓ ^ a * c := by
    intro a b hab
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hab]
  have hunb : ∀ E, ∃ n, E < e n := by
    intro E
    by_contra h
    push Not at h
    have hmem : ∀ n, Additive.ofMul (P n) ∈
        {x : Additive (specOver R k ⟶ 𝒜) | (ℓ ^ E * c) • x = 0} := by
      intro n
      change (ℓ ^ E * c) • _ = 0
      rw [← hexp E (e n) (h n), mul_assoc, mul_comm c, mul_smul, he n, smul_zero]
    have := (htors (ℓ ^ E * c) (mul_ne_zero (pow_ne_zero _ hℓ0) hc0)).to_subtype
    have : Finite ℕ := Finite.of_injective
      (fun n => (⟨Additive.ofMul (P n), hmem n⟩ : {x : Additive (specOver R k ⟶ 𝒜) |
        (ℓ ^ E * c) • x = 0})) fun n n' h => hP (congrArg Subtype.val h)
    exact not_finite ℕ
  -- the elements `y n = ℓ ^ (e n - 1) c P_n` of `A(k)[ℓ]`
  let y : ℕ → Additive (specOver R k ⟶ 𝒜) := fun n => (ℓ ^ (e n - 1) * c) • Additive.ofMul (P n)
  have hyℓ : ∀ n, ℓ • y n = 0 := by
    intro n
    rcases Nat.eq_zero_or_pos (e n) with h0 | hpos
    · have h1 := he n
      rw [h0] at h1
      change ℓ • ((ℓ ^ (e n - 1) * c) • _) = 0
      rw [h0, h1, smul_zero]
    · change ℓ • ((ℓ ^ (e n - 1) * c) • _) = 0
      rw [smul_smul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, he n]
  have hy0 : ∀ n, 0 < e n → y n ≠ 0 := fun n hn => hemin n (e n - 1) (by omega)
  have hG : {x : Additive (specOver R k ⟶ 𝒜) | ℓ • x = 0}.Finite := htors ℓ hℓ0
  obtain ⟨z, -, hz0, hzinf⟩ : ∃ z ∈ {x : Additive (specOver R k ⟶ 𝒜) | ℓ • x = 0}, z ≠ 0 ∧
      ∀ E, ∃ n, E < e n ∧ y n = z := by
    by_contra h
    push Not at h
    choose! E hE using h
    obtain ⟨B, hB⟩ := (hG.image E).bddAbove
    obtain ⟨n, hn⟩ := hunb B
    exact hE (y n) (hyℓ n) (hy0 n (by omega)) n
      (lt_of_le_of_lt (hB ⟨_, hyℓ n, rfl⟩) hn) rfl
  obtain ⟨n₁, -, hn₁⟩ := hzinf 0
  -- the ring `S₁ = S_{n₁}[1/f]`
  have hf0 : algebraMap R k f ≠ 0 := by
    rwa [Ne, ← map_zero (algebraMap R k), hk.eq_iff]
  let S₁ : Subalgebra R k := (ρ n₁).range ⊔ Algebra.adjoin R {(algebraMap R k f)⁻¹}
  have hfS : (algebraMap R k f)⁻¹ ∈ S₁ :=
    (le_sup_right : Algebra.adjoin R {(algebraMap R k f)⁻¹} ≤ S₁)
      (Algebra.subset_adjoin (Set.mem_singleton _))
  have : Algebra.FiniteType R S₁ := by
    refine (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.FG.sup ?_ ?_)
    · rw [← Algebra.map_top]
      exact (Algebra.FiniteType.out (R := R) (A := Γ(𝒜.left, U))).map (ρ n₁)
    · exact ⟨{(algebraMap R k f)⁻¹}, by simp⟩
  have : Algebra.FiniteType ℤ S₁ := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : IsJacobsonRing S₁ := isJacobsonRing_of_finiteType (A := ℤ)
  let ρ₁ : Γ(𝒜.left, U) →ₐ[R] S₁ :=
    (ρ n₁).codRestrict S₁ fun b => (le_sup_left : (ρ n₁).range ≤ S₁) (AlgHom.mem_range_self _ b)
  let a₁ : specOver R S₁ ⟶ 𝒜 := specOverMap ρ₁ ≫ affineChart 𝒜 hU
  have ha₁ : specOverMap S₁.val ≫ a₁ = P n₁ := by
    rw [← Category.assoc, specOverMap_comp]
    rfl
  let z' := a₁ ^ (ℓ ^ (e n₁ - 1) * c)
  have hz' : Additive.ofMul (specOverMap S₁.val ≫ z') = z := by
    rw [MonObj.comp_pow, ha₁, ← hn₁]
    rfl
  -- a closed point of `Spec S₁` where `z` is nontrivial
  obtain ⟨𝔫, h𝔫, h𝔫z⟩ : ∃ 𝔫 : Ideal S₁, 𝔫.IsMaximal ∧
      specOverMap (Ideal.Quotient.mkₐ R 𝔫) ≫ z' ≠ 1 := by
    by_contra h
    push Not at h
    have hz1 : z' = 1 := eq_of_forall_isMaximal 𝒜 fun 𝔫 h𝔫 => by rw [h 𝔫 h𝔫, MonObj.comp_one]
    apply hz0
    rw [← hz', hz1, MonObj.comp_one]
    rfl
  obtain ⟨N, hN⟩ := specOverMap_mk_comp_eq_one_of_eq_pow 𝒜 S₁ hf0 hfS 𝔫 d hℓ
  obtain ⟨n, hn, hyn⟩ := hzinf N
  -- `z = ℓ ^ N w` with `w` of `ℓ`-power order over `S_n`
  let S := (ρ n).range
  let aₙ : specOver R S ⟶ 𝒜 := specOverMap (ρ n).rangeRestrict ≫ affineChart 𝒜 hU
  have haₙ : specOverMap S.val ≫ aₙ = P n := by
    rw [← Category.assoc, specOverMap_comp]
    rfl
  let w := aₙ ^ (ℓ ^ (e n - 1 - N) * c)
  apply h𝔫z
  refine hN S (ρ n ∘ u) (fun i => AlgHom.mem_range_self _ _) ?_ z' w (N + 1) ?_ ?_
  · rintro s ⟨b, rfl⟩
    exact hspan n b
  · apply specOverMap_comp_injective 𝒜 S.val Subtype.val_injective
    simp only
    rw [MonObj.comp_one, MonObj.comp_pow, MonObj.comp_pow, haₙ, ← pow_mul,
      show e n - 1 - N = e n - (N + 1) by omega, hexp _ _ (by omega)]
    exact congrArg Additive.toMul (he n)
  · apply Additive.ofMul.injective
    rw [hz', ← hyn, MonObj.comp_pow, haₙ, ← pow_mul, hexp _ _ (by omega)]
    rfl

end AlgebraicGeometry

namespace Stacks.Groupoids

/-- **An abelian variety `A ≠ 0` over an algebraically closed field `k` which is not an
algebraic extension of a finite prime field has a rational point of infinite order.**

This is the fact the proof of Stacks Tag 0AFB, part (a), uses without proof ("there is such a
nontorsion point as `k` is algebraically closed and not the algebraic closure of a finite field --
this is actually not trivial to prove"). The hypothesis on `k` is that of the situation of
Section 0AF8: the prime subfield `⊥` of `k` is not finite with `k` algebraic over it. -/
theorem exists_not_isOfFinAddOrder {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ (Finite (⊥ : Subfield k) ∧ Algebra.IsAlgebraic (⊥ : Subfield k) k))
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) :
    ∃ a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), ¬ IsOfFinAddOrder a := by
  by_cases h0 : CharZero k
  · exact exists_not_isOfFinAddOrder_of_charZero A hA
  obtain ⟨p, hp⟩ := CharP.exists k
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact h0 (CharP.charP_to_charZero k)
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right hp0⟩
  have hfin : Finite (⊥ : Subfield k) := by
    have hle : ((⊥ : Subfield k) : Set k) ⊆ Set.range (ZMod.castHom (dvd_refl p) k) := by
      rw [← RingHom.coe_fieldRange]
      exact SetLike.coe_subset_coe.mpr bot_le
    exact ((Set.finite_range _).subset hle).to_subtype
  obtain ⟨t, ht⟩ : ∃ t : k, ¬ IsAlgebraic (⊥ : Subfield k) t := by
    by_contra h
    push Not at h
    exact hk ⟨hfin, ⟨h⟩⟩
  obtain ⟨R, _, _, _, φ, hφ, 𝒜, _, e, hlfp, hqc, hsep, hmon, ht'⟩ :=
    exists_grpObj_model_of_finset A {t}
  obtain ⟨t₀, ht₀⟩ := ht' t (Finset.mem_singleton_self t)
  have : Infinite R := by
    refine Infinite.of_injective (fun n : ℕ => t₀ ^ n) fun a b hab => ?_
    by_contra hne
    apply ht
    have h' : t ^ a = t ^ b := by
      have := congrArg φ hab
      simpa [ht₀] using this
    refine ⟨Polynomial.X ^ a - Polynomial.X ^ b, fun h => ?_, by simp [h']⟩
    have := congrArg (fun q => Polynomial.coeff q a) h
    simp [Polynomial.coeff_X_pow, hne] at this
  let : Algebra R k := φ.toAlgebra
  have : LocallyOfFiniteType 𝒜.X.hom := inferInstance
  let ψ := basePointsHom φ 𝒜 e
  have hψi : Function.Injective ψ := basePointsHom_injective φ 𝒜 e
  have hψs : Function.Surjective ψ := basePointsHom_surjective φ 𝒜 e
  have : Infinite (specOver R k ⟶ 𝒜.X) := by
    have hk' : Infinite k := inferInstance
    have h1 := cardinalMk_le_points A hA
    have : Infinite (𝟙_ (Over (Spec (.of k))) ⟶ A) :=
      Cardinal.infinite_iff.mpr ((Cardinal.infinite_iff.mp hk').trans h1)
    exact Infinite.of_surjective ψ hψs
  have htors : ∀ N : ℕ, N ≠ 0 → {x : Additive (specOver R k ⟶ 𝒜.X) | N • x = 0}.Finite := by
    intro N hN
    have hfin := finite_torsionBy_of_ne_zero A N hN
    refine Set.finite_coe_iff.mp (Finite.of_injective
      (fun x : {x : Additive (specOver R k ⟶ 𝒜.X) | N • x = 0} =>
        (⟨Additive.ofMul (ψ x.1.toMul), ?_⟩ : Submodule.torsionBy ℤ
          (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (N : ℤ))) ?_)
    · rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
      have := congrArg (fun y => Additive.ofMul (ψ y.toMul)) x.2
      simpa [toMul_nsmul, map_pow] using this
    · intro x y h
      exact Subtype.ext (Additive.toMul.injective (hψi (Additive.ofMul.injective
        (congrArg Subtype.val h))))
  obtain ⟨x, hx⟩ := exists_not_isOfFinAddOrder_of_model_of_infinite 𝒜.X (k := k) hφ htors
  refine ⟨Additive.ofMul (ψ x.toMul), fun h => hx ?_⟩
  have hinj : Function.Injective (MonoidHom.toAdditive ψ) := hψi
  rw [← addOrderOf_pos_iff] at h ⊢
  rwa [← addOrderOf_injective _ hinj x]

end Stacks.Groupoids

end
