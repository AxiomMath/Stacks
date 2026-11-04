module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Composition
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.CompleteLocalRing.NoetherianOfCotangent
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.Tangent
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The special fibre of a universal deformation ring under de Jong's conjecture

Let `R` be the universal deformation ring of `ρ₀ : π → GLₙ(𝐅_ℓ)` with determinant fixed to `δ`,
let `N ⊆ π` be a normal subgroup on which `ρ₀` is absolutely irreducible, assume `ℓ ∤ n`, and
assume that every continuous representation of `π` over `𝐅_ℓ⟦X⟧`, of any rank, has finite image
on `N`. Then `R` is Noetherian and its special fibre `R/ℓR` is finite.

`R` is Noetherian because its cotangent space is finite
(`Deformation.IsUniversalFixedDeterminantDeformation.finite_quotient_sq_sup_span`). If `R/ℓR`
were infinite it would not be Artinian, so there would be a prime `𝔮 ∋ ℓ` maximal among the
primes containing `ℓ` other than the maximal ideal. Then `S = R/𝔮` is a one-dimensional
complete local domain of characteristic `ℓ`; for `0 ≠ y ∈ 𝔪_S` the quotient `S/yS` is Artinian,
hence finite, so `S` is a finite free module over `𝐅_ℓ⟦y⟧`. Restricting scalars turns the
pushforward of the universal representation to `S` into a continuous representation over
`𝐅_ℓ⟦X⟧` of rank `n · rank S`, which by assumption has finite image on `N`. By
`Deformation.IsUniversalFixedDeterminantDeformation.eq_maximalIdeal_of_finite_image` this forces
`𝔮` to be the maximal ideal, a contradiction.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.isNoetherianRing_of_finite_image`.
* `Deformation.IsUniversalFixedDeterminantDeformation.finite_quotient_span_of_finite_image`.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped PowerSeries.WithPiTopology

/-- An additive homomorphism to a discrete group killing a power of an ideal `I` is continuous
for the `I`-adic topology. -/
theorem AddMonoidHom.continuous_adic_of_pow_le_ker {A B : Type*} [CommRing A] [AddCommGroup B]
    [TopologicalSpace B] [DiscreteTopology B] (I : Ideal A) (f : A →+ B) (k : ℕ)
    (h : ∀ x ∈ I ^ k, f x = 0) : @Continuous A B I.adicTopology _ f := by
  let : TopologicalSpace A := I.adicTopology
  have : IsTopologicalRing A := I.ringFilterBasis.isTopologicalRing
  have : IsTopologicalAddGroup B := ⟨⟩
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, nhds_discrete B, Filter.tendsto_pure]
  filter_upwards [(Ideal.hasBasis_nhds_zero_adic I).mem_of_mem (i := k) trivial] with x hx
  exact h x (by simpa using hx)

/-- An Artinian local algebra over `ZMod ℓ` with finite residue field is finite. -/
theorem IsArtinianRing.finite_of_finite_residueField {ℓ : ℕ} [Fact ℓ.Prime] (B : Type*)
    [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra (ZMod ℓ) B]
    [Finite (ResidueField B)] : Finite B := by
  have : Module.Finite (ZMod ℓ) (B ⧸ Ring.jacobson B) := by
    rw [ringJacobson_eq_maximalIdeal]
    have : Finite (B ⧸ maximalIdeal B) := ‹Finite (ResidueField B)›
    exact Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) B := IsSemiprimaryRing.finite_of_isArtinian (ZMod ℓ) B B
  exact Module.finite_of_finite (ZMod ℓ)

/-- A Noetherian local ring all of whose primes are maximal is Artinian. -/
theorem IsLocalRing.isArtinianRing_of_forall_isPrime {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (h : ∀ Q : Ideal B, Q.IsPrime → Q = maximalIdeal B) :
    IsArtinianRing B := by
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨inferInstance, Ring.KrullDimLE.mk₀ fun Q hQ => ?_⟩
  rw [h Q hQ]
  exact maximalIdeal.isMaximal B

/-- The `span {a}`-power multiple of `⊤` is the span of the image of `a ^ k`. -/
private theorem pow_span_smul_top_eq_restrictScalars {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (a : A) {x : B} (hx : algebraMap A B a = x) (k : ℕ) :
    Ideal.span {a} ^ k • (⊤ : Submodule A B) = (Ideal.span {x ^ k}).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    map_pow, hx]

/-- If `B / (x)` is finite, so is `B / (a • ⊤)` whenever `a` maps to `x`. -/
private theorem finite_quotient_span_smul_top {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) {x : B} (hx : algebraMap A B a = x) [Finite (B ⧸ Ideal.span {x})] :
    Finite (B ⧸ Ideal.span {a} • (⊤ : Submodule A B)) := by
  have e := pow_span_smul_top_eq_restrictScalars a hx 1
  rw [pow_one, pow_one] at e
  exact Finite.of_equiv _ ((Submodule.Quotient.restrictScalarsEquiv A
    (Ideal.span {x})).symm.toEquiv.trans (Submodule.quotEquivOfEq _ _ e.symm).toEquiv)

section RestrictScalars

variable {ℓ : ℕ} [Fact ℓ.Prime] {S : Type*} [CommRing S] [IsDomain S] [IsLocalRing S]
  [Algebra (ZMod ℓ) S]

omit [IsDomain S] [IsLocalRing S] [Algebra (ZMod ℓ) S] [Fact ℓ.Prime] in
/-- Substitution of an element of an ideal `I` into power series, for an `I`-adically complete
ring. -/
theorem exists_powerSeries_ringHom {Λ : Type*} [CommRing Λ] (I : Ideal S) [IsAdicComplete I S]
    (f : Λ →+* S) (t : S) (ht : t ∈ I) :
    ∃ φ : PowerSeries Λ →+* S, φ PowerSeries.X = t ∧ ∀ c, φ (PowerSeries.C c) = f c := by
  let _ : WithIdeal Λ := ⟨⊥⟩
  have : DiscreteTopology Λ := is_bot_adic_iff.1 rfl
  let _ : WithIdeal S := ⟨I⟩
  obtain ⟨hcs, ht2⟩ := (IsAdic.isAdicComplete_iff (I := I) rfl).1 ‹IsAdicComplete I S›
  have ha : MvPowerSeries.HasEval (fun _ : Unit => t) :=
    { hpow := fun _ => WithIdeal.isTopologicallyNilpotent_of_mem ht
      tendsto_zero := by simp [Filter.cofinite_eq_bot] }
  refine ⟨MvPowerSeries.eval₂Hom (φ := f) continuous_of_discreteTopology ha, ?_, fun c => ?_⟩
  · rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_X _ _ ()
  · rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_C _ _ c

/-- **Finite image by restriction of scalars.** Let `S` be a complete local domain over `𝐅_ℓ`,
`t ≠ 0` in its maximal ideal with `S/tS` finite and some power of the maximal ideal inside `tS`.
A representation `σ : π → GLₙ(S)`, continuous for the maximal-ideal-adic topology, has finite
image on `N` as soon as every continuous representation of `π` over `𝐅_ℓ⟦X⟧` does: `S` is finite
free over `𝐅_ℓ⟦t⟧`, and restricting scalars embeds `GLₙ(S)` continuously into `GLₙᵣ(𝐅_ℓ⟦X⟧)`. -/
theorem finite_image_of_restrictScalars [IsAdicComplete (maximalIdeal S) S] {t : S} (ht0 : t ≠ 0)
    (htm : t ∈ maximalIdeal S) (hfin : Finite (S ⧸ Ideal.span {t}))
    {k₀ : ℕ} (hk₀ : maximalIdeal S ^ k₀ ≤ Ideal.span {t}) {n : ℕ} {π : Type*} [Group π]
    [TopologicalSpace π] [IsTopologicalGroup π] (σ : π →* Matrix.GeneralLinearGroup (Fin n) S)
    (hσ : ∀ i j, @Continuous π S _ (maximalIdeal S).adicTopology
      fun g => (σ g : Matrix (Fin n) (Fin n) S) i j) (N : Set π)
    (hconj : ∀ (m : ℕ) (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (ρ '' N).Finite) :
    (σ '' N).Finite := by
  classical
  obtain ⟨φ, hφX, -⟩ := exists_powerSeries_ringHom (maximalIdeal S) (algebraMap (ZMod ℓ) S) t htm
  let : Algebra (PowerSeries (ZMod ℓ)) S := φ.toAlgebra
  have hsmul : ∀ (f : PowerSeries (ZMod ℓ)) (x : S), f • x = φ f * x := fun _ _ => rfl
  -- `φ` is injective
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun f hf => by_contra fun hf0 => ?_
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      rwa [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, ne_eq,
        PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff]
    rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f), map_mul, map_pow, hφX] at hf
    rcases mul_eq_zero.1 hf with h1 | h1
    · exact ht0 (pow_eq_zero_iff'.1 h1).1
    · exact (hu.map φ).ne_zero h1
  have : Module.IsTorsionFree (PowerSeries (ZMod ℓ)) S :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hφinj
  -- `S` is finite over `𝐅_ℓ⟦X⟧`
  have hmap := pow_span_smul_top_eq_restrictScalars (PowerSeries.X : PowerSeries (ZMod ℓ))
    (B := S) hφX
  have : Module.Finite (PowerSeries (ZMod ℓ)) S := by
    refine Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
      (Ideal.span {PowerSeries.X}) ?_ ?_
    · refine eq_bot_iff.2 fun x hx => ?_
      rw [Submodule.mem_bot]
      refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := maximalIdeal S)) x
        fun k => ?_
      have := (Submodule.mem_iInf _).1 hx k
      rw [hmap, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at this
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      obtain ⟨y, rfl⟩ := this
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm k)
    · have := finite_quotient_span_smul_top (PowerSeries.X : PowerSeries (ZMod ℓ)) (B := S) hφX
      exact Module.Finite.of_finite
  -- a basis and the restriction of scalars
  let b := Module.finBasis (PowerSeries (ZMod ℓ)) S
  set r := Module.finrank (PowerSeries (ZMod ℓ)) S
  let L : S →+* Matrix (Fin r) (Fin r) (PowerSeries (ZMod ℓ)) :=
    (Algebra.leftMulMatrix b).toRingHom
  have hLinj : Function.Injective L := Algebra.leftMulMatrix_injective b
  let Ψ : Matrix (Fin n) (Fin n) S →+* Matrix (Fin (n * r)) (Fin (n * r)) (PowerSeries (ZMod ℓ)) :=
    (Matrix.reindexRingEquiv (PowerSeries (ZMod ℓ)) finProdFinEquiv).toRingHom.comp
      ((Matrix.compRingEquiv (Fin n) (Fin r) (PowerSeries (ZMod ℓ))).toRingHom.comp L.mapMatrix)
  have hΨinj : Function.Injective Ψ :=
    (Matrix.reindexRingEquiv _ finProdFinEquiv).injective.comp
      ((Matrix.compRingEquiv _ _ _).injective.comp (Matrix.map_injective hLinj))
  let _ : TopologicalSpace S := (maximalIdeal S).adicTopology
  have : IsTopologicalRing S := (maximalIdeal S).ringFilterBasis.isTopologicalRing
  have hσ' : Continuous fun g => (σ g : Matrix (Fin n) (Fin n) S) :=
    continuous_pi fun i => continuous_pi fun j => hσ i j
  -- continuity of the coordinates
  have hcoord : ∀ (p q : Fin r), Continuous fun s : S => L s p q := by
    intro p q
    refine PowerSeries.WithPiTopology.continuous_of_forall_continuous_coeff fun k => ?_
    let f : S →+ ZMod ℓ := (PowerSeries.coeff k).toAddMonoidHom.comp
      ((b.coord p).toAddMonoidHom.comp (AddMonoidHom.mulRight (b q)))
    have hf : ∀ s, PowerSeries.coeff k (L s p q) = f s := fun s => by
      simp only [L, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.leftMulMatrix_eq_repr_mul,
        f, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
        LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply]
    simp only [hf]
    refine AddMonoidHom.continuous_adic_of_pow_le_ker _ f (k₀ * (k + 1)) fun x hx => ?_
    have hx' : x * b q ∈ Ideal.span {t ^ (k + 1)} := by
      rw [pow_mul] at hx
      have := Ideal.pow_right_mono hk₀ (k + 1) hx
      rw [Ideal.span_singleton_pow] at this
      exact Ideal.mul_mem_right _ _ this
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    have : x * b q = (PowerSeries.X ^ (k + 1) : PowerSeries (ZMod ℓ)) • y := by
      rw [hsmul, map_pow, hφX, ← hy, mul_comm]
    simp only [f, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
      LinearMap.toAddMonoidHom_coe, this, map_smul, Module.Basis.coord_apply, smul_eq_mul]
    show PowerSeries.coeff k (PowerSeries.X ^ (k + 1) * _) = 0
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  have hΨ : Continuous Ψ := by
    refine continuous_pi fun a => continuous_pi fun c => ?_
    have : (fun M : Matrix (Fin n) (Fin n) S => Ψ M a c) = fun M =>
        L (M (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm c).1)
          (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm c).2 := rfl
    rw [this]
    exact (hcoord _ _).comp ((continuous_apply _).comp (continuous_apply _))
  -- the restricted representation
  let ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin (n * r)) (PowerSeries (ZMod ℓ)) :=
    { toMonoidHom := (Units.map Ψ.toMonoidHom).comp σ
      continuous_toFun := by
        refine Units.continuous_iff.2 ⟨hΨ.comp hσ', ?_⟩
        have : (fun g => (((Units.map Ψ.toMonoidHom).comp σ g)⁻¹ :
            Matrix.GeneralLinearGroup (Fin (n * r)) (PowerSeries (ZMod ℓ))).val) =
            (Ψ ∘ fun g => (σ g : Matrix (Fin n) (Fin n) S)) ∘ fun g => g⁻¹ := by
          funext g
          simp [map_inv]
        exact this ▸ (hΨ.comp hσ').comp continuous_inv }
  have hρ : ρ '' N = Units.map Ψ.toMonoidHom '' (σ '' N) := by
    rw [Set.image_image]
    rfl
  exact (hρ ▸ hconj (n * r) ρ).of_finite_image (Units.map_injective hΨinj).injOn

end RestrictScalars

namespace Deformation.IsUniversalFixedDeterminantDeformation

universe u v

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

/-- The residue field of a universal deformation ring is the image of `ℤ_[ℓ]`. -/
theorem surjective_mk_maximalIdeal_comp_algebraMap
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R)).comp (algebraMap ℤ_[ℓ] R)) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := ℓ)) (reduce a)
  refine ⟨z, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, ← h.ker_reduce, RingHom.mem_ker, map_sub,
    h.reduce_algebraMap, hz, sub_self]

/-- **Noetherianity under de Jong's conjecture.** -/
theorem isNoetherianRing_of_finite_image [IsTopologicalGroup π]
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (N : Subgroup π) [N.Normal] (hirr : IsAbsolutelyIrreducible fun g : N => ρ₀ g)
    (hn : ¬ ℓ ∣ n)
    (hconj : ∀ (m : ℕ) (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (ρ '' (N : Set π)).Finite) :
    IsNoetherianRing R := by
  classical
  have := h.isAdicComplete
  set I₀ := maximalIdeal R ^ 2 ⊔ Ideal.span {algebraMap ℤ_[ℓ] R ℓ}
  have hT := h.finite_quotient_sq_sup_span N hirr hn hconj
  set mk : R →+* R ⧸ I₀ := Ideal.Quotient.mk I₀
  choose lift hlift using fun t : R ⧸ I₀ => Ideal.Quotient.mk_surjective t
  set G : Set R := insert (algebraMap ℤ_[ℓ] R ℓ)
    (lift '' {t | lift t ∈ maximalIdeal R})
  have hGfin : G.Finite := ((Set.toFinite _).image _).insert _
  have hGm : G ⊆ maximalIdeal R := by
    rintro x (rfl | ⟨t, ht, rfl⟩)
    · exact h.algebraMap_mem_maximalIdeal
    · exact ht
  refine IsLocalRing.isNoetherianRing_of_fg_maximalIdeal (ℓ := ℓ)
    h.surjective_mk_maximalIdeal_comp_algebraMap
    (IsLocalRing.fg_maximalIdeal_of_le_span_sup_sq G hGfin hGm fun a ha => ?_)
  have hla : lift (mk a) - a ∈ I₀ := by
    rw [← Ideal.Quotient.eq, hlift]
  have hI₀m : I₀ ≤ maximalIdeal R := sup_le (Ideal.pow_le_self two_ne_zero)
    ((Ideal.span_singleton_le_iff_mem _).2 h.algebraMap_mem_maximalIdeal)
  have hlm : lift (mk a) ∈ maximalIdeal R := by
    simpa using (maximalIdeal R).add_mem ha (hI₀m hla)
  have h1 : lift (mk a) ∈ Ideal.span G ⊔ maximalIdeal R ^ 2 :=
    Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨mk a, hlm, rfl⟩))
  have h2 : a - lift (mk a) ∈ Ideal.span G ⊔ maximalIdeal R ^ 2 := by
    rw [← neg_sub]
    refine (Ideal.neg_mem_iff _).2 ?_
    have hle : I₀ ≤ Ideal.span G ⊔ maximalIdeal R ^ 2 := by
      refine sup_le le_sup_right ?_
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
    exact hle hla
  simpa using Ideal.add_mem _ h1 h2

/-- **Finiteness of the special fibre under de Jong's conjecture.** Let `N` be a normal subgroup
of `π` on which `ρ₀` is absolutely irreducible, assume `ℓ ∤ n`, and assume that every continuous
representation of `π` over `𝐅_ℓ⟦X⟧`, of any rank, has finite image on `N`. Then `R/ℓR` is
finite. -/
theorem finite_quotient_span_of_finite_image [IsTopologicalGroup π]
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (N : Subgroup π) [N.Normal] (hirr : IsAbsolutelyIrreducible fun g : N => ρ₀ g)
    (hn : ¬ ℓ ∣ n)
    (hconj : ∀ (m : ℕ) (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (ρ '' (N : Set π)).Finite) :
    Finite (R ⧸ Ideal.span {algebraMap ℤ_[ℓ] R ℓ}) := by
  classical
  have := h.isAdicComplete
  have hnoeth := h.isNoetherianRing_of_finite_image N hirr hn hconj
  set P₀ := Ideal.span {algebraMap ℤ_[ℓ] R ℓ}
  have hP₀m : P₀ ≤ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).2 h.algebraMap_mem_maximalIdeal
  /- An Artinian quotient containing `ℓ` with the residue field of `R` is finite. -/
  have hartfin : ∀ J : Ideal R, P₀ ≤ J → J ≤ maximalIdeal R →
      (∀ Q : Ideal R, Q.IsPrime → J ≤ Q → Q = maximalIdeal R) → Finite (R ⧸ J) := by
    intro J hP₀J hJm hJ
    have : IsLocalRing (R ⧸ J) := h.isLocalRing_quotient_of_le J hJm
    have : CharP (R ⧸ J) ℓ := h.charP_quotient J (hP₀J (Ideal.mem_span_singleton_self _))
    let : Algebra (ZMod ℓ) (R ⧸ J) := ZMod.algebra (R ⧸ J) ℓ
    have : IsArtinianRing (R ⧸ J) := IsLocalRing.isArtinianRing_of_forall_isPrime fun Q hQ => by
      have hc := hJ (Q.comap (Ideal.Quotient.mk J)) (hQ.comap _) fun a ha => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
        exact Q.zero_mem
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hc,
        IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    have : Finite (ResidueField (R ⧸ J)) :=
      Finite.of_surjective _ (h.residue_comp_algebraMap_surjective J)
    exact IsArtinianRing.finite_of_finite_residueField (ℓ := ℓ) _
  by_contra hinf
  have hex : ({𝔮 : Ideal R | 𝔮.IsPrime ∧ P₀ ≤ 𝔮 ∧ 𝔮 ≠ maximalIdeal R}).Nonempty := by
    by_contra hall
    refine hinf (hartfin P₀ le_rfl hP₀m fun Q hQ hP₀Q => by_contra fun hQm => hall ?_)
    exact ⟨Q, hQ, hP₀Q, hQm⟩
  obtain ⟨𝔮, ⟨h𝔮p, hP₀𝔮, h𝔮m⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 hnoeth _ hex
  have h𝔮le : 𝔮 ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal h𝔮p.ne_top
  obtain ⟨a, ham, ha𝔮⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h𝔮le h𝔮m)
  -- every prime strictly above `𝔮` is the maximal ideal
  have habove : ∀ Q : Ideal R, Q.IsPrime → 𝔮 ≤ Q → a ∈ Q → Q = maximalIdeal R := by
    intro Q hQ h𝔮Q haQ
    by_contra hQm
    exact hmax Q ⟨hQ, hP₀𝔮.trans h𝔮Q, hQm⟩ (lt_of_le_of_ne h𝔮Q fun e => ha𝔮 (e ▸ haQ))
  set J := 𝔮 ⊔ Ideal.span {a}
  have hJm : J ≤ maximalIdeal R := sup_le h𝔮le ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have hJfin : Finite (R ⧸ J) := hartfin J (hP₀𝔮.trans le_sup_left) hJm fun Q hQ hJQ =>
    habove Q hQ (le_sup_left.trans hJQ)
      (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  -- the quotient `S = R/𝔮`
  set S := R ⧸ 𝔮
  have : IsLocalRing S := h.isLocalRing_quotient_of_le 𝔮 h𝔮le
  have : CharP S ℓ := h.charP_quotient 𝔮 (hP₀𝔮 (Ideal.mem_span_singleton_self _))
  let : Algebra (ZMod ℓ) S := ZMod.algebra S ℓ
  have hcompS : IsAdicComplete (maximalIdeal S) S := (quotient_isNoetherianCompleteLocalRing
    ⟨inferInstance, inferInstance, h.isAdicComplete⟩ 𝔮 h𝔮p.ne_top).isComplete
  set mk : R →+* S := Ideal.Quotient.mk 𝔮
  set t : S := mk a
  have ht0 : t ≠ 0 := fun e => ha𝔮 (Ideal.Quotient.eq_zero_iff_mem.1 e)
  have htm : t ∈ maximalIdeal S := (h.mk_mem_maximalIdeal_quotient_iff 𝔮 a).2 ham
  have hspanJ : (Ideal.span {t}).comap mk = J := by
    have e : Ideal.span {t} = (Ideal.span {a}).map mk := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]
  have htfin : Finite (S ⧸ Ideal.span {t}) := by
    refine Finite.of_surjective (Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp mk)
      fun x hx => ?_) ?_
    · rwa [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hspanJ]
    · intro z
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
      exact ⟨Ideal.Quotient.mk J x, rfl⟩
  -- a power of the maximal ideal of `S` lies in `tS`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, maximalIdeal S ^ k₀ ≤ Ideal.span {t} := by
    have : IsLocalRing (R ⧸ J) := h.isLocalRing_quotient_of_le J hJm
    have : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite (R ⧸ J) (R ⧸ J)
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ J)
    rw [Ideal.jacobson_bot, ringJacobson_eq_maximalIdeal] at hk
    refine ⟨k, ?_⟩
    rw [← IsLocalRing.map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow, Ideal.map_le_iff_le_comap, hspanJ]
    intro x hx
    have : Ideal.Quotient.mk J x ∈ maximalIdeal (R ⧸ J) ^ k := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
        ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    rwa [hk, Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  -- the pushforward to `S` has finite image on `N`
  have hmk_cont : @Continuous R S _ (maximalIdeal S).adicTopology mk := by
    rw [h.isAdicTopology]
    refine (mk.continuous_adic_iff _ _).2 ⟨1, le_rfl, fun x hx => ?_⟩
    rw [pow_one] at hx
    exact (h.mk_mem_maximalIdeal_quotient_iff 𝔮 x).2 hx
  have hfinS := finite_image_of_restrictScalars (ℓ := ℓ) ht0 htm htfin hk₀
    ((Matrix.GeneralLinearGroup.map mk).comp ρuniv.toMonoidHom)
    (fun i j => by
      have h0 : Continuous fun g => (ρuniv g : Matrix (Fin n) (Fin n) R) :=
        Units.continuous_val.comp ρuniv.continuous_toFun
      exact @Continuous.comp _ _ _ _ _ (maximalIdeal S).adicTopology _ _ hmk_cont
        ((continuous_apply_apply i j).comp h0)) N hconj
  exact h𝔮m (h.eq_maximalIdeal_of_finite_image N hirr hn 𝔮
    (hP₀𝔮 (Ideal.mem_span_singleton_self _)) hfinS)

/-- **Finiteness of the universal deformation ring under de Jong's conjecture.** Let `N` be a
normal subgroup of `π` on which `ρ₀` is absolutely irreducible, assume `ℓ ∤ n`, and assume that
every continuous representation of `π` over `𝐅_ℓ⟦X⟧`, of any rank, has finite image on `N`. Then
the universal deformation ring of `ρ₀` with determinant fixed to `δ` is finite over `ℤ_[ℓ]`. -/
theorem moduleFinite_of_finite_image [IsTopologicalGroup π]
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (N : Subgroup π) [N.Normal] (hirr : IsAbsolutelyIrreducible fun g : N => ρ₀ g)
    (hn : ¬ ℓ ∣ n)
    (hconj : ∀ (m : ℕ) (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (ρ '' (N : Set π)).Finite) :
    Module.Finite ℤ_[ℓ] R := by
  have := h.finite_quotient_span_of_finite_image N hirr hn hconj
  refine h.finite ?_
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact finite_quotient_span_smul_top (ℓ : ℤ_[ℓ]) (B := R) rfl

end Deformation.IsUniversalFixedDeterminantDeformation
