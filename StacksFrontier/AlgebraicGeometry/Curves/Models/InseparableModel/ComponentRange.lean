module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Components

/-!
# A regular model with an inseparable component: the special fibre is the union of two lines

Every point of the model `X` of `Stacks.Models.InseparableModel` lying over the closed point of
`Spec R` lies on the strict transform `range jC₁` or on the exceptional curve `range jE`, and
neither of these two closed sets contains the other.

A point `x` over the closed point has `π ∈ 𝔭_x`. If `z₀₀ ∈ 𝔭_x`, then `z₁₀ ∈ 𝔭_x` by
`z₁₀² = π z₀₀ z₀₁ + t z₀₀²`, and `A → A/𝔭_x` factors through `k[a, b]`; otherwise
`w = z₁₀/z₀₀` is a square root of `t` in `Frac(A/𝔭_x)` and `A → Frac(A/𝔭_x)` factors through
`κ[a, b]`, `θ ↦ w`. In both cases the homogeneous core of the kernel of the second map is a point
of the projective line over `x` (`Stacks.Models.InseparableModel.mem_range_map_of_ker`).

## Main results

* `Stacks.Models.InseparableModel.mem_range_map_of_ker`: a point whose prime is the kernel of a
  map through a graded map `f` to a domain lies in the image of `Proj.map f`.
* `Stacks.Models.InseparableModel.mem_range_jC₁_or_mem_range_jE`
* `Stacks.Models.InseparableModel.exists_mem_range_jE_notMem_range_jC₁`
* `Stacks.Models.InseparableModel.exists_mem_range_jC₁_notMem_range_jE`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {A B σ τ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A homogeneous element lies in a homogeneous prime of `Proj.map f` exactly when its image
does. -/
theorem mem_map_asHomogeneousIdeal_iff (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤
    (HomogeneousIdeal.irrelevant 𝒜).map f) (y : Proj ℬ) (a : A) :
    a ∈ (Proj.map f hf y).asHomogeneousIdeal ↔ f a ∈ y.asHomogeneousIdeal :=
  Iff.rfl

/-- **A point lies in the image of `Proj.map f` as soon as its homogeneous prime is the kernel of
a map through `f` to a domain.** If `ψ : B → L` is a ring map to a domain with
`ψ (f a) = 0 ↔ a ∈ 𝔭` for all `a`, the homogeneous core of `ker ψ` is a point of `Proj ℬ` over
`𝔭`. -/
theorem mem_range_map_of_ker (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤
    (HomogeneousIdeal.irrelevant 𝒜).map f) {L : Type} [CommRing L] [IsDomain L] (ψ : B →+* L)
    (x : Proj 𝒜) (hx : ∀ a, ψ (f a) = 0 ↔ a ∈ x.asHomogeneousIdeal) :
    x ∈ Set.range (Proj.map f hf) := by
  set Q := (RingHom.ker ψ).homogeneousCore ℬ
  have hhom : ∀ {i : ℕ} {a : A}, a ∈ 𝒜 i → (f a ∈ Q ↔ a ∈ x.asHomogeneousIdeal) := by
    intro i a ha
    rw [← hx a, ← RingHom.mem_ker]
    exact ⟨fun h => Ideal.toIdeal_homogeneousCore_le ℬ _ h,
      fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨i, GradedFunLike.map_mem f ha⟩ h⟩
  have hmem : ∀ a, f a ∈ Q ↔ a ∈ x.asHomogeneousIdeal := by
    intro a
    rw [← HomogeneousIdeal.mem_iff, Q.isHomogeneous.mem_iff, ← HomogeneousIdeal.mem_iff,
      x.asHomogeneousIdeal.isHomogeneous.mem_iff]
    refine forall_congr' fun i => ?_
    rw [← f.map_directSumDecompose]
    exact hhom (Subtype.prop _)
  have hirr : ¬ HomogeneousIdeal.irrelevant ℬ ≤ Q := by
    intro hle
    apply x.not_irrelevant_le
    intro a ha
    rw [← HomogeneousIdeal.mem_iff, x.asHomogeneousIdeal.isHomogeneous.mem_iff]
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h0 : (DirectSum.decompose 𝒜 a 0 : A) = 0 :=
        (HomogeneousIdeal.mem_irrelevant_iff 𝒜 a).1 ha
      rw [h0]
      exact zero_mem _
    · exact HomogeneousIdeal.mem_iff.mpr ((hhom (Subtype.prop (DirectSum.decompose 𝒜 a i))).1
        (hle (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi
          (GradedFunLike.map_mem f (Subtype.prop _)))))
  refine ⟨⟨Q, (RingHom.ker_isPrime ψ).homogeneousCore, hirr⟩, ProjectiveSpectrum.ext ?_⟩
  ext a
  exact (mem_map_asHomogeneousIdeal_iff f hf _ a).trans (hmem a)

end General

/-! ### The model -/

/-- The class of `π` in `A`. -/
private abbrev πA : A := Ideal.Quotient.mk J.toIdeal (MvPolynomial.C π)

/-- The class of `t` in `A`. -/
private abbrev tA : A := Ideal.Quotient.mk J.toIdeal (MvPolynomial.C tR)

/-- The class of a constant of `R` in `A`, through `k → R`, `c ↦ c`. -/
private def kA : k →+* A :=
  (Ideal.Quotient.mk J.toIdeal).comp (MvPolynomial.C.comp (PowerSeries.C (R := k)))

private theorem rel₁ : zA 2 ^ 2 = πA * zA 0 * zA 1 + tA * zA 0 ^ 2 := by
  have h := mk_gen_eq_zero (q := q₁) (by simp [gens])
  simp only [q₁, map_sub, map_add, map_mul, map_pow] at h
  exact (sub_eq_zero.mp h).symm

/-- A point of `X` over the closed point of `Spec R` contains `π`. -/
private theorem πA_mem (x : XR) (hx : X_to_R x = IsLocalRing.closedPoint R) :
    πA ∈ x.asHomogeneousIdeal := by
  have hm : π ∈ (X_to_R x).asIdeal := by
    rw [hx]
    exact (IsLocalRing.mem_maximalIdeal π).2 irreducible_π.not_isUnit
  have h2 : algebraMap R (grading 0) π ∈ (Proj.toSpecZero grading x).asIdeal := hm
  have h3 : x ∉ Proj.basicOpen grading ((algebraMap R (grading 0) π : grading 0) : A) := by
    rw [← Proj.toSpecZero_preimage_basicOpen]
    exact fun h => h h2
  rw [Proj.mem_basicOpen, not_not] at h3
  simpa [SetLike.GradeZero.coe_algebraMap, IsScalarTower.algebraMap_apply R P A] using h3

/-- Modulo a prime containing `π`, a constant of `R` agrees with its residue. -/
private theorem kA_constantCoeff_sub_mem {𝔭 : Ideal A} (h𝔭 : πA ∈ 𝔭) (r : R) :
    Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r) - kA (PowerSeries.constantCoeff r) ∈ 𝔭 := by
  obtain ⟨s, hs⟩ : PowerSeries.X ∣ r - PowerSeries.C (PowerSeries.constantCoeff r) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have : Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r) - kA (PowerSeries.constantCoeff r) =
      πA * Ideal.Quotient.mk J.toIdeal (MvPolynomial.C s) := by
    simp only [kA, RingHom.comp_apply, ← map_sub, ← map_mul, π, hs]
  rw [this]
  exact Ideal.mul_mem_right _ _ h𝔭

/-- The two ring maps `A → L` out of `P = R[z]` agree as soon as they agree on the constants and
on the variables. -/
private theorem ringHom_ext_A {L : Type} [CommRing L] {f g : A →+* L}
    (hC : ∀ r : R, f (Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r)) =
      g (Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r)))
    (hX : ∀ i, f (zA i) = g (zA i)) : f = g :=
  Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => hC r) fun i => hX i)

/-! ### The classification -/

private theorem mem_range_jC₁_of_mem (x : XR) (hπ : πA ∈ x.asHomogeneousIdeal)
    (h0 : zA 0 ∈ x.asHomogeneousIdeal) : x ∈ Set.range jC₁ := by
  set 𝔭 := x.asHomogeneousIdeal.toIdeal
  have : 𝔭.IsPrime := x.isPrime
  have hπ' : πA ∈ 𝔭 := hπ
  have h0' : zA 0 ∈ 𝔭 := h0
  have h2 : zA 2 ∈ 𝔭 := by
    refine x.isPrime.mem_of_pow_mem 2 ?_
    rw [rel₁]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ'))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h0' 2 two_pos))
  let q := Ideal.Quotient.mk 𝔭
  let ψ : MvPolynomial (Fin (1 + 1)) k →+* A ⧸ 𝔭 :=
    MvPolynomial.eval₂Hom (q.comp kA) ![q (zA 1), q (zA 3)]
  have hψ : ψ.comp ringC₁ = q := by
    refine ringHom_ext_A (fun r => ?_) (fun i => ?_)
    · change ψ (evC₁ (MvPolynomial.C r)) = _
      have h := kA_constantCoeff_sub_mem hπ' r
      rw [← Ideal.Quotient.eq] at h
      simp only [ψ, evC₁, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        RingHom.algebraMap_toAlgebra]
      exact h.symm
    · change ψ (evC₁ (MvPolynomial.X i)) = q (zA i)
      fin_cases i
      · simpa [ψ, evC₁] using (Ideal.Quotient.eq_zero_iff_mem.mpr h0').symm
      · simp [ψ, evC₁]
      · simpa [ψ, evC₁] using (Ideal.Quotient.eq_zero_iff_mem.mpr h2).symm
      · simp [ψ, evC₁]
  refine mem_range_map_of_ker φC₁ irrelevant_le_map_φC₁ ψ x fun a => ?_
  change (ψ.comp ringC₁) a = 0 ↔ _
  rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
  exact HomogeneousIdeal.mem_iff

private theorem mem_range_jE_of_notMem (x : XR) (hπ : πA ∈ x.asHomogeneousIdeal)
    (h0 : zA 0 ∉ x.asHomogeneousIdeal) : x ∈ Set.range jE := by
  set 𝔭 := x.asHomogeneousIdeal.toIdeal
  have : 𝔭.IsPrime := x.isPrime
  have hπ' : πA ∈ 𝔭 := hπ
  have h0' : zA 0 ∉ 𝔭 := h0
  let ι : A →+* FractionRing (A ⧸ 𝔭) :=
    (algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp (Ideal.Quotient.mk 𝔭)
  have hιinj : ∀ a, ι a = 0 ↔ a ∈ 𝔭 := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff' (map_zero _)
  have hu : ι (zA 0) ≠ 0 := fun h => h0' ((hιinj _).1 h)
  have hπ0 : ι πA = 0 := (hιinj _).2 hπ'
  set w : FractionRing (A ⧸ 𝔭) := ι (zA 2) / ι (zA 0) with hwdef
  have hw2 : w * ι (zA 0) = ι (zA 2) := div_mul_cancel₀ _ hu
  have hw : w ^ 2 = (ι.comp kA) t := by
    have h := congrArg ι rel₁
    simp only [map_add, map_mul, map_pow, hπ0, zero_mul, zero_add] at h
    change w ^ 2 = ι tA
    rw [hwdef, div_pow, div_eq_iff (pow_ne_zero 2 hu), h]
  have h3 : ι (zA 3) = w * ι (zA 1) := by
    have h := congrArg ι zA_rel₀
    simp only [map_mul] at h
    rw [hwdef, div_mul_eq_mul_div, eq_div_iff hu]
    linear_combination h
  let lκ : κ →+* FractionRing (A ⧸ 𝔭) := AdjoinRoot.lift (ι.comp kA) w (by
    unfold κpoly
    simp [hw])
  have hlκθ : lκ θ = w := by
    simp only [lκ, θ, AdjoinRoot.lift_root]
  have hlκk : ∀ c : k, lκ (algebraMap k κ c) = ι (kA c) := by
    intro c
    simp only [lκ, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, RingHom.comp_apply]
  let ψ : MvPolynomial (Fin (1 + 1)) κ →+* FractionRing (A ⧸ 𝔭) :=
    MvPolynomial.eval₂Hom lκ ![ι (zA 0), ι (zA 1)]
  have hψ : ψ.comp ringE = ι := by
    refine ringHom_ext_A (fun r => ?_) (fun i => ?_)
    · change ψ (evE (MvPolynomial.C r)) = _
      have h := kA_constantCoeff_sub_mem hπ' r
      rw [← hιinj, map_sub, sub_eq_zero] at h
      rw [h]
      simp only [ψ, evE, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        RingHom.algebraMap_toAlgebra]
      exact hlκk _
    · change ψ (evE (MvPolynomial.X i)) = ι (zA i)
      rw [evE, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · simp [ψ]
      · simp [ψ]
      · simp only [ψ, MvPolynomial.coe_eval₂Hom]
        simp [hlκθ, hw2]
      · simp only [ψ, MvPolynomial.coe_eval₂Hom]
        simp [hlκθ, h3]
  refine mem_range_map_of_ker φE irrelevant_le_map_φE ψ x fun a => ?_
  change (ψ.comp ringE) a = 0 ↔ _
  rw [hψ, hιinj]
  exact HomogeneousIdeal.mem_iff

/-! ### Two points of the projective line -/

/-- The variable `a` is not in the homogeneous core of the kernel of evaluation at `[1 : 0]`. -/
private theorem X_zero_notMem_core (F : Type) [Field F] :
    (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) F) ∉
      (RingHom.ker (MvPolynomial.eval ![(1 : F), 0])).homogeneousCore (lineGrading F) := by
  intro h
  have := Ideal.toIdeal_homogeneousCore_le _ _ (HomogeneousIdeal.mem_iff.mpr h)
  simp at this

/-- The point `[1 : 0]` of `ℙ¹_F`, the homogeneous prime `(b)`. -/
private def pt (F : Type) [Field F] : P1 F where
  asHomogeneousIdeal := (RingHom.ker (MvPolynomial.eval ![(1 : F), 0])).homogeneousCore _
  isPrime := (RingHom.ker_isPrime _).homogeneousCore
  not_irrelevant_le h :=
    X_zero_notMem_core F (h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X F 0))))

private theorem X_one_mem_pt (F : Type) [Field F] :
    (MvPolynomial.X 1 : MvPolynomial (Fin (1 + 1)) F) ∈ (pt F).asHomogeneousIdeal :=
  HomogeneousIdeal.mem_iff.mp (Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨1, (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X F 1)⟩
    (by simp))

private theorem zA_zero_mem_jC₁ (y : P1 k) : zA 0 ∈ (jC₁ y).asHomogeneousIdeal := by
  rw [jC₁, mem_map_asHomogeneousIdeal_iff, φC₁_zA]
  exact zero_mem _

private theorem θ_ne_zero : θ ≠ 0 := by
  intro h
  have := θ_sq
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap k κ).injective] at this
  exact RatFunc.X_ne_zero this

/-- **The special fibre is the union of the two lines.** A point of `X` lying over the closed
point of `Spec R` lies on the strict transform or on the exceptional curve. -/
theorem mem_range_jC₁_or_mem_range_jE (x : XR)
    (hx : X_to_R x = IsLocalRing.closedPoint R) :
    x ∈ Set.range jC₁ ∨ x ∈ Set.range jE := by
  by_cases h0 : zA 0 ∈ x.asHomogeneousIdeal
  · exact Or.inl (mem_range_jC₁_of_mem x (πA_mem x hx) h0)
  · exact Or.inr (mem_range_jE_of_notMem x (πA_mem x hx) h0)

/-- The exceptional curve is not contained in the strict transform. -/
theorem exists_mem_range_jE_notMem_range_jC₁ :
    ∃ x ∈ Set.range jE, x ∉ Set.range jC₁ := by
  refine ⟨jE (pt κ), ⟨_, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  have h := zA_zero_mem_jC₁ y
  rw [hy, jE, mem_map_asHomogeneousIdeal_iff, φE_zA] at h
  exact X_zero_notMem_core κ h

/-- The strict transform is not contained in the exceptional curve. -/
theorem exists_mem_range_jC₁_notMem_range_jE :
    ∃ x ∈ Set.range jC₁, x ∉ Set.range jE := by
  refine ⟨jC₁ (pt k), ⟨_, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  have h0 := zA_zero_mem_jC₁ (pt k)
  have h3 : zA 3 ∈ (jC₁ (pt k)).asHomogeneousIdeal := by
    rw [jC₁, mem_map_asHomogeneousIdeal_iff, φC₁_zA]
    exact X_one_mem_pt k
  rw [← hy, jE, mem_map_asHomogeneousIdeal_iff, φE_zA] at h0 h3
  change _ ∈ y.asHomogeneousIdeal.toIdeal at h0 h3
  have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin (1 + 1)) κ) ∈ y.asHomogeneousIdeal.toIdeal := by
    have e : (MvPolynomial.X 1 : MvPolynomial (Fin (1 + 1)) κ) =
        MvPolynomial.C θ⁻¹ * (MvPolynomial.C θ * MvPolynomial.X 1) := by
      rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ θ_ne_zero, MvPolynomial.C_1, one_mul]
    rw [e]
    exact Ideal.mul_mem_left _ _ (by simpa using h3)
  apply y.not_irrelevant_le
  rw [← toIdeal_le_toIdeal_iff]
  refine (Stacks.AlgebraicGeometry.ProjPolyChart.irrelevant_le_span_X κ 1).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa using h0
  · exact h1

end Stacks.Models.InseparableModel
