module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicSpecialFibre

/-!
# The special fibre of the split conic is the union of two lines

Let `R` be a local ring, `π` in its maximal ideal, and `X = V(T₁T₂ - πT₀²)`. Every point of `X`
over the closed point of `Spec R` lies on the line `C₁ = V(π, T₁)` or on the line `C₂ = V(π, T₂)`.

## Main results

* `Stacks.Models.GenusZero.mem_range_map_of_ker_le`: a homogeneous prime containing the kernel of
  a surjective graded homomorphism is in the image of the induced closed immersion of `Proj`s.
* `Stacks.Models.GenusZero.ker_firstLineHom_le` and `ker_secondLineHom_le`: the kernels of the
  two graded surjections onto `k[S₀, S₁]` are `(π, T₁)` and `(π, T₂)`.
* `Stacks.Models.GenusZero.mem_range_lines_of_mem_specialFibre`: the special fibre is covered
  by the two lines.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The image of a closed immersion of `Proj`s -/

section Range

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **A homogeneous prime containing the kernel of a surjective graded homomorphism is in the image
of the induced morphism of `Proj`s.** -/
theorem mem_range_map_of_ker_le (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hs : Function.Surjective f) (x : ProjectiveSpectrum 𝒜)
    (hx : RingHom.ker (f : A →+* B) ≤ x.asHomogeneousIdeal.toIdeal) :
    ∃ y : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comap f hf y = x := by
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let Q : HomogeneousIdeal ℬ := x.asHomogeneousIdeal.map f
  have hQprime : Q.toIdeal.IsPrime := Ideal.map_isPrime_of_surjective hs hx
  have hcomap : Q.toIdeal.comap (f : A →+* B) = x.asHomogeneousIdeal.toIdeal := by
    change (x.asHomogeneousIdeal.toIdeal.map (f : A →+* B)).comap (f : A →+* B) = _
    rwa [Ideal.comap_map_of_surjective (f : A →+* B) (hs : Function.Surjective (f : A →+* B)),
      sup_eq_left]
  have hirr : ¬ HomogeneousIdeal.irrelevant ℬ ≤ Q := by
    intro h
    apply x.not_irrelevant_le
    intro a ha
    change a ∈ x.asHomogeneousIdeal.toIdeal
    rw [← hcomap]
    apply h
    change f a ∈ HomogeneousIdeal.irrelevant ℬ
    change a ∈ HomogeneousIdeal.irrelevant 𝒜 at ha
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha ⊢
    rw [← GradedRingHom.map_directSumDecompose, ha, map_zero]
  exact ⟨⟨Q, hQprime, hirr⟩, ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective hcomap)⟩

end Range

/-! ### The kernels of the two graded surjections -/

section Kernels

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  (hπ : Irreducible π)
include hπ

local notation "κ" => IsLocalRing.ResidueField R

/-- A uniformizer lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_irreducible : π ∈ IsLocalRing.maximalIdeal R := by
  rw [hπ.maximalIdeal_eq]
  exact Ideal.subset_span rfl

/-- The constants of the residue field, in `R[T₀, T₁, T₂]/(T₁T₂ - πT₀², J)` for an ideal `J`
containing `π`. -/
def residueLift (J : Ideal (MvPolynomial (Fin 3) R ⧸ conicIdeal π)) (hJ : conicConst π ∈ J) :
    κ →+* (MvPolynomial (Fin 3) R ⧸ conicIdeal π) ⧸ J :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal R)
    ((Ideal.Quotient.mk J).comp ((Ideal.Quotient.mk (conicIdeal π)).comp C)) (fun r hr => by
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
      obtain ⟨s, rfl⟩ := hr
      rw [RingHom.comp_apply, RingHom.comp_apply, map_mul, map_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr hJ, zero_mul])

/-- `residueLift` sends the residue of `r` to the class of the constant `r`. -/
theorem residueLift_residue (J : Ideal (MvPolynomial (Fin 3) R ⧸ conicIdeal π))
    (hJ : conicConst π ∈ J) (r : R) :
    residueLift hπ J hJ (IsLocalRing.residue R r) =
      Ideal.Quotient.mk J (Ideal.Quotient.mk (conicIdeal π) (C r)) := rfl

/-- A graded map `lineHom` to `k[S₀, S₁]` has kernel inside an ideal `J` containing `π` as soon as
some evaluation of `k[S₀, S₁]` in `R[T]/(T₁T₂ - πT₀², J)` recovers the quotient map. -/
private theorem ker_lineHom_le_of_eval (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (J : Ideal (MvPolynomial (Fin 3) R ⧸ conicIdeal π))
    (hJc : conicConst π ∈ J) (w : Fin (1 + 1) → (MvPolynomial (Fin 3) R ⧸ conicIdeal π) ⧸ J)
    (hw : ∀ i, eval₂Hom (residueLift hπ J hJc) w (y i) = Ideal.Quotient.mk J (conicCoord π i)) :
    RingHom.ker (lineHom π y hy hlin : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+*
      MvPolynomial (Fin (1 + 1)) κ) ≤ J := by
  have hσ : (eval₂Hom (residueLift hπ J hJc) w).comp
      (lineHom π y hy hlin : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* _) =
        Ideal.Quotient.mk J := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_C, eval₂Hom_C]
      rfl
    · simpa using hw i
  intro a ha
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hσ, RingHom.comp_apply]
  exact (congrArg _ (RingHom.mem_ker.mp ha)).trans (map_zero _)

/-- **The kernel of `R[T]/(T₁T₂ - πT₀²) → k[S₀, S₁]`, `(T₀, T₁, T₂) ↦ (S₁, 0, S₀)`, is `(π, T₁)`.**
-/
theorem ker_firstLineHom_le :
    RingHom.ker (lineHom π _ (firstLine_rel (mem_maximalIdeal_of_irreducible hπ))
        firstLine_lin : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* MvPolynomial (Fin (1 + 1)) κ) ≤
      Ideal.span {conicConst π, conicCoord π 1} := by
  have hJc : conicConst π ∈ Ideal.span {conicConst π, conicCoord π 1} :=
    Ideal.subset_span (by simp)
  have hJ1 : conicCoord π 1 ∈ Ideal.span {conicConst π, conicCoord π 1} :=
    Ideal.subset_span (by simp)
  refine ker_lineHom_le_of_eval hπ _ _ _ _ hJc
    ![Ideal.Quotient.mk _ (conicCoord π 2), Ideal.Quotient.mk _ (conicCoord π 0)] (fun i => ?_)
  fin_cases i <;> simp [Ideal.Quotient.eq_zero_iff_mem.mpr hJ1]

/-- **The kernel of `R[T]/(T₁T₂ - πT₀²) → k[S₀, S₁]`, `(T₀, T₁, T₂) ↦ (S₀, S₁, 0)`, is `(π, T₂)`.**
-/
theorem ker_secondLineHom_le :
    RingHom.ker (lineHom π _ (secondLine_rel (mem_maximalIdeal_of_irreducible hπ))
        secondLine_lin : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* MvPolynomial (Fin (1 + 1)) κ) ≤
      Ideal.span {conicConst π, conicCoord π 2} := by
  have hJc : conicConst π ∈ Ideal.span {conicConst π, conicCoord π 2} :=
    Ideal.subset_span (by simp)
  have hJ2 : conicCoord π 2 ∈ Ideal.span {conicConst π, conicCoord π 2} :=
    Ideal.subset_span (by simp)
  refine ker_lineHom_le_of_eval hπ _ _ _ _ hJc
    ![Ideal.Quotient.mk _ (conicCoord π 0), Ideal.Quotient.mk _ (conicCoord π 1)] (fun i => ?_)
  fin_cases i <;> simp [Ideal.Quotient.eq_zero_iff_mem.mpr hJ2]

/-! ### The special fibre is covered by the two lines -/

omit hπ [IsDomain R] [IsDiscreteValuationRing R] in
/-- Every point of `X` has a homogeneous coordinate not in its homogeneous prime. -/
private theorem exists_conicCoord_not_mem (x : conicScheme π) :
    ∃ i : Fin 3, conicCoord π i ∉ x.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  apply x.not_irrelevant_le
  refine (irrelevant_le_span_mk_X (isHomogeneous_conicEquation π)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact h j

omit hπ [IsDomain R] [IsDiscreteValuationRing R] in
/-- On the chart `D₊(Tᵢ)`, the structure morphism of `X` is induced by the degree-zero part. -/
private theorem awayι_comp_conicToSpec (i : Fin 3) :
    Proj.awayι (conicGrading π) (conicCoord π i) (conicCoord_mem π i) one_pos ≫
      conicToSpec π = Spec.map (CommRingCat.ofHom ((fromZeroRingHom (conicGrading π) _).comp
        (PlaneCurveModel.toGradingZero (conicEquation π) (isHomogeneous_conicEquation π)))) := by
  unfold conicToSpec
  rw [PlaneCurveModel.toSpec_eq, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-- A point of `X` over the closed point of `Spec R` has `π` in its homogeneous prime. -/
theorem conicConst_mem_of_mem_specialFibre (x : conicScheme π)
    (hx : x ∈ Set.range (pullback.fst (conicToSpec π) (residueSpecMap R))) :
    conicConst π ∈ x.asHomogeneousIdeal := by
  rw [Scheme.Pullback.range_fst] at hx
  obtain ⟨q, hq⟩ := hx
  by_contra hc
  -- some coordinate does not vanish at `x`
  obtain ⟨i, hi⟩ := exists_conicCoord_not_mem x
  have hx' : x ∈ Proj.basicOpen (conicGrading π) (conicConst π * conicCoord π i) := by
    rw [Proj.mem_basicOpen]
    exact fun hmem => (x.isPrime.mem_or_mem hmem).elim hc hi
  have hxi : x ∈ (Proj.awayι (conicGrading π) (conicCoord π i) (conicCoord_mem π i)
      one_pos).opensRange := by
    rwa [Proj.opensRange_awayι, Proj.mem_basicOpen]
  obtain ⟨p, rfl⟩ := hxi
  have hc0 : conicConst π ∈ conicGrading π 0 :=
    Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
      ((mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C _ π))
  have hcmem : conicConst π * conicCoord π i ∈ conicGrading π 1 := by
    simpa using SetLike.mul_mem_graded hc0 (conicCoord_mem π i)
  have hp : p ∈ Proj.awayι (conicGrading π) (conicCoord π i) (conicCoord_mem π i) one_pos ⁻¹ᵁ
      Proj.basicOpen (conicGrading π) (conicConst π * conicCoord π i) := hx'
  rw [Proj.awayι_preimage_basicOpen (conicGrading π) (conicCoord_mem π i) one_pos hcmem one_pos]
    at hp
  -- the image of `p` in `Spec R` is the closed point
  rw [← Scheme.Hom.comp_apply, awayι_comp_conicToSpec] at hq
  have hmem : π ∈ (residueSpecMap R q).asIdeal := by
    change π ∈ Ideal.comap (algebraMap R (IsLocalRing.ResidueField R)) q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ _ q.isPrime, Ideal.mem_comap]
    exact (IsLocalRing.residue_eq_zero_iff π).2 (mem_maximalIdeal_of_irreducible hπ)
  rw [hq] at hmem
  change fromZeroRingHom (conicGrading π) _ (PlaneCurveModel.toGradingZero _ _ π) ∈ p.asIdeal
    at hmem
  apply hp
  convert hmem using 1
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ _ = (HomogeneousLocalization.mk ⟨0, _, 1, one_mem _⟩).val
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [PlaneCurveModel.coe_toGradingZero, conicConst]
  ring

/-- **The special fibre of `X` is covered by the two lines**: a point of `X` over the closed
point of `Spec R` lies on `C₁ = V(π, T₁)` or on `C₂ = V(π, T₂)`. -/
theorem mem_range_lines_of_mem_specialFibre (x : conicScheme π)
    (hx : x ∈ Set.range (pullback.fst (conicToSpec π) (residueSpecMap R))) :
    x ∈ Set.range (firstLine (mem_maximalIdeal_of_irreducible hπ)) ∪
      Set.range (secondLine (mem_maximalIdeal_of_irreducible hπ)) := by
  have hc := conicConst_mem_of_mem_specialFibre hπ x hx
  have h12 : conicCoord π 1 * conicCoord π 2 ∈ x.asHomogeneousIdeal := by
    rw [conic_relation]
    exact Ideal.mul_mem_right _ _ hc
  rcases x.isPrime.mem_or_mem h12 with h1 | h2
  · left
    exact mem_range_map_of_ker_le _ _
      (surjective_lineHom π _ (firstLine_rel (mem_maximalIdeal_of_irreducible hπ))
        firstLine_lin 2 0 rfl rfl) x
      ((ker_firstLineHom_le hπ).trans (by
        rw [Ideal.span_le]
        rintro z (rfl | rfl)
        exacts [hc, h1]))
  · right
    exact mem_range_map_of_ker_le _ _
      (surjective_lineHom π _ (secondLine_rel (mem_maximalIdeal_of_irreducible hπ))
        secondLine_lin 0 1 rfl rfl) x
      ((ker_secondLineHom_le hπ).trans (by
        rw [Ideal.span_le]
        rintro z (rfl | rfl)
        exacts [hc, h2]))

end Kernels

end Stacks.Models.GenusZero

end
