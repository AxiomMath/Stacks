module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Basic
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj

/-!
# A regular model with an inseparable component: the two components of the special fibre

The special fibre of the model `X` of `Stacks.Models.InseparableModel` is `V(π) ⊆ X`. It is the
union of two projective lines:

* the strict transform `C₁ = V(z₀₀, z₁₀) ≅ ℙ¹_k`, the image of the closed immersion `jC₁`
  attached to the graded map `A → k[a, b]`, `z₀₀, z₁₀ ↦ 0`, `z₀₁ ↦ a`, `z₁₁ ↦ b`;
* the exceptional curve `E ≅ ℙ¹_κ`, the image of the closed immersion `jE` attached to the
  graded map `A → κ[a, b]`, `z₀₀ ↦ a`, `z₀₁ ↦ b`, `z₁₀ ↦ θa`, `z₁₁ ↦ θb`.

## Main definitions

* `Stacks.Models.InseparableModel.P1` — `ℙ¹_F = Proj F[a, b]`.
* `Stacks.Models.InseparableModel.φC₁`, `φE` — the two graded maps.
* `Stacks.Models.InseparableModel.jC₁`, `jE` — the two closed immersions into `X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The total-degree grading of `F[a, b]`. -/
abbrev lineGrading (F : Type) [Field F] : ℕ → Submodule F (MvPolynomial (Fin (1 + 1)) F) :=
  Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading F 1

/-- The projective line `ℙ¹_F = Proj F[a, b]` over a field. -/
abbrev P1 (F : Type) [Field F] : Scheme := Proj (lineGrading F)

/-- The structure morphism `ℙ¹_F ⟶ Spec F`. -/
abbrev P1toSpec (F : Type) [Field F] : P1 F ⟶ Spec (.of F) :=
  Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff F 1

open MvPolynomial in
/-- `R[z] → k[a, b]`: reduce modulo `π`, `z₀₀, z₁₀ ↦ 0`, `z₀₁ ↦ a`, `z₁₁ ↦ b`. -/
def evC₁ : P →+* MvPolynomial (Fin (1 + 1)) k :=
  eval₂Hom ((C : k →+* MvPolynomial (Fin (1 + 1)) k).comp (algebraMap R k))
    ![0, MvPolynomial.X 0, 0, MvPolynomial.X 1]

open MvPolynomial in
/-- `R[z] → κ[a, b]`: reduce modulo `π`, `z₀₀ ↦ a`, `z₀₁ ↦ b`, `z₁₀ ↦ θa`, `z₁₁ ↦ θb`. -/
def evE : P →+* MvPolynomial (Fin (1 + 1)) κ :=
  eval₂Hom ((C : κ →+* MvPolynomial (Fin (1 + 1)) κ).comp ((algebraMap k κ).comp (algebraMap R k)))
    ![MvPolynomial.X 0, MvPolynomial.X 1, C θ * MvPolynomial.X 0, C θ * MvPolynomial.X 1]

/-- The image of `tR ∈ R` in the residue field `k` is `t`. -/
theorem algebraMap_Rk_tR : algebraMap R k tR = t := by
  simp [RingHom.algebraMap_toAlgebra, tR]

/-- The ideal `J` lies in the kernel of `evC₁`. -/
theorem J_le_ker_evC₁ : J.toIdeal ≤ RingHom.ker evC₁ := by
  show Ideal.span gens ≤ _
  rw [Ideal.span_le]
  rintro q (rfl | rfl | rfl) <;>
    simp [evC₁, q₀, q₁, q₂, algebraMap_Rk_π, algebraMap_Rk_tR]

/-- The ideal `J` lies in the kernel of `evE`. -/
theorem J_le_ker_evE : J.toIdeal ≤ RingHom.ker evE := by
  show Ideal.span gens ≤ _
  rw [Ideal.span_le]
  rintro q (rfl | rfl | rfl)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, evE, q₀]
    simp
    ring
  · simp only [SetLike.mem_coe, RingHom.mem_ker, evE, q₁]
    simp only [Nat.reduceAdd, AdjoinRoot.algebraMap_eq, Fin.isValue, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      RingHom.coe_comp, Function.comp_apply, algebraMap_Rk_π, map_zero, MvPolynomial.eval₂_X,
      Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one, algebraMap_Rk_tR, MvPolynomial.eval₂_pow,
      zero_add, Matrix.cons_val]
    rw [mul_pow, ← map_pow, θ_sq]
    simp
  · simp only [SetLike.mem_coe, RingHom.mem_ker, evE, q₂]
    simp only [Nat.reduceAdd, AdjoinRoot.algebraMap_eq, Fin.isValue, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      RingHom.coe_comp, Function.comp_apply, algebraMap_Rk_π, map_zero, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, Matrix.cons_val_one, Matrix.cons_val_zero, zero_mul, algebraMap_Rk_tR,
      zero_add, Matrix.cons_val]
    rw [mul_mul_mul_comm, ← map_mul, ← pow_two, θ_sq]
    simp
    ring

/-- The ring map `A → k[a, b]`. -/
def ringC₁ : A →+* MvPolynomial (Fin (1 + 1)) k :=
  Ideal.Quotient.lift J.toIdeal evC₁ fun _ ha => J_le_ker_evC₁ ha

/-- The ring map `A → κ[a, b]`. -/
def ringE : A →+* MvPolynomial (Fin (1 + 1)) κ :=
  Ideal.Quotient.lift J.toIdeal evE fun _ ha => J_le_ker_evE ha

/-- **The graded map `A → k[a, b]`** of the strict transform. -/
def φC₁ : grading →+*ᵍ lineGrading k where
  __ := ringC₁
  map_mem := by
    intro i x hx
    obtain ⟨p, hp, rfl⟩ :=
      (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff polyGrading J).1 hx
    change evC₁ p ∈ _
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    simpa [evC₁] using hp.eval₂
      ((MvPolynomial.C : k →+* MvPolynomial (Fin (1 + 1)) k).comp (algebraMap R k))
      ![0, MvPolynomial.X 0, 0, MvPolynomial.X 1]
      (fun r => MvPolynomial.isHomogeneous_C _ _) (n := 1) (by
        intro j
        fin_cases j
        · exact MvPolynomial.isHomogeneous_zero _ _ _
        · exact MvPolynomial.isHomogeneous_X _ _
        · exact MvPolynomial.isHomogeneous_zero _ _ _
        · exact MvPolynomial.isHomogeneous_X _ _)

/-- **The graded map `A → κ[a, b]`** of the exceptional curve. -/
def φE : grading →+*ᵍ lineGrading κ where
  __ := ringE
  map_mem := by
    intro i x hx
    obtain ⟨p, hp, rfl⟩ :=
      (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff polyGrading J).1 hx
    change evE p ∈ _
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    have hCX : ∀ j : Fin (1 + 1),
        (MvPolynomial.C θ * MvPolynomial.X j : MvPolynomial (Fin (1 + 1)) κ).IsHomogeneous 1 :=
      fun j => by
        simpa using (MvPolynomial.isHomogeneous_C _ θ).mul (MvPolynomial.isHomogeneous_X _ j)
    simpa [evE] using hp.eval₂
      ((MvPolynomial.C : κ →+* MvPolynomial (Fin (1 + 1)) κ).comp
        ((algebraMap k κ).comp (algebraMap R k)))
      ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C θ * MvPolynomial.X 0,
        MvPolynomial.C θ * MvPolynomial.X 1]
      (fun r => MvPolynomial.isHomogeneous_C _ _) (n := 1) (by
        intro j
        fin_cases j
        · exact MvPolynomial.isHomogeneous_X _ _
        · exact MvPolynomial.isHomogeneous_X _ _
        · exact hCX 0
        · exact hCX 1)

/-- `φC₁` sends the class of `p ∈ R[z]` to `evC₁ p`. -/
theorem φC₁_mk (p : P) : φC₁ (Ideal.Quotient.mk J.toIdeal p) = evC₁ p := rfl

/-- `φE` sends the class of `p ∈ R[z]` to `evE p`. -/
theorem φE_mk (p : P) : φE (Ideal.Quotient.mk J.toIdeal p) = evE p := rfl

/-- `φC₁` sends `z₀₀, z₁₀ ↦ 0`, `z₀₁ ↦ a`, `z₁₁ ↦ b`. -/
theorem φC₁_zA (i : Fin 4) :
    φC₁ (zA i) = ![0, MvPolynomial.X 0, 0, MvPolynomial.X 1] i := by
  simp [zA, φC₁_mk, evC₁]

/-- `φE` sends `z₀₀ ↦ a`, `z₀₁ ↦ b`, `z₁₀ ↦ θa`, `z₁₁ ↦ θb`. -/
theorem φE_zA (i : Fin 4) :
    φE (zA i) = ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C θ * MvPolynomial.X 0,
      MvPolynomial.C θ * MvPolynomial.X 1] i := by
  simp [zA, φE_mk, evE]

/-- `φC₁` sends the constant `c ∈ k ⊆ R` to the constant `c`. -/
theorem φC₁_C (c : k) :
    φC₁ (Ideal.Quotient.mk J.toIdeal (MvPolynomial.C (PowerSeries.C c))) = MvPolynomial.C c := by
  simp [φC₁_mk, evC₁, RingHom.algebraMap_toAlgebra]

/-- `φE` sends the constant `c ∈ k ⊆ R` to the constant `c ∈ κ`. -/
theorem φE_C (c : k) :
    φE (Ideal.Quotient.mk J.toIdeal (MvPolynomial.C (PowerSeries.C c))) =
      MvPolynomial.C (algebraMap k κ c) := by
  simp [φE_mk, evE, RingHom.algebraMap_toAlgebra]

/-- Each generator `zA i` lies in the irrelevant ideal of `A`. -/
theorem zA_mem_irrelevant (i : Fin 4) : zA i ∈ HomogeneousIdeal.irrelevant grading :=
  HomogeneousIdeal.mem_irrelevant_of_mem grading Nat.one_pos (zA_mem i)

/-- If `φ` sends `zA i, zA j` to the two variables, the irrelevant ideal of `F[a, b]` lies in
the image of the irrelevant ideal of `A`. -/
private theorem irrelevant_le_map_of_zA {F : Type} [Field F] (φ : grading →+*ᵍ lineGrading F)
    (i j : Fin 4) (hi : φ (zA i) = MvPolynomial.X 0) (hj : φ (zA j) = MvPolynomial.X 1) :
    (HomogeneousIdeal.irrelevant (lineGrading F)) ≤
      (HomogeneousIdeal.irrelevant grading).map φ := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine (Stacks.AlgebraicGeometry.ProjPolyChart.irrelevant_le_span_X F 1).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨l, rfl⟩
  fin_cases l
  · simpa [hi] using Ideal.mem_map_of_mem φ (zA_mem_irrelevant i)
  · simpa [hj] using Ideal.mem_map_of_mem φ (zA_mem_irrelevant j)

/-- The irrelevant ideal of `k[a, b]` is contained in the image under `φC₁` of the
irrelevant ideal of `A`. -/
theorem irrelevant_le_map_φC₁ :
    (HomogeneousIdeal.irrelevant (lineGrading k)) ≤
      (HomogeneousIdeal.irrelevant grading).map φC₁ :=
  irrelevant_le_map_of_zA φC₁ 1 3 (by simp [φC₁_zA]) (by simp [φC₁_zA])

/-- The irrelevant ideal of `κ[a, b]` is contained in the image under `φE` of the
irrelevant ideal of `A`. -/
theorem irrelevant_le_map_φE :
    (HomogeneousIdeal.irrelevant (lineGrading κ)) ≤
      (HomogeneousIdeal.irrelevant grading).map φE :=
  irrelevant_le_map_of_zA φE 0 1 (by simp [φE_zA]) (by simp [φE_zA])

/-- **The strict transform** `jC₁ : ℙ¹_k ⟶ X`. -/
def jC₁ : P1 k ⟶ XR := Proj.map φC₁ irrelevant_le_map_φC₁

/-- **The exceptional curve** `jE : ℙ¹_κ ⟶ X`. -/
def jE : P1 κ ⟶ XR := Proj.map φE irrelevant_le_map_φE

/-- Every element of `κ = k(θ)` is `a + bθ` with `a, b ∈ k`. -/
theorem exists_eq_add_mul_θ (c : κ) :
    ∃ a b : k, c = algebraMap k κ a + algebraMap k κ b * θ := by
  have hc : c ∈ Algebra.adjoin k ({θ} : Set κ) := by
    rw [θ, AdjoinRoot.adjoinRoot_eq_top]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap a => exact ⟨a, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by simp only [map_add]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    refine ⟨a * a' + b * b' * t, a * b' + b * a', ?_⟩
    have h := θ_sq
    simp only [map_add, map_mul]
    linear_combination (algebraMap k κ b * algebraMap k κ b') * h

/-- The graded map `φC₁ : A → k[a, b]` is surjective. -/
theorem φC₁_surjective : Function.Surjective φC₁ := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨_, φC₁_C c⟩
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨x, rfl⟩ := hp
    fin_cases i
    · exact ⟨x * zA 1, by simp [φC₁_zA]⟩
    · exact ⟨x * zA 3, by simp [φC₁_zA]⟩

/-- The range of `A → κ[a, b]`, as a subring. -/
abbrev rangeE : Subring (MvPolynomial (Fin (1 + 1)) κ) := (φE : A →+* _).range

/-- The variables `a, b` lie in the range of `φE`. -/
theorem X_mem_rangeE (i : Fin (1 + 1)) : MvPolynomial.X i ∈ rangeE := by
  fin_cases i
  · exact ⟨zA 0, by simp [φE_zA]⟩
  · exact ⟨zA 1, by simp [φE_zA]⟩

/-- For `c ∈ κ`, the linear monomials `c a` and `c b` lie in the range of `φE`. -/
theorem C_mul_X_mem_rangeE (c : κ) (i : Fin (1 + 1)) :
    MvPolynomial.C c * MvPolynomial.X i ∈ rangeE := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_θ c
  have hθ : MvPolynomial.C θ * MvPolynomial.X i ∈ rangeE := by
    fin_cases i
    · exact ⟨zA 2, by simp [φE_zA]⟩
    · exact ⟨zA 3, by simp [φE_zA]⟩
  have hk : ∀ a : k, MvPolynomial.C (algebraMap k κ a) ∈ rangeE := fun a => ⟨_, φE_C a⟩
  rw [map_add, map_mul, add_mul, mul_assoc]
  exact add_mem (mul_mem (hk a) (X_mem_rangeE i)) (mul_mem (hk b) hθ)

/-- Every monomial of positive degree with coefficient in `κ` lies in the range of `φE`. -/
theorem monomial_mem_rangeE {m : Fin (1 + 1) →₀ ℕ} (hm : m ≠ 0) (c : κ) :
    MvPolynomial.monomial m c ∈ rangeE := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (Finsupp.ext h)
  have hm' : m = Finsupp.single i 1 + (m - Finsupp.single i 1) := by
    ext j
    by_cases hj : i = j
    · subst hj; simp; omega
    · simp [hj]
  have hprod : ∀ n : Fin (1 + 1) →₀ ℕ, MvPolynomial.monomial n (1 : κ) ∈ rangeE := by
    intro n
    rw [MvPolynomial.monomial_eq, map_one, one_mul]
    exact Subring.prod_mem _ fun j _ => pow_mem (X_mem_rangeE j) _
  rw [hm', ← mul_one c, ← MvPolynomial.monomial_mul, ← MvPolynomial.C_mul_X_eq_monomial]
  exact mul_mem (C_mul_X_mem_rangeE c i) (hprod _)

/-- Every homogeneous polynomial of degree `d ≥ 1` in `κ[a, b]` lies in the range of `φE`. -/
theorem mem_rangeE_of_isHomogeneous {b : MvPolynomial (Fin (1 + 1)) κ} {d : ℕ}
    (hb : b.IsHomogeneous d) (hd : 1 ≤ d) : b ∈ rangeE := by
  rw [MvPolynomial.as_sum b]
  refine Subring.sum_mem _ fun m hm => monomial_mem_rangeE ?_ _
  rintro rfl
  have := hb (MvPolynomial.mem_support_iff.1 hm)
  simp at this
  omega

/-- The graded map `φE : A → κ[a, b]` is surjective in every degree `d ≥ 1`. -/
theorem surjectiveInLargeDegrees_φE : Stacks.Proj.SurjectiveInLargeDegrees φE := by
  refine ⟨1, fun d hd b hb => ?_⟩
  obtain ⟨x, hx⟩ := mem_rangeE_of_isHomogeneous
    ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hb) hd
  refine ⟨DirectSum.decompose grading x d, Subtype.prop _, ?_⟩
  rw [φE.map_directSumDecompose]
  show (DirectSum.decompose (lineGrading κ) ((φE : A →+* _) x) d :
    MvPolynomial (Fin (1 + 1)) κ) = b
  rw [hx, DirectSum.decompose_of_mem_same _ hb]

/-- The strict transform `jC₁ : ℙ¹_k ⟶ X` is a closed immersion. -/
instance isClosedImmersion_jC₁ : IsClosedImmersion jC₁ :=
  Proj.isClosedImmersion_map_of_surjective _ φC₁_surjective

/-- The exceptional curve `jE : ℙ¹_κ ⟶ X` is a closed immersion. -/
instance isClosedImmersion_jE : IsClosedImmersion jE :=
  Proj.isClosedImmersion_map_of_surjectiveInLargeDegrees _ surjectiveInLargeDegrees_φE

/-- The map `ℙ¹_F ⟶ X` of a graded map `φ` compatible with `ψ : R → F` lies over
`ℙ¹_F ⟶ Spec F ⟶ Spec R`. -/
private theorem proj_map_comp_X_to_R {F : Type} [Field F] (φ : grading →+*ᵍ lineGrading F)
    (h : (HomogeneousIdeal.irrelevant (lineGrading F)) ≤
      (HomogeneousIdeal.irrelevant grading).map φ) (ψ : R →+* F)
    (hψ : ∀ r : R, φ (algebraMap R A r) = MvPolynomial.C (ψ r)) :
    Proj.map φ h ≫ X_to_R = P1toSpec F ≫ Spec.map (CommRingCat.ofHom ψ) := by
  rw [X_to_R, Proj.map_toSpecZero_assoc, P1toSpec,
    Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 2
  ext r : 3
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
    GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
  rw [hψ, DirectSum.decompose_of_mem_same _ (SetLike.algebraMap_mem_graded _ _)]
  rfl

/-- The strict transform lies over the closed point: `ℙ¹_k ⟶ X ⟶ Spec R` is
`ℙ¹_k ⟶ Spec k ⟶ Spec R`. -/
theorem jC₁_comp_X_to_R :
    jC₁ ≫ X_to_R = P1toSpec k ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) :=
  proj_map_comp_X_to_R _ _ _ fun r => by
    simp [IsScalarTower.algebraMap_apply R P A, φC₁_mk, evC₁]

/-- The exceptional curve lies over the closed point: `ℙ¹_κ ⟶ X ⟶ Spec R` is
`ℙ¹_κ ⟶ Spec κ ⟶ Spec k ⟶ Spec R`. -/
theorem jE_comp_X_to_R :
    jE ≫ X_to_R = P1toSpec κ ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
  rw [← Spec.map_comp]
  exact proj_map_comp_X_to_R _ _ ((algebraMap k κ).comp (algebraMap R k)) fun r => by
    simp [IsScalarTower.algebraMap_apply R P A, φE_mk, evE]

end Stacks.Models.InseparableModel
