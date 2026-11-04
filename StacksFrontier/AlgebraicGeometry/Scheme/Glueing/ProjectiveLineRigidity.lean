module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineAffineOpen
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineChartMorphisms
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType

/-!
# Automorphisms of the projective line fixing three points

Let `k` be a field. An automorphism of `ℙ¹_k` over `k` which fixes three distinct `k`-points
`x = a`, `x = b`, `x = c` of the first chart is the identity.

## Main definitions

* `AlgebraicGeometry.projectiveLineXChartPoint`: the `R`-point `x = a` of `ℙ¹_R`, in the first
  chart.

## Main results

* `AlgebraicGeometry.projectiveLineXChartPoint_comp_projectiveLineScaling` and
  `AlgebraicGeometry.projectiveLineXChartPoint_comp_projectiveLineTranslation`: the scaling
  `x ↦ u x` moves the point `x = a` to `x = u a`, and the translation `x ↦ x + c` moves it to
  `x = a + c`.
* `AlgebraicGeometry.projectiveLineXChartPoint_eq_comp_projectiveLineSChart`: the point `x = a`,
  for `a ≠ 1`, is the point `s = 1/(a - 1)` of the third chart.
* `AlgebraicGeometry.eq_id_of_fix_one`: an automorphism over `k` fixing `1` and two further
  points is the identity.
* `AlgebraicGeometry.eq_id_of_fix_three`: **an automorphism of `ℙ¹_k` over `k` fixing three
  distinct points of the first chart is the identity.**

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

section Points

variable {R : Type u} [CommRing R]

/-- The `R`-point `x = a` of the projective line `ℙ¹_R`, in its first chart. -/
def projectiveLineXChartPoint (a : R) : Spec (.of R) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ projectiveLineXChart R

/-- The point `x = a` is a section of the structure morphism. -/
@[reassoc (attr := simp)]
theorem projectiveLineXChartPoint_comp_structureMorphism (a : R) :
    projectiveLineXChartPoint a ≫ (projectiveLine R ↘ Spec (.of R)) = 𝟙 _ := by
  rw [projectiveLineXChartPoint, Category.assoc, projectiveLineXChart_comp_structureMorphism,
    projectiveLineAffineStructureMorphism, Spec_map_ofHom_comp_Spec_map_ofHom]
  have : (Polynomial.evalRingHom a).comp (C : R →+* R[X]) = RingHom.id R := by ext; simp
  rw [this, CommRingCat.ofHom_id, Spec.map_id]

/-- A chartwise endomorphism moves the point `x = a` to `x = p(a)`. -/
theorem projectiveLineXChartPoint_comp_projectiveLineHom (a : R) (p q : R[X])
    (h : Polynomial.toLaurent p * projectiveLineOverlapInverseCoordinate R q = 1) :
    projectiveLineXChartPoint a ≫ projectiveLineHom (RingHom.id R) p q h =
      projectiveLineXChartPoint (p.eval a) := by
  rw [projectiveLineXChartPoint, Category.assoc, projectiveLineXChart_comp_projectiveLineHom,
    ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom, projectiveLineXChartPoint]
  congr 3
  refine Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- The scaling `x ↦ u x` moves the point `x = a` to `x = u a`. -/
theorem projectiveLineXChartPoint_comp_projectiveLineScaling (a : R) (u : Rˣ) :
    projectiveLineXChartPoint a ≫ projectiveLineScaling u =
      projectiveLineXChartPoint ((u : R) * a) := by
  rw [projectiveLineScaling, projectiveLineXChartPoint_comp_projectiveLineHom]
  simp

/-- The translation `x ↦ x + c` moves the point `x = a` to `x = a + c`. -/
theorem projectiveLineXChartPoint_comp_projectiveLineTranslation (a : R) {c : R} (hc : c * c = 0) :
    projectiveLineXChartPoint a ≫ projectiveLineTranslation c hc =
      projectiveLineXChartPoint (a + c) := by
  rw [projectiveLineTranslation, projectiveLineXChartPoint_comp_projectiveLineHom]
  simp

end Points

section Field

variable {k : Type u} [Field k]

/-- The ring map `k[x][1/(x-1)] ⟶ k` evaluating at a point `x = a` with `a ≠ 1`. -/
def affineLineAwayOneEval (a : k) (ha : a ≠ 1) : affineLineAwayOne k →+* k :=
  IsLocalization.Away.lift (Polynomial.X - 1 : k[X]) (g := Polynomial.evalRingHom a)
    (by simpa [sub_eq_zero] using ha)

/-- Evaluation at `x = a` on `k[x][1/(x-1)]` restricts to evaluation at `a` on `k[x]`. -/
theorem affineLineAwayOneEval_comp_algebraMap (a : k) (ha : a ≠ 1) :
    (affineLineAwayOneEval a ha).comp (algebraMap k[X] (affineLineAwayOne k)) =
      Polynomial.evalRingHom a :=
  IsLocalization.Away.lift_comp _ _

/-- Evaluation at `x = a` sends the coordinate `s = 1/(x - 1)` to `1/(a - 1)`: composed with the
substitution `affineLineSOnXChart k` it is evaluation at `(a - 1)⁻¹` on `k[s]`. -/
theorem affineLineAwayOneEval_comp_affineLineSOnXChart (a : k) (ha : a ≠ 1) :
    (affineLineAwayOneEval a ha).comp (affineLineSOnXChart k) =
      Polynomial.evalRingHom (a - 1)⁻¹ := by
  have hL : ∀ g : k[X], affineLineAwayOneEval a ha (algebraMap k[X] (affineLineAwayOne k) g) =
      g.eval a := fun g ↦
    congrArg (fun φ : k[X] →+* k ↦ φ g) (affineLineAwayOneEval_comp_algebraMap a ha)
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · rw [RingHom.comp_apply, coe_evalRingHom, eval_C,
      show affineLineSOnXChart k (C r) = algebraMap k[X] (affineLineAwayOne k) (C r) by
        simp [affineLineSOnXChart, IsScalarTower.algebraMap_apply k k[X] (affineLineAwayOne k)],
      hL, eval_C]
  · rw [RingHom.comp_apply, affineLineSOnXChart_X, coe_evalRingHom, eval_X]
    have hu : (a - 1) * affineLineAwayOneEval a ha
        (IsLocalization.Away.invSelf (Polynomial.X - 1 : k[X])) = 1 := by
      have := congrArg (affineLineAwayOneEval a ha)
        (IsLocalization.Away.mul_invSelf (S := affineLineAwayOne k) (Polynomial.X - 1 : k[X]))
      rwa [map_mul, map_one, hL, eval_sub, eval_X, eval_one] at this
    exact (inv_eq_of_mul_eq_one_right hu).symm

/-- **The point `x = a` of the first chart, for `a ≠ 1`, is the point `s = 1/(a - 1)` of the
third chart.** -/
theorem projectiveLineXChartPoint_eq_comp_projectiveLineSChart (a : k) (ha : a ≠ 1) :
    projectiveLineXChartPoint a =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (a - 1)⁻¹)) ≫
        projectiveLineSChart k := by
  rw [← affineLineAwayOneEval_comp_affineLineSOnXChart a ha,
    ← Spec_map_ofHom_comp_Spec_map_ofHom, Category.assoc,
    projectiveLineSXPiece_comp_projectiveLineSChart, ← Category.assoc,
    Spec_map_ofHom_comp_Spec_map_ofHom, affineLineAwayOneEval_comp_algebraMap]
  rfl

/-- The coordinate `s = 1/(x - 1)` is an injective substitution. -/
theorem affineLineSOnXChart_injective : Function.Injective (affineLineSOnXChart k) := by
  have h := awayEquivOfSubst_comp Polynomial.X (Polynomial.X - 1) _ _
    (isUnit_affineLineSOnXChart_X k) (isUnit_xOnSChart_X_sub_one k)
    (affineLineSOnXChart_hfg k) (affineLineSOnXChart_hgf k)
  rw [← h]
  exact (affineLineAwayOneEquivX k).injective.comp
    (IsLocalization.injective (Localization.Away (Polynomial.X : k[X]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero))

/-- The third chart lies over `Spec k` by the structure morphism of the affine line. -/
@[reassoc (attr := simp)]
theorem projectiveLineSChart_comp_structureMorphism :
    projectiveLineSChart k ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (C : k →+* k[X])) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = projectiveLineSChart k ≫ (projectiveLine k ↘ Spec (.of k)) :=
    ⟨_, Spec.map_preimage _⟩
  rw [← hφ]
  congr 1
  have e : projectiveLineSXPiece k ≫ Spec.map φ =
      projectiveLineSXPiece k ≫ Spec.map (CommRingCat.ofHom (C : k →+* k[X])) := by
    rw [hφ, ← Category.assoc, projectiveLineSXPiece_comp_projectiveLineSChart, Category.assoc,
      projectiveLineXChart_comp_structureMorphism, projectiveLineAffineStructureMorphism,
      Spec_map_ofHom_comp_Spec_map_ofHom, projectiveLineSXPiece,
      Spec_map_ofHom_comp_Spec_map_ofHom]
    congr 2
    ext r
    simp [affineLineSOnXChart, IsScalarTower.algebraMap_apply k k[X] (affineLineAwayOne k)]
  have e2 : φ ≫ CommRingCat.ofHom (affineLineSOnXChart k) =
      CommRingCat.ofHom C ≫ CommRingCat.ofHom (affineLineSOnXChart k) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact e)
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ affineLineSOnXChart_injective ?_)
  simpa using congrArg (fun g ↦ g.hom r) e2

/-- The point `x = 1` is the point `1` of the projective line. -/
theorem projectiveLineXChartPoint_one_apply (z : Spec (.of k)) :
    (projectiveLineXChartPoint (1 : k)).base z = projectiveLineOne k := by
  change (projectiveLineXChart k).base
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : k)))).base z) = _
  rw [projectiveLineOne]
  congr 1
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (Polynomial.evalRingHom (1 : k)) z.asIdeal = Ideal.span {X - 1}
  have := z.isPrime
  rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom,
    map_one]

/-- A polynomial of degree one fixing two distinct points is the coordinate. -/
theorem eq_X_of_natDegree_eq_one_of_eval_eq {f : k[X]} (hf : f.natDegree = 1) {s₁ s₂ : k}
    (hs : s₁ ≠ s₂) (h₁ : f.eval s₁ = s₁) (h₂ : f.eval s₂ = s₂) : f = X := by
  have e := Polynomial.eq_X_add_C_of_natDegree_le_one hf.le
  rw [e] at h₁ h₂ ⊢
  simp only [eval_add, eval_mul, eval_C, eval_X] at h₁ h₂
  have hα : f.coeff 1 = 1 := by
    have : (f.coeff 1 - 1) * (s₁ - s₂) = 0 := by linear_combination h₁ - h₂
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd (sub_eq_zero.1 h) hs
  have hβ : f.coeff 0 = 0 := by
    rw [hα] at h₁
    linear_combination h₁
  rw [hα, hβ, C_1, C_0, one_mul, add_zero]

/-- A ring endomorphism of `k[X]` fixing the constants is a substitution. -/
theorem eq_eval₂RingHom_of_comp_C_eq {ψ : k[X] →+* k[X]} (hψ : ψ.comp C = C) :
    ψ = eval₂RingHom C (ψ X) :=
  Polynomial.ringHom_ext (fun r ↦ by simpa using congrArg (· r) hψ) (by simp)

/-- **An automorphism of `ℙ¹_k` over `k` fixing the point `1` and two further distinct points of
the first chart is the identity.** -/
theorem eq_id_of_fix_one {σ : projectiveLine k ⟶ projectiveLine k} [IsIso σ]
    (hσ : σ ≫ (projectiveLine k ↘ Spec (.of k)) = projectiveLine k ↘ Spec (.of k))
    {a b : k} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (h1 : projectiveLineXChartPoint 1 ≫ σ = projectiveLineXChartPoint 1)
    (h₁ : projectiveLineXChartPoint a ≫ σ = projectiveLineXChartPoint a)
    (h₂ : projectiveLineXChartPoint b ≫ σ = projectiveLineXChartPoint b) : σ = 𝟙 _ := by
  let z : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hleft : ∀ g h : projectiveLine k ⟶ projectiveLine k, g ≫ h = 𝟙 _ →
      Function.LeftInverse h.base g.base := fun g h e x ↦ by
    change (g ≫ h).base x = x
    rw [e]
    rfl
  have hone : σ.base (projectiveLineOne k) = projectiveLineOne k := by
    have := congrArg (fun φ : Spec (.of k) ⟶ projectiveLine k ↦ φ.base z) h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rwa [projectiveLineXChartPoint_one_apply] at this
  have hlift : ∀ g : projectiveLine k ⟶ projectiveLine k, Function.Injective g.base →
      g.base (projectiveLineOne k) = projectiveLineOne k →
      ∃ ψ, Spec.map ψ ≫ projectiveLineSChart k = projectiveLineSChart k ≫ g := by
    intro g hg hg1
    refine ⟨Spec.preimage (IsOpenImmersion.lift (projectiveLineSChart k)
      (projectiveLineSChart k ≫ g) ?_), by
        rw [Spec.map_preimage]
        exact IsOpenImmersion.lift_fac ..⟩
    rintro _ ⟨w, rfl⟩
    rw [range_projectiveLineSChart]
    intro hw
    have hmem : (projectiveLineSChart k).base w ∈ Set.range (projectiveLineSChart k).base :=
      ⟨w, rfl⟩
    rw [range_projectiveLineSChart] at hmem
    exact hmem (hg (hw.trans hg1.symm))
  obtain ⟨ψ, hσS⟩ := hlift σ (hleft σ (inv σ) (IsIso.hom_inv_id σ)).injective hone
  obtain ⟨ψ', hτS⟩ := hlift (inv σ) (hleft (inv σ) σ (IsIso.inv_hom_id σ)).injective
    (by simpa [hone] using hleft σ (inv σ) (IsIso.hom_inv_id σ) (projectiveLineOne k))
  have hστ : Spec.map ψ ≫ Spec.map ψ' = 𝟙 _ := by
    rw [← cancel_mono (projectiveLineSChart k), Category.assoc, hτS, ← Category.assoc, hσS,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  have hlin : ψ.hom.comp C = C := by
    have e : Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (C : k →+* k[X])) =
        Spec.map (CommRingCat.ofHom (C : k →+* k[X])) := by
      rw [← projectiveLineSChart_comp_structureMorphism, ← Category.assoc, hσS,
        Category.assoc, hσ]
    rw [← Spec.map_comp] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hdeg : (ψ.hom X).natDegree = 1 := by
    have e : ψ' ≫ ψ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hστ, Spec.map_id]
    have e' : (ψ'.hom X).comp (ψ.hom X) = X := by
      have := congrArg (fun φ : CommRingCat.of k[X] ⟶ CommRingCat.of k[X] ↦ φ.hom X) e
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
        RingHom.id_apply] at this
      rw [eq_eval₂RingHom_of_comp_C_eq hlin] at this
      simpa [Polynomial.comp] using this
    have := congrArg natDegree e'
    rw [natDegree_comp, natDegree_X] at this
    exact Nat.eq_one_of_mul_eq_one_left this
  have hfix : ∀ c : k, c ≠ 1 → projectiveLineXChartPoint c ≫ σ = projectiveLineXChartPoint c →
      (ψ.hom X).eval (c - 1)⁻¹ = (c - 1)⁻¹ := by
    intro c hc h
    rw [projectiveLineXChartPoint_eq_comp_projectiveLineSChart c hc, Category.assoc, ← hσS,
      ← Category.assoc, cancel_mono, ← Spec.map_comp] at h
    have := congrArg (fun φ : CommRingCat.of k[X] ⟶ CommRingCat.of k ↦ φ.hom X)
      (Spec.map_injective h)
    simpa using this
  have hs : (a - 1)⁻¹ ≠ (b - 1)⁻¹ := by
    rw [Ne, inv_inj, sub_left_inj]
    exact hab
  have hX := eq_X_of_natDegree_eq_one_of_eval_eq hdeg hs (hfix a ha h₁) (hfix b hb h₂)
  have hψid : ψ = 𝟙 _ := by
    apply CommRingCat.hom_ext
    rw [eq_eval₂RingHom_of_comp_C_eq hlin, hX]
    exact Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)
  have hS : projectiveLineSChart k ≫ σ = projectiveLineSChart k ≫ 𝟙 _ := by
    rw [← hσS, hψid, Spec.map_id, Category.id_comp, Category.comp_id]
  have : IsDominant (projectiveLineSChart k) :=
    ⟨(projectiveLineSChart k).isOpenEmbedding.isOpen_range.dense
      ⟨_, ⟨⟨⊥, Ideal.isPrime_bot⟩, rfl⟩⟩⟩
  exact ext_of_isDominant_of_isSeparated (projectiveLine k ↘ Spec (.of k))
    (by rw [hσ, Category.id_comp]) (projectiveLineSChart k) hS

/-- **An automorphism of `ℙ¹_k` over `k` fixing three distinct points of the first chart is the
identity.** -/
theorem eq_id_of_fix_three {σ : projectiveLine k ⟶ projectiveLine k} [IsIso σ]
    (hσ : σ ≫ (projectiveLine k ↘ Spec (.of k)) = projectiveLine k ↘ Spec (.of k))
    {a b c : k} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : projectiveLineXChartPoint a ≫ σ = projectiveLineXChartPoint a)
    (hb : projectiveLineXChartPoint b ≫ σ = projectiveLineXChartPoint b)
    (hc : projectiveLineXChartPoint c ≫ σ = projectiveLineXChartPoint c) : σ = 𝟙 _ := by
  wlog hc0 : c ≠ 0 generalizing a b c
  · push Not at hc0
    exact this hbc.symm hac.symm hab.symm hc hb ha (hc0 ▸ hac)
  let u : kˣ := Units.mk0 c hc0
  let μ := projectiveLineScalingIso u
  have hpt : ∀ x : k, projectiveLineXChartPoint x ≫ σ = projectiveLineXChartPoint x →
      projectiveLineXChartPoint ((↑u⁻¹ : k) * x) ≫ (μ.hom ≫ σ ≫ μ.inv) =
        projectiveLineXChartPoint ((↑u⁻¹ : k) * x) := by
    intro x hx
    change projectiveLineXChartPoint _ ≫ projectiveLineScaling u ≫ σ ≫ projectiveLineScaling u⁻¹ = _
    rw [← Category.assoc, projectiveLineXChartPoint_comp_projectiveLineScaling,
      Units.mul_inv_cancel_left, ← Category.assoc, hx,
      projectiveLineXChartPoint_comp_projectiveLineScaling]
  have hu1 : (↑u⁻¹ : k) * c = 1 := Units.inv_mul u
  have hne1 : ∀ x : k, x ≠ c → (↑u⁻¹ : k) * x ≠ 1 := fun x hx h ↦
    hx ((Units.inv_mul_eq_one.1 h).symm)
  have key := eq_id_of_fix_one (σ := μ.hom ≫ σ ≫ μ.inv) (a := (↑u⁻¹ : k) * a)
    (b := (↑u⁻¹ : k) * b)
    (by simp [μ, projectiveLineScalingIso, hσ]) (hne1 a hac) (hne1 b hbc)
    ((mul_right_injective₀ (Units.ne_zero u⁻¹)).ne hab) (hu1 ▸ hpt c hc) (hpt a ha) (hpt b hb)
  calc σ = μ.inv ≫ (μ.hom ≫ σ ≫ μ.inv) ≫ μ.hom := by simp
    _ = 𝟙 _ := by rw [key, Category.id_comp, Iso.inv_hom_id]

end Field

end AlgebraicGeometry
