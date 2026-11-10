module

public import StacksFrontier.AlgebraicGeometry.Curves.WeilBound.WeilBound
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.ConstantField

/-!
# The Weil bound for a Frobenius twisted by an automorphism of finite order

Let `X` be a smooth, proper, geometrically irreducible curve of genus `g` over a finite field `k`
with `q = p ^ e` elements, `Ω` an algebraic closure of `k`, `X_Ω = X ×_k Spec Ω`, and
`Ψ = 𝟙_X × Spec(a ↦ a ^ q)` the Frobenius twist of `X_Ω`
(`AlgebraicGeometry.WeilBound.frobeniusTwist`). For an automorphism `σ` of `X` over `k` of finite
order, let `σ_Ω = σ × 𝟙` be its base change and `Φ = Ψ ∘ σ_Ω` the *twisted Frobenius*. Then for
every `m ≥ 1` the closed points of `X_Ω` fixed by `Φ ^ m` number `N m` with

`|N m - q ^ m - 1| ≤ 2 g √q ^ m`.

## Main definitions

* `Stacks.Drinfeld.baseChangeEndo`: the base change `φ × 𝟙` to `X_Ω` of an endomorphism `φ` of
  `X` over `k`.
* `Stacks.Drinfeld.baseChangeAut`: the base change of an automorphism.
* `Stacks.Drinfeld.twistedFrobenius`: `Φ = Ψ ∘ σ_Ω`.

## Main results

* `Stacks.Drinfeld.twistedFrobenius_hom_comp_snd`: `Φ` is `q`-semilinear.
* `Stacks.Drinfeld.abs_natCard_fixed_twistedFrobenius_sub_le`: the twisted Weil bound.
* `Stacks.Drinfeld.closedPointsEquiv_baseChangeAut`: on `X(Ω)`, `σ_Ω` is postcomposition with
  `σ`.
* `Stacks.Drinfeld.exists_fieldValuedPoint_twisted`: for `m ≡ 1` modulo the order of `σ` and
  `q ^ m > 2 g √q ^ m`, some `z ∈ X(Ω)` has `z ∘ σ = Frob_{q^m} ∘ z`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.WeilBound

universe u

namespace Stacks.Drinfeld

variable {k : Type u} [Field k] [Fintype k] (Ω : Type u) [Field Ω] [Algebra k Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The base change `φ × 𝟙 : X_Ω ⟶ X_Ω` of an endomorphism `φ` of `X` over `k`. -/
def baseChangeEndo (φ : X ⟶ X) (hφ : φ ≫ f = f) :
    geometricBaseChange Ω f ⟶ geometricBaseChange Ω f :=
  pullback.map f (baseMap k Ω) f (baseMap k Ω) φ (𝟙 _) (𝟙 _) (by rw [hφ, Category.comp_id])
    (by simp)

omit [Fintype k] in
/-- The base change `φ × 𝟙` followed by the projection to `X` is the projection followed by
`φ`. -/
@[reassoc (attr := simp)]
theorem baseChangeEndo_fst (φ : X ⟶ X) (hφ : φ ≫ f = f) :
    baseChangeEndo Ω f φ hφ ≫ pullback.fst f (baseMap k Ω) = pullback.fst f (baseMap k Ω) ≫ φ :=
  pullback.lift_fst _ _ _

omit [Fintype k] in
/-- The base change `φ × 𝟙` commutes with the projection to `Spec Ω`. -/
@[reassoc (attr := simp)]
theorem baseChangeEndo_snd (φ : X ⟶ X) (hφ : φ ≫ f = f) :
    baseChangeEndo Ω f φ hφ ≫ pullback.snd f (baseMap k Ω) = pullback.snd f (baseMap k Ω) := by
  simp [baseChangeEndo]

omit [Fintype k] in
/-- The base change of the identity of `X` is the identity of `X_Ω`. -/
theorem baseChangeEndo_id : baseChangeEndo Ω f (𝟙 X) (Category.id_comp f) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

omit [Fintype k] in
/-- Base change takes the composite `φ ≫ ψ` to the composite of the base changes. -/
theorem baseChangeEndo_comp (φ ψ : X ⟶ X) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) :
    baseChangeEndo Ω f (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) =
      baseChangeEndo Ω f φ hφ ≫ baseChangeEndo Ω f ψ hψ := by
  apply pullback.hom_ext <;> simp

/-- The `n`-fold composite `φ ≫ ⋯ ≫ φ` of an endomorphism. -/
def compPow {Y : Scheme.{u}} (φ : Y ⟶ Y) : ℕ → (Y ⟶ Y)
  | 0 => 𝟙 Y
  | n + 1 => φ ≫ compPow φ n

omit [Fintype k] in
/-- A power of an endomorphism over `k` is over `k`. -/
theorem compPow_comp_eq (φ : X ⟶ X) (hφ : φ ≫ f = f) (n : ℕ) : compPow φ n ≫ f = f := by
  induction n with
  | zero => exact Category.id_comp f
  | succ n ih => rw [compPow, Category.assoc, ih, hφ]

/-- The iterates of the underlying map of an endomorphism are the underlying maps of its
composites. -/
theorem base_iterate_eq_compPow {Y : Scheme.{u}} (φ : Y ⟶ Y) (n : ℕ) :
    (⇑φ.base)^[n] = ⇑(compPow φ n).base := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ, ih, compPow, Scheme.Hom.comp_base]
    rfl

omit [Fintype k] in
/-- The composites of a base change are the base changes of the composites. -/
theorem compPow_baseChangeEndo (φ : X ⟶ X) (hφ : φ ≫ f = f) (n : ℕ) :
    compPow (baseChangeEndo Ω f φ hφ) n =
      baseChangeEndo Ω f (compPow φ n) (compPow_comp_eq f φ hφ n) := by
  induction n with
  | zero => exact (baseChangeEndo_id Ω f).symm
  | succ n ih =>
    rw [compPow, ih, ← baseChangeEndo_comp]
    rfl

/-- The base change `σ_Ω = σ × 𝟙` of an automorphism `σ` of `X` over `k`. -/
def baseChangeAut (σ : X ≅ X) (hσ : σ.hom ≫ f = f) :
    geometricBaseChange Ω f ≅ geometricBaseChange Ω f where
  hom := baseChangeEndo Ω f σ.hom hσ
  inv := baseChangeEndo Ω f σ.inv (by rw [Iso.inv_comp_eq, hσ])
  hom_inv_id := by
    rw [← baseChangeEndo_comp]
    simp only [Iso.hom_inv_id, baseChangeEndo_id]
  inv_hom_id := by
    rw [← baseChangeEndo_comp]
    simp only [Iso.inv_hom_id, baseChangeEndo_id]

variable [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (e : ℕ)
  (hq : Fintype.card k = p ^ e)

/-- **The twisted Frobenius** `Φ = Ψ ∘ σ_Ω` of `X_Ω`, for an automorphism `σ` of `X` over `k`. -/
def twistedFrobenius (σ : X ≅ X) (hσ : σ.hom ≫ f = f) :
    geometricBaseChange Ω f ≅ geometricBaseChange Ω f :=
  baseChangeAut Ω f σ hσ ≪≫ frobeniusTwist Ω p e hq f

/-- **The twisted Frobenius is `q`-semilinear.** -/
theorem twistedFrobenius_hom_comp_snd (σ : X ≅ X) (hσ : σ.hom ≫ f = f) :
    (twistedFrobenius Ω f p e hq σ hσ).hom ≫ pullback.snd f (baseMap k Ω) =
      pullback.snd f (baseMap k Ω) ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p e)) := by
  simp only [twistedFrobenius, baseChangeAut, Iso.trans_hom, Category.assoc,
    frobeniusTwist_hom_comp_snd, baseChangeEndo_snd_assoc]

/-- The base change of an endomorphism commutes with the Frobenius twist. -/
theorem baseChangeEndo_comp_frobeniusTwist (φ : X ⟶ X) (hφ : φ ≫ f = f) :
    baseChangeEndo Ω f φ hφ ≫ (frobeniusTwist Ω p e hq f).hom =
      (frobeniusTwist Ω p e hq f).hom ≫ baseChangeEndo Ω f φ hφ := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, frobeniusTwist_hom_comp_snd, baseChangeEndo_snd,
      baseChangeEndo_snd_assoc]

/-- For `n` a multiple of the order of `σ`, `Φ ^ n` and `Ψ ^ n` agree on points. -/
theorem twistedFrobenius_base_iterate_of_dvd (σ : X ≅ X) (hσ : σ.hom ≫ f = f) {n : ℕ}
    (hσn : compPow σ.hom n = 𝟙 X) (j : ℕ) :
    (⇑(twistedFrobenius Ω f p e hq σ hσ).hom.base)^[n * j] =
      (⇑(frobeniusTwist Ω p e hq f).hom.base)^[n * j] := by
  set a := ⇑(baseChangeEndo Ω f σ.hom hσ).base
  set b := ⇑(frobeniusTwist Ω p e hq f).hom.base
  have hcomm : Function.Commute b a := by
    intro x
    have := congrArg (fun φ ↦ φ.base x)
      (baseChangeEndo_comp_frobeniusTwist Ω f p e hq σ.hom hσ)
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
  have hΦ : ⇑(twistedFrobenius Ω f p e hq σ hσ).hom.base = b ∘ a := rfl
  have ha : a^[n] = id := by
    rw [base_iterate_eq_compPow, compPow_baseChangeEndo]
    have : baseChangeEndo Ω f (compPow σ.hom n) (compPow_comp_eq f σ.hom hσ n) = 𝟙 _ := by
      rw [← baseChangeEndo_id Ω f]
      congr 1
    rw [this]
    rfl
  rw [hΦ, hcomm.comp_iterate, Function.iterate_mul a, ha, Function.iterate_id]
  rfl

section Bound

variable {f}

/-- The number of closed points of `X_Ω` fixed by `Φ ^ m`. -/
abbrev twistedFixedCount (σ : X ≅ X) (hσ : σ.hom ≫ f = f) (m : ℕ) : ℕ :=
  Nat.card {x : geometricBaseChange Ω f | IsClosed ({x} : Set (geometricBaseChange Ω f)) ∧
    (⇑(twistedFrobenius Ω f p e hq σ hσ).hom.base)^[m] x = x}

/-- For `n ∣ m`, `n` the order of `σ`, the fixed points of `Φ ^ m` are counted by `X(K)`, `K` an
extension of `k` of degree `m`. -/
theorem twistedFixedCount_eq_of_dvd [LocallyOfFiniteType f] (σ : X ≅ X) (hσ : σ.hom ≫ f = f)
    {n : ℕ} (hσn : compPow σ.hom n = 𝟙 X) (j : ℕ) (K : Type u) [Field K] [Finite K]
    [Algebra k K] (hK : Module.finrank k K = n * j) :
    twistedFixedCount Ω p e hq σ hσ (n * j) =
      Nat.card (Stacks.EtaleCohomology.fieldValuedPoints f K) := by
  have := Fintype.ofFinite K
  rw [← natCard_fixed_frobeniusTwist Ω p e hq f K (n * j) hK, twistedFixedCount,
    twistedFrobenius_base_iterate_of_dvd Ω f p e hq σ hσ hσn j]

end Bound

/-- **The Weil bound for a twisted Frobenius.** Let `X` be a smooth, proper, geometrically
irreducible curve of genus `g` over a finite field `k` with `q` elements and `σ` an automorphism of
`X` over `k` with `σ ^ n = 𝟙` for some `n ≥ 1`. Then for every `m ≥ 1` the closed points of
`X_Ω`, `Ω` an algebraic closure of `k`, fixed by `(Ψ ∘ σ_Ω) ^ m` number `N` with
`|N - q ^ m - 1| ≤ 2 g √q ^ m`. -/
theorem abs_natCard_fixed_twistedFrobenius_sub_le [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] [IsCurve k f] (p : ℕ) [Fact p.Prime] [CharP k p]
    [CharP (AlgebraicClosure k) p] (e : ℕ) (hq : Fintype.card k = p ^ e) (σ : X ≅ X)
    (hσ : σ.hom ≫ f = f) {n : ℕ} (hn : 0 < n) (hσn : compPow σ.hom n = 𝟙 X) {m : ℕ}
    (hm : 0 < m) :
    |(twistedFixedCount (AlgebraicClosure k) p e hq σ hσ m : ℝ) - (Fintype.card k : ℝ) ^ m - 1| ≤
      2 * genus f * Real.sqrt (Fintype.card k) ^ m := by
  set Ω := AlgebraicClosure k
  have : GeometricallyIntegral f := Stacks.AbelMap.geometricallyIntegral_of_smooth f
  have hpb := IsPullback.of_hasPullback f (baseMap k Ω)
  set g := pullback.snd f (baseMap k Ω)
  have : IsProper g := Stacks.AbelMap.isProper_of_isPullback f _ _ hpb
  have : IsCurve Ω g :=
    { toIsIntegral := Stacks.AbelMap.isIntegral_of_isPullback f _ _ hpb
      topologicalKrullDim_eq_one :=
        Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback f _ _ hpb }
  have hgenus : genus g = genus f := genus_baseChange k Ω _ g f hpb
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero] at hq
      exact absurd hq (Fintype.one_lt_card (α := k)).ne'
    · exact h
  set Φ := twistedFrobenius Ω f p e hq σ hσ
  have hΦ := twistedFrobenius_hom_comp_snd Ω f p e hq σ hσ
  obtain ⟨-, -, r, α, hr, -, hN⟩ := Stacks.Zeta.exists_zeta_roots_of_isCurve p g e he Φ hΦ
    (isAlgebraic_zmod_algebraicClosure k p)
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  set N : ℕ → ℕ := fun m ↦ twistedFixedCount Ω p e hq σ hσ m
  have hNα : ∀ m : ℕ, m ≠ 0 →
      (N m : ℂ) = 1 - (∑ i, (ι (α i)) ^ m) + (Fintype.card k : ℂ) ^ m := by
    intro m hm
    have h := congrArg ι (hN m (Nat.pos_of_ne_zero hm)).1
    rw [map_natCast] at h
    change (twistedFixedCount Ω p e hq σ hσ m : ℂ) = _
    rw [twistedFixedCount, h, hq]
    simp only [map_add, map_sub, map_one, map_sum, map_pow, map_natCast]
    push_cast
    ring
  have hbound : ∀ m : ℕ, 1 ≤ m → n ∣ m →
      |(N m : ℝ) - (Fintype.card k : ℝ) ^ m - 1| ≤
        (2 * genus f) * Real.sqrt (Fintype.card k) ^ m := by
    rintro m hm ⟨j, rfl⟩
    obtain ⟨K, _, _, _, hK⟩ := FrobeniusSplitting.exists_finrank_eq k (n := n * j) (by omega)
    have hcardK : Fintype.card K = Fintype.card k ^ (n * j) := by
      rw [← hK]
      exact Module.card_eq_pow_finrank
    have hW := abs_natCard_fieldValuedPoints_sub_le f K
    have hsqrt : Real.sqrt (Fintype.card K) = Real.sqrt (Fintype.card k) ^ (n * j) := by
      rw [hcardK, Nat.cast_pow, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
        ← mul_pow, Real.mul_self_sqrt (by positivity)]
    change |(twistedFixedCount Ω p e hq σ hσ (n * j) : ℝ) - _ - 1| ≤ _
    rw [twistedFixedCount_eq_of_dvd Ω p e hq σ hσ hσn j K hK]
    rwa [hsqrt, hcardK, Nat.cast_pow] at hW
  have hle : ∀ i, ‖ι (α i)‖ ≤ Real.sqrt (Fintype.card k) := fun i ↦
    Stacks.TraceFormula.norm_le_sqrt_of_pointCount (fun i ↦ ι (α i)) Fintype.card_pos N hNα
      hn.ne' 1 hbound i
  have hnorm : ‖(∑ i, (ι (α i)) ^ m : ℂ)‖ ≤ r * Real.sqrt (Fintype.card k) ^ m := by
    calc ‖(∑ i, (ι (α i)) ^ m : ℂ)‖ ≤ ∑ i, ‖ι (α i)‖ ^ m := by
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_pow, le_refl]
      _ ≤ ∑ _i : Fin r, Real.sqrt (Fintype.card k) ^ m :=
          Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hle i) m
      _ = r * Real.sqrt (Fintype.card k) ^ m := by simp
  change |(N m : ℝ) - _ - 1| ≤ _
  have h : (((N m : ℝ) - Fintype.card k ^ m - 1 : ℝ) : ℂ) = -∑ i, (ι (α i)) ^ m := by
    push_cast
    linear_combination hNα m hm.ne'
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h, norm_neg]
  refine hnorm.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [← hgenus]
  exact_mod_cast hr

section Points

variable [LocallyOfFiniteType f]

omit [Fintype k] [IsAlgClosed Ω] [LocallyOfFiniteType f] in
/-- An automorphism of `X_Ω` maps closed points to closed points. -/
theorem isClosed_iso_hom (θ : geometricBaseChange Ω f ≅ geometricBaseChange Ω f)
    (x : closedPoints (geometricBaseChange Ω f)) :
    θ.hom.base x.1 ∈ closedPoints (geometricBaseChange Ω f) := by
  rw [mem_closedPoints_iff]
  have h := θ.hom.homeomorph.isClosedMap _ x.2
  rwa [Set.image_singleton] at h

omit [Fintype k] in
/-- On `X(Ω)`, the base change `σ_Ω` of an automorphism is postcomposition with `σ`. -/
theorem closedPointsEquiv_baseChangeAut (σ : X ≅ X) (hσ : σ.hom ≫ f = f)
    (x : closedPoints (geometricBaseChange Ω f)) :
    closedPointsEquiv Ω f ⟨_, isClosed_iso_hom Ω f (baseChangeAut Ω f σ hσ) x⟩ =
      ⟨(closedPointsEquiv Ω f x).1 ≫ σ.hom, by
        rw [Category.assoc, hσ]; exact (closedPointsEquiv Ω f x).2⟩ := by
  have hs := pointOfClosedPoint_comp (pullback.snd f (baseMap k Ω)) x.1 x.2
  have hs' : (pointOfClosedPoint (pullback.snd f (baseMap k Ω)) x.1 x.2 ≫
      (baseChangeAut Ω f σ hσ).hom) ≫ pullback.snd f (baseMap k Ω) = 𝟙 _ := by
    rw [Category.assoc]
    change _ ≫ baseChangeEndo Ω f σ.hom hσ ≫ _ = _
    rw [baseChangeEndo_snd, hs]
  have heq : pointOfClosedPoint (pullback.snd f (baseMap k Ω)) x.1 x.2 ≫
      (baseChangeAut Ω f σ hσ).hom =
      pointOfClosedPoint (pullback.snd f (baseMap k Ω)) _
        (isClosed_iso_hom Ω f (baseChangeAut Ω f σ hσ) x) :=
    ext_of_apply_closedPoint_eq (pullback.snd f (baseMap k Ω)) hs'
      (pointOfClosedPoint_comp _ _ _)
      ((congrArg (fun y ↦ (baseChangeAut Ω f σ hσ).hom.base y)
        (pointOfClosedPoint_apply _ x.1 x.2 _)).trans
        (pointOfClosedPoint_apply _ _ (isClosed_iso_hom Ω f (baseChangeAut Ω f σ hσ) x) _).symm)
  apply Subtype.ext
  simp only [closedPointsEquiv_apply]
  rw [← heq, Category.assoc]
  change _ ≫ baseChangeEndo Ω f σ.hom hσ ≫ _ = _
  rw [baseChangeEndo_fst, Category.assoc]

end Points

/-- For `m ≡ 1` modulo the order `n` of `σ`, `Φ ^ m = Ψ ^ m ∘ σ_Ω` on points. -/
theorem twistedFrobenius_base_iterate_mul_add_one (σ : X ≅ X) (hσ : σ.hom ≫ f = f) {n : ℕ}
    (hσn : compPow σ.hom n = 𝟙 X) (j : ℕ) :
    (⇑(twistedFrobenius Ω f p e hq σ hσ).hom.base)^[n * j + 1] =
      (⇑(frobeniusTwist Ω p e hq f).hom.base)^[n * j + 1] ∘
        ⇑(baseChangeEndo Ω f σ.hom hσ).base := by
  rw [Function.iterate_succ, twistedFrobenius_base_iterate_of_dvd Ω f p e hq σ hσ hσn j,
    Function.iterate_succ]
  rfl

/-- **Points with a prescribed twisted Frobenius.** Let `X` be a smooth, proper, geometrically
irreducible curve of genus `g` over a finite field `k` with `q` elements, `σ` an automorphism of
`X` over `k` with `σ ^ n = 𝟙`, and `m = n j + 1` with `2 g √q ^ m < q ^ m`. Then some point
`z ∈ X(Ω)`, `Ω` an algebraic closure of `k`, satisfies `z ∘ σ = Frob_{q^m} ∘ z`, in the form
`Spec(Frob_{q^m}⁻¹) ≫ z ≫ σ = z`. -/
theorem exists_fieldValuedPoint_twisted [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [IsCurve k f] (p : ℕ) [Fact p.Prime] [CharP k p] [CharP (AlgebraicClosure k) p] (e : ℕ)
    (hq : Fintype.card k = p ^ e) (σ : X ≅ X) (hσ : σ.hom ≫ f = f) {n : ℕ} (hn : 0 < n)
    (hσn : compPow σ.hom n = 𝟙 X) (j : ℕ)
    (hlarge : 2 * genus f * Real.sqrt (Fintype.card k) ^ (n * j + 1) <
      (Fintype.card k : ℝ) ^ (n * j + 1)) :
    ∃ z : Stacks.EtaleCohomology.fieldValuedPoints f (AlgebraicClosure k),
      fieldValuedPointsPrecomp f
        ((frobeniusAlgEquiv (AlgebraicClosure k) p e hq).symm ^ (n * j + 1) :
          AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k).toAlgHom
        ⟨z.1 ≫ σ.hom, by rw [Category.assoc, hσ]; exact z.2⟩ = z := by
  set Ω := AlgebraicClosure k
  have : LocallyOfFiniteType f := inferInstance
  have hb := abs_natCard_fixed_twistedFrobenius_sub_le f p e hq σ hσ hn hσn
    (m := n * j + 1) (Nat.succ_pos _)
  have hpos : 0 < twistedFixedCount Ω p e hq σ hσ (n * j + 1) := by
    have : (0 : ℝ) < twistedFixedCount Ω p e hq σ hσ (n * j + 1) := by
      linarith [(abs_le.1 hb).1]
    exact_mod_cast this
  obtain ⟨⟨y, hy, hfix⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  rw [twistedFrobenius_base_iterate_mul_add_one Ω f p e hq σ hσ hσn j] at hfix
  set y₀ : closedPoints (geometricBaseChange Ω f) := ⟨y, hy⟩
  set y₁ : closedPoints (geometricBaseChange Ω f) :=
    ⟨_, isClosed_iso_hom Ω f (baseChangeAut Ω f σ hσ) y₀⟩
  refine ⟨closedPointsEquiv Ω f y₀, ?_⟩
  have h2 := closedPointsEquiv_frobeniusTwist_iterate Ω p e hq f (n * j + 1) y₁
  have h3 : (⟨_, isClosed_frobeniusTwist_iterate Ω p e hq f (n * j + 1) y₁⟩ :
      closedPoints (geometricBaseChange Ω f)) = y₀ := Subtype.ext hfix
  rw [h3, closedPointsEquiv_baseChangeAut Ω f σ hσ y₀] at h2
  exact h2.symm

end Stacks.Drinfeld
