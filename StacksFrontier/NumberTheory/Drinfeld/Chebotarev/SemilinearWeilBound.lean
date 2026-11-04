module

public import StacksFrontier.NumberTheory.Drinfeld.TwistedWeilBound
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.SplitPoints

/-!
# The Weil bound for a Frobenius twisted by a semilinear automorphism

Let `Z` be a smooth, proper, geometrically irreducible curve of genus `g` over a finite field `κ`
of characteristic `p`, `Ω` an algebraic closure of `κ` and `Z_Ω = Z ×_κ Spec Ω`. Let `σ` be an
automorphism of the scheme `Z` of finite order which is `p ^ E`-semilinear over `κ` for some
`E ≥ 1`: `σ ≫ r = r ≫ Spec (a ↦ a ^ p ^ E)` for the structure morphism `r : Z ⟶ Spec κ`. Then
`Θ = σ × Spec (a ↦ a ^ p ^ E)` is a `p ^ E`-semilinear automorphism of `Z_Ω`, and for every
`m ≥ 1` the points `z ∈ Z(Ω)` with `σ ^ m ∘ z = z ∘ Spec (a ↦ a ^ p ^ (E m))` number `N m` with

`|N m - (p ^ E) ^ m - 1| ≤ 2 g √(p ^ E) ^ m`.

This generalizes `Stacks.Drinfeld.abs_natCard_fixed_twistedFrobenius_sub_le` (the case where `σ`
is `κ`-linear and `p ^ E = #κ`) to the deck transformations of a Galois cover which act
nontrivially on the field of constants, which is what the Chebotarev density theorem for the
non-geometric Frobenius classes needs.

## The proof

`Θ` is `p ^ E`-semilinear, so the zeta function of `Θ` is rational
(`Stacks.Zeta.exists_zeta_roots_of_isCurve`): `N m = 1 + (p ^ E) ^ m - ∑ α_i ^ m` with `r ≤ 2 g`
algebraic integers `α_i`. If `n` is the order of `σ` and `#κ = p ^ e`, then for `m` a multiple of
`n e` the condition on `z` reads `z = z ∘ Spec (a ↦ a ^ (#κ) ^ (E m / e))`, so `N m = #Z(K)` for an
extension `K` of `κ` of degree `E m / e`, and the Weil bound for `Z` bounds it. Along this
progression `‖α_i‖ ≤ √(p ^ E)` (`Stacks.TraceFormula.norm_le_sqrt_of_pointCount`), which gives the
bound for every `m`.

## Main definitions

* `Stacks.Drinfeld.semilinearBaseChange`: `Θ = σ × Spec (a ↦ a ^ p ^ E)`.

## Main results

* `Stacks.Drinfeld.abs_natCard_semilinearFixed_sub_le`: the bound.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.WeilBound

universe u

namespace Stacks.Drinfeld

variable {κ : Type u} [Field κ] (Ω : Type u) [Field Ω] [Algebra κ Ω]
  {Z : Scheme.{u}} (r : Z ⟶ Spec (.of κ)) (p : ℕ) [Fact p.Prime] [CharP κ p] [CharP Ω p]

/-- The `p ^ E`-Frobenius commutes with the structure morphism `Spec Ω ⟶ Spec κ`. -/
theorem specMap_iterateFrobenius_comp_baseMap (E : ℕ) :
    baseMap κ Ω ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E)) =
      Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p E)) ≫ baseMap κ Ω := by
  simp only [baseMap, ← Spec.map_comp]
  congr 1
  ext a
  simp [iterateFrobenius_def, map_pow]

/-- **The semilinear base change** `Θ = σ × Spec (a ↦ a ^ p ^ E)` of an endomorphism `σ` of `Z`
which is `p ^ E`-semilinear over `κ`. -/
def semilinearBaseChange (σ : Z ⟶ Z) (E : ℕ)
    (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) :
    geometricBaseChange Ω r ⟶ geometricBaseChange Ω r :=
  pullback.map r (baseMap κ Ω) r (baseMap κ Ω) σ
    (Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p E)))
    (Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) hσ.symm
    (specMap_iterateFrobenius_comp_baseMap Ω p E)

/-- The first projection intertwines `Θ` with `σ`: `Θ ≫ pr₁ = pr₁ ≫ σ`. -/
@[reassoc (attr := simp)]
theorem semilinearBaseChange_fst (σ : Z ⟶ Z) (E : ℕ)
    (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) :
    semilinearBaseChange Ω r p σ E hσ ≫ pullback.fst r (baseMap κ Ω) =
      pullback.fst r (baseMap κ Ω) ≫ σ :=
  pullback.lift_fst _ _ _

/-- The second projection intertwines `Θ` with the `p ^ E`-Frobenius of `Ω`:
`Θ ≫ pr₂ = pr₂ ≫ Spec (a ↦ a ^ p ^ E)`. -/
@[reassoc (attr := simp)]
theorem semilinearBaseChange_snd (σ : Z ⟶ Z) (E : ℕ)
    (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) :
    semilinearBaseChange Ω r p σ E hσ ≫ pullback.snd r (baseMap κ Ω) =
      pullback.snd r (baseMap κ Ω) ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p E)) :=
  pullback.lift_snd _ _ _

/-- A composite of endomorphisms is an isomorphism if the endomorphism is. -/
theorem isIso_compPow {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIso φ] (m : ℕ) : IsIso (compPow φ m) := by
  induction m with
  | zero => exact inferInstanceAs (IsIso (𝟙 Y))
  | succ m ih => exact inferInstanceAs (IsIso (φ ≫ compPow φ m))

/-- The `m`-th power of `Θ` lies over `σ ^ m`: `Θ ^ m ≫ pr₁ = pr₁ ≫ σ ^ m`. -/
theorem compPow_semilinearBaseChange_fst (σ : Z ⟶ Z) (E : ℕ)
    (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) (m : ℕ) :
    compPow (semilinearBaseChange Ω r p σ E hσ) m ≫ pullback.fst r (baseMap κ Ω) =
      pullback.fst r (baseMap κ Ω) ≫ compPow σ m := by
  induction m with
  | zero => simp [compPow]
  | succ m ih =>
    simp only [compPow, Category.assoc, ih, semilinearBaseChange_fst_assoc]

/-- The `m`-th power of `Θ` lies over the `p ^ (E m)`-Frobenius of `Ω`:
`Θ ^ m ≫ pr₂ = pr₂ ≫ Spec (a ↦ a ^ p ^ (E m))`. -/
theorem compPow_semilinearBaseChange_snd (σ : Z ⟶ Z) (E : ℕ)
    (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) (m : ℕ) :
    compPow (semilinearBaseChange Ω r p σ E hσ) m ≫ pullback.snd r (baseMap κ Ω) =
      pullback.snd r (baseMap κ Ω) ≫
        Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (E * m))) := by
  induction m with
  | zero => simp [compPow]
  | succ m ih =>
    simp only [compPow, Category.assoc, ih, semilinearBaseChange_snd_assoc, ← Spec.map_comp]
    congr 2
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [mul_add, mul_one, add_comm, iterateFrobenius_add_apply]

/-- `Θ` is an isomorphism when `σ` is, over perfect fields. -/
private theorem isIso_semilinearBaseChange [PerfectRing κ p] [PerfectRing Ω p] (σ : Z ⟶ Z)
    [IsIso σ] (E : ℕ) (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) :
    IsIso (semilinearBaseChange Ω r p σ E hσ) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) :=
    inferInstanceAs (IsIso (Spec.map (iterateFrobeniusEquiv κ p E).toCommRingCatIso.hom))
  have : IsIso (Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p E))) :=
    inferInstanceAs (IsIso (Spec.map (iterateFrobeniusEquiv Ω p E).toCommRingCatIso.hom))
  unfold semilinearBaseChange
  infer_instance

section Points

variable [IsAlgClosed Ω] [LocallyOfFiniteType r]

/-- **An endomorphism of `Z_Ω` over a field endomorphism of `Ω`, read on `Z(Ω)`.** If
`φ ≫ pr₁ = pr₁ ≫ a` and `φ ≫ pr₂ = pr₂ ≫ Spec τ`, then a closed point `y` of `Z_Ω` with `φ y`
closed has `Spec τ ≫ z_{φ y} = z_y ≫ a` on the corresponding points of `Z(Ω)`. -/
theorem specMap_comp_closedPointsEquiv (φ : geometricBaseChange Ω r ⟶ geometricBaseChange Ω r)
    (a : Z ⟶ Z) (τ : Ω →+* Ω)
    (hfst : φ ≫ pullback.fst r (baseMap κ Ω) = pullback.fst r (baseMap κ Ω) ≫ a)
    (hsnd : φ ≫ pullback.snd r (baseMap κ Ω) =
      pullback.snd r (baseMap κ Ω) ≫ Spec.map (CommRingCat.ofHom τ))
    (y : closedPoints (geometricBaseChange Ω r))
    (hy : IsClosed ({φ.base y.1} : Set (geometricBaseChange Ω r))) :
    Spec.map (CommRingCat.ofHom τ) ≫ (closedPointsEquiv Ω r ⟨_, hy⟩).1 =
      (closedPointsEquiv Ω r y).1 ≫ a := by
  set g := pullback.snd r (baseMap κ Ω)
  have heq : Spec.map (CommRingCat.ofHom τ) ≫ pointOfClosedPoint g _ hy =
      pointOfClosedPoint g y.1 y.2 ≫ φ := by
    refine ext_of_apply_closedPoint_eq_of_comp_eq g hy ?_ ?_ ?_
    · exact pointOfClosedPoint_apply g _ hy _
    · exact congrArg φ.base (pointOfClosedPoint_apply g y.1 y.2 _)
    · rw [Category.assoc, Category.assoc, pointOfClosedPoint_comp g _ hy, hsnd,
        reassoc_of% (pointOfClosedPoint_comp g y.1 y.2), Category.comp_id]
  simp only [closedPointsEquiv_apply]
  rw [← Category.assoc, heq, Category.assoc, hfst, Category.assoc]

/-- The fixed points of `Θ ^ m` among the closed points of `Z_Ω` are the points `z ∈ Z(Ω)` with
`z ≫ σ ^ m = Spec (a ↦ a ^ p ^ (E m)) ≫ z`. -/
theorem natCard_closed_fixed_semilinearBaseChange [PerfectRing κ p] [PerfectRing Ω p]
    (σ : Z ⟶ Z) [IsIso σ] (E : ℕ)
    (hσ : σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E))) (m : ℕ) :
    Nat.card {y : geometricBaseChange Ω r | IsClosed ({y} : Set (geometricBaseChange Ω r)) ∧
        (⇑(semilinearBaseChange Ω r p σ E hσ).base)^[m] y = y} =
      Nat.card {z : Stacks.EtaleCohomology.fieldValuedPoints r Ω // z.1 ≫ compPow σ m =
        Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (E * m))) ≫ z.1} := by
  set Θ := semilinearBaseChange Ω r p σ E hσ
  have : IsIso Θ := isIso_semilinearBaseChange Ω r p σ E hσ
  set φ := compPow Θ m
  have : IsIso φ := isIso_compPow Θ m
  have hφ : (⇑Θ.base)^[m] = ⇑φ.base := base_iterate_eq_compPow Θ m
  have hcl : ∀ y : closedPoints (geometricBaseChange Ω r),
      IsClosed ({φ.base y.1} : Set (geometricBaseChange Ω r)) := fun y => by
    have h := (asIso φ).hom.homeomorph.isClosedMap _ y.2
    rw [Set.image_singleton] at h
    exact h
  have hiff : ∀ c : closedPoints (geometricBaseChange Ω r), (⇑Θ.base)^[m] c.1 = c.1 ↔
      (closedPointsEquiv Ω r c).1 ≫ compPow σ m =
        Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (E * m))) ≫
          (closedPointsEquiv Ω r c).1 := by
    intro c
    rw [hφ]
    have h := specMap_comp_closedPointsEquiv Ω r φ (compPow σ m) _
      (compPow_semilinearBaseChange_fst Ω r p σ E hσ m)
      (compPow_semilinearBaseChange_snd Ω r p σ E hσ m) c (hcl c)
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [show (⟨_, hcl c⟩ : closedPoints (geometricBaseChange Ω r)) = c from Subtype.ext hc] at h
      exact h.symm
    · rw [hc] at h
      exact congrArg Subtype.val ((closedPointsEquiv Ω r).injective
        (Subtype.ext (specMap_comp_injective (Y := Z) (iterateFrobenius Ω p (E * m)) h)))
  let e1 : {y : geometricBaseChange Ω r | IsClosed ({y} : Set (geometricBaseChange Ω r)) ∧
      (⇑Θ.base)^[m] y = y} ≃
      {c : closedPoints (geometricBaseChange Ω r) // (⇑Θ.base)^[m] c.1 = c.1} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      invFun := fun c => ⟨c.1.1, c.1.2, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr (e1.trans ((closedPointsEquiv Ω r).subtypeEquiv hiff))

end Points

/-- The composites of an endomorphism add: `φ ^ (a + b) = φ ^ a ≫ φ ^ b`. -/
theorem compPow_add {Y : Scheme.{u}} (φ : Y ⟶ Y) (a b : ℕ) :
    compPow φ (a + b) = compPow φ a ≫ compPow φ b := by
  induction a with
  | zero => simp [compPow]
  | succ a ih =>
    rw [Nat.succ_add, compPow, compPow, ih, Category.assoc]

/-- If `φ ^ n = 𝟙` then `φ ^ (n j) = 𝟙`. -/
theorem compPow_mul_eq_id {Y : Scheme.{u}} (φ : Y ⟶ Y) {n : ℕ} (hn : compPow φ n = 𝟙 Y)
    (j : ℕ) : compPow φ (n * j) = 𝟙 Y := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.mul_succ, compPow_add, ih, hn, Category.id_comp]

/-- If `φ ^ n = 𝟙` then `φ ^ (n j + 1) = φ`. -/
theorem compPow_mul_add_one {Y : Scheme.{u}} (φ : Y ⟶ Y) {n : ℕ} (hn : compPow φ n = 𝟙 Y)
    (j : ℕ) : compPow φ (n * j + 1) = φ := by
  rw [compPow_add, compPow_mul_eq_id φ hn, Category.id_comp]
  exact Category.comp_id φ

section Fixed

variable [Fintype κ] [IsAlgClosed Ω]

/-- **The points of `Z(Ω)` fixed by a power of the `#κ`-Frobenius** are the points of `Z(K)`, `K`
an extension of `κ` of the corresponding degree. -/
def fixedIterateFrobeniusEquiv (e : ℕ) (hq : Fintype.card κ = p ^ e) (K : Type u) [Field K]
    [Fintype K] [Algebra κ K] (N : ℕ) (hK : Module.finrank κ K = N) :
    Stacks.EtaleCohomology.fieldValuedPoints r K ≃
      {z : Stacks.EtaleCohomology.fieldValuedPoints r Ω //
        z.1 = Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * N))) ≫ z.1} := by
  let j : K →ₐ[κ] Ω := IsAlgClosed.lift
  let τ := frobeniusAlgEquiv Ω p e hq ^ N
  have hτ' : (τ.toAlgHom : Ω →+* Ω) = iterateFrobenius Ω p (e * N) := by
    ext a
    change τ a = _
    rw [frobeniusAlgEquiv_pow_apply, hq, iterateFrobenius_def, ← pow_mul]
  have hcardK : Fintype.card K = Fintype.card κ ^ N := hK ▸ Module.card_eq_pow_finrank
  have hj : ∀ c : K, τ.toAlgHom (j c) = j c := fun c => by
    change τ (j c) = j c
    rw [frobeniusAlgEquiv_pow_apply, ← map_pow, ← hcardK, FiniteField.pow_card]
  have hτ : ∀ a : Ω, τ.toAlgHom a = a → a ∈ Set.range j := fun a ha => by
    change τ a = a at ha
    rw [frobeniusAlgEquiv_pow_apply, ← hcardK] at ha
    exact mem_range_of_pow_card_eq j.toRingHom ha
  refine (fixedFieldValuedPointsEquiv r j τ.toAlgHom hj hτ).trans
    (Equiv.subtypeEquivRight fun z => ?_)
  refine Subtype.ext_iff.trans ?_
  change Spec.map (CommRingCat.ofHom (τ.toAlgHom : Ω →+* Ω)) ≫ z.1 = z.1 ↔ _
  rw [hτ', eq_comm]

omit [CharP κ p] in
/-- **The points of `Z(Ω)` fixed by a power of the `#κ`-Frobenius** are counted by `Z(K)`, `K` an
extension of `κ` of the corresponding degree. -/
theorem natCard_fixed_iterateFrobenius (e : ℕ) (hq : Fintype.card κ = p ^ e) (K : Type u)
    [Field K] [Finite K] [Algebra κ K] (N : ℕ) (hK : Module.finrank κ K = N) :
    Nat.card {z : Stacks.EtaleCohomology.fieldValuedPoints r Ω //
        z.1 = Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * N))) ≫ z.1} =
      Nat.card (Stacks.EtaleCohomology.fieldValuedPoints r K) := by
  have := Fintype.ofFinite K
  exact (Nat.card_congr (fixedIterateFrobeniusEquiv Ω r p e hq K N hK)).symm

end Fixed

/-- **The Weil bound for a Frobenius twisted by a semilinear automorphism.** Let `Z` be a smooth,
proper, geometrically irreducible curve of genus `g` over a finite field `κ` of characteristic `p`,
and `σ` an automorphism of the scheme `Z` with `σ ^ n = 𝟙` for some `n ≥ 1` which is
`p ^ E`-semilinear over `κ`, `E ≥ 1`. Then for every `m ≥ 1` the points `z ∈ Z(Ω)`, `Ω` an
algebraic closure of `κ`, with `z ≫ σ ^ m = Spec (a ↦ a ^ p ^ (E m)) ≫ z` number `N` with
`|N - (p ^ E) ^ m - 1| ≤ 2 g √(p ^ E) ^ m`. -/
theorem abs_natCard_semilinearFixed_sub_le [Fintype κ] [IsProper r] [Smooth r]
    [GeometricallyIrreducible r] [IsCurve κ r] (p : ℕ) [Fact p.Prime] [CharP κ p]
    [CharP (AlgebraicClosure κ) p] (e : ℕ) (hq : Fintype.card κ = p ^ e) (σ : Z ≅ Z) (E : ℕ)
    (hE : 0 < E) (hσ : σ.hom ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E)))
    {n : ℕ} (hn : 0 < n) (hσn : compPow σ.hom n = 𝟙 Z) {m : ℕ} (hm : 0 < m) :
    |(Nat.card {z : Stacks.EtaleCohomology.fieldValuedPoints r (AlgebraicClosure κ) //
        z.1 ≫ compPow σ.hom m =
          Spec.map (CommRingCat.ofHom (iterateFrobenius (AlgebraicClosure κ) p (E * m))) ≫ z.1} :
        ℝ) - ((p ^ E : ℕ) : ℝ) ^ m - 1| ≤
      2 * genus r * Real.sqrt (p ^ E : ℕ) ^ m := by
  set Ω := AlgebraicClosure κ
  have : GeometricallyIntegral r := Stacks.AbelMap.geometricallyIntegral_of_smooth r
  have hpb := IsPullback.of_hasPullback r (baseMap κ Ω)
  set g := pullback.snd r (baseMap κ Ω)
  have : IsProper g := Stacks.AbelMap.isProper_of_isPullback r _ _ hpb
  have : IsCurve Ω g :=
    { toIsIntegral := Stacks.AbelMap.isIntegral_of_isPullback r _ _ hpb
      topologicalKrullDim_eq_one :=
        Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback r _ _ hpb }
  have hgenus : genus g = genus r := genus_baseChange κ Ω _ g r hpb
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq
    exact absurd hq (Fintype.one_lt_card (α := κ)).ne'
  have : IsIso (semilinearBaseChange Ω r p σ.hom E hσ) :=
    isIso_semilinearBaseChange Ω r p σ.hom E hσ
  set Θ := asIso (semilinearBaseChange Ω r p σ.hom E hσ)
  obtain ⟨-, -, rr, α, hr, -, hN⟩ := Stacks.Zeta.exists_zeta_roots_of_isCurve p g E hE Θ
    (semilinearBaseChange_snd Ω r p σ.hom E hσ) (isAlgebraic_zmod_algebraicClosure κ p)
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  set N : ℕ → ℕ := fun m => Nat.card {z : Stacks.EtaleCohomology.fieldValuedPoints r Ω //
    z.1 ≫ compPow σ.hom m = Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (E * m))) ≫ z.1}
  have hNclosed : ∀ m : ℕ, N m = Nat.card {y : geometricBaseChange Ω r |
      IsClosed ({y} : Set (geometricBaseChange Ω r)) ∧ (⇑Θ.hom.base)^[m] y = y} := fun m =>
    (natCard_closed_fixed_semilinearBaseChange Ω r p σ.hom E hσ m).symm
  have hNα : ∀ m : ℕ, m ≠ 0 →
      (N m : ℂ) = 1 - (∑ i, (ι (α i)) ^ m) + ((p ^ E : ℕ) : ℂ) ^ m := by
    intro m hm
    have h := congrArg ι (hN m (Nat.pos_of_ne_zero hm)).1
    rw [map_natCast] at h
    rw [hNclosed m, h]
    simp only [map_add, map_sub, map_one, map_sum, map_pow, map_natCast]
    ring
  have hbound : ∀ m : ℕ, 1 ≤ m → n * e ∣ m →
      |(N m : ℝ) - ((p ^ E : ℕ) : ℝ) ^ m - 1| ≤
        (2 * genus r) * Real.sqrt (p ^ E : ℕ) ^ m := by
    rintro m hm ⟨j, rfl⟩
    have hj : j ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨K, _, _, _, hK⟩ :=
      FrobeniusSplitting.exists_finrank_eq κ (n := E * n * j) (by positivity)
    have hcardK : (Fintype.card K : ℝ) = ((p ^ E : ℕ) : ℝ) ^ (n * e * j) := by
      have h1 : Fintype.card K = Fintype.card κ ^ (E * n * j) := by
        rw [← hK]
        exact Module.card_eq_pow_finrank
      rw [h1, hq]
      push_cast
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hW := abs_natCard_fieldValuedPoints_sub_le r K
    have hcomp : compPow σ.hom (n * e * j) = 𝟙 Z := by
      rw [mul_assoc]
      exact compPow_mul_eq_id σ.hom hσn _
    have hNK : N (n * e * j) = Nat.card (Stacks.EtaleCohomology.fieldValuedPoints r K) := by
      rw [← natCard_fixed_iterateFrobenius Ω r p e hq K (E * n * j) hK]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
      have hexp : E * (n * e * j) = e * (E * n * j) := by ring
      rw [hcomp, Category.comp_id, hexp]
    rw [hNK]
    rw [hcardK] at hW
    have hsqrt : Real.sqrt (((p ^ E : ℕ) : ℝ) ^ (n * e * j)) =
        Real.sqrt (p ^ E : ℕ) ^ (n * e * j) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
        Real.mul_self_sqrt (by positivity)]
    rw [hsqrt] at hW
    exact hW
  have hle : ∀ i, ‖ι (α i)‖ ≤ Real.sqrt (p ^ E : ℕ) := fun i =>
    Stacks.TraceFormula.norm_le_sqrt_of_pointCount (fun i => ι (α i))
      (pow_pos (Fact.out : p.Prime).pos E) N hNα (Nat.mul_ne_zero hn.ne' he) 1 hbound i
  have hsum : ((N m : ℝ) - ((p ^ E : ℕ) : ℝ) ^ m - 1 : ℝ) =
      -(∑ i, (ι (α i)) ^ m : ℂ).re ∧ (∑ i, (ι (α i)) ^ m : ℂ).im = 0 := by
    have h := hNα m hm.ne'
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.natCast_re, Complex.sub_re, Complex.add_re, Complex.one_re,
      Complex.natCast_im, Complex.sub_im, Complex.add_im, Complex.one_im] at hre him
    rw [← Complex.ofReal_natCast (p ^ E), ← Complex.ofReal_pow, Complex.ofReal_re] at hre
    rw [← Complex.ofReal_natCast (p ^ E), ← Complex.ofReal_pow, Complex.ofReal_im] at him
    refine ⟨?_, by linarith⟩
    linarith
  have hnorm : ‖(∑ i, (ι (α i)) ^ m : ℂ)‖ ≤ rr * Real.sqrt (p ^ E : ℕ) ^ m := by
    calc ‖(∑ i, (ι (α i)) ^ m : ℂ)‖ ≤ ∑ i, ‖ι (α i)‖ ^ m := by
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_pow, le_refl]
      _ ≤ ∑ _i : Fin rr, Real.sqrt (p ^ E : ℕ) ^ m :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hle i) m
      _ = rr * Real.sqrt (p ^ E : ℕ) ^ m := by simp
  change |(N m : ℝ) - _ - 1| ≤ _
  rw [hsum.1, abs_neg]
  have hreal : |(∑ i, (ι (α i)) ^ m : ℂ).re| = ‖(∑ i, (ι (α i)) ^ m : ℂ)‖ :=
    Complex.abs_re_eq_norm.2 hsum.2
  rw [hreal]
  refine hnorm.trans ?_
  have hr' : (rr : ℝ) ≤ 2 * genus r := by
    rw [← hgenus]
    exact_mod_cast hr
  exact mul_le_mul_of_nonneg_right hr' (by positivity)

end Stacks.Drinfeld

end
