module

public import StacksFrontier.NumberTheory.Drinfeld.Chebotarev.FrobeniusPoint
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Chebotarev density theorem for the fundamental group of a curve over a finite field

Let `X` be a smooth, proper, geometrically irreducible curve over a finite field `k` and `S` a
finite set of closed points of `X`. **The Frobenius elements of `π₁(X, base)` at the closed points
outside `S` are dense** (`AlgebraicGeometry.dense_frobeniusElements_compl`). Equivalently, every
coset `g U` of an open normal subgroup `U` contains a Frobenius element at a closed point outside
`S` (`AlgebraicGeometry.exists_frobeniusData_element_mem_smul_of_finite`).

As a consequence, two continuous representations `ρ, ρ' : π₁(X, base) → GL_n(E)`, `E` a Hausdorff
topological ring, whose traces agree at the Frobenius elements outside `S` have the same trace
everywhere (`AlgebraicGeometry.trace_eq_of_forall_frobeniusElements`). This is the "Chebotarev
density" step in Drinfeld's construction of the Galois representation attached to a cusp
eigenform (Stacks Theorem 03VT): together with Brauer–Nesbitt
(`Stacks.Drinfeld.exists_conj_of_trace_eq`) it shows that a semisimple `ℓ`-adic representation is
determined by its Frobenius traces.

## The proof

Let `U` be an open normal subgroup and `g ∈ π₁`. Let `Z` be the connected Galois cover of `X` with
fibre `π₁ / U` (`AlgebraicGeometry.exists_galoisCover_stabilizer_eq`), `z₀` the point of stabilizer
`U`, and `σ` the deck transformation with `σ z₀ = g z₀`; it has some finite order `n`. Then `Z` is
a smooth proper geometrically irreducible curve over its field of constants `κ`, finite over `k`
(`AlgebraicGeometry.exists_constantField_of_finiteEtale`), and `σ` acts on `κ` as `a ↦ a ^ q ^ c`
for some `c ≥ 1` (`AlgebraicGeometry.exists_algHom_comp_specMap`,
`AlgebraicGeometry.exists_algHom_eq_iterateFrobenius`).

For `m = n j + 1` and `D = c m`, the semilinear twisted Weil bound
(`Stacks.Drinfeld.abs_natCard_semilinearFixed_sub_le`) gives at least
`q ^ D + 1 - 2 g_Z √q ^ D` points `z ∈ Z(Ω)` with `z ≫ σ = Spec (a ↦ a ^ q ^ D) ≫ z`. The image
`x̄ ∈ X(Ω)` of such a `z` is fixed by `Spec (a ↦ a ^ q ^ D)`, so it lies over a closed point `x` of
degree `d ∣ D`. If `d < D` then `d ≤ D / 2` and `x̄` is fixed by `Spec (a ↦ a ^ q ^ d)`; there are
at most `#X(k_d) ≤ (2 g + 2) √q ^ D` such `x̄` for each `d`, each with `deg(Z / X)` lifts. So at
most `D deg(Z / X) (2 g + 2) √q ^ D` points `z` are bad, and for `j` large some `z` has image of
degree exactly `D`, larger than the degrees of the points of `S`. For such a `z` the local
Frobenius at `x̄` acts on the lift `z` as `σ` does, and transporting to the base point gives a
Frobenius element at `x ∉ S` in `g U` (`Stacks.Drinfeld.exists_frobeniusData_element_smul_eq`,
`Stacks.Drinfeld.exists_frobeniusData_element_mem_smul`).

## Main results

* `AlgebraicGeometry.exists_frobeniusData_element_mem_smul_of_finite`.
* `AlgebraicGeometry.dense_frobeniusElements_compl`: Chebotarev density.
* `AlgebraicGeometry.trace_eq_of_forall_frobeniusElements`: equal Frobenius traces off `S` give
  equal traces.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Filter Topology AlgebraicGeometry.WeilBound Stacks.EtaleCohomology
  Stacks.Drinfeld

open scoped Pointwise

universe u

namespace AlgebraicGeometry

section Arithmetic

/-- An exponential beats a linear function: for `b > 1` there is `D₀` with `A + B D < b ^ D` for
all `D ≥ D₀`. -/
theorem exists_forall_ge_add_mul_lt_pow {b : ℝ} (hb : 1 < b) (A B : ℝ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → A + B * D < b ^ D := by
  have hb0 : 0 < b := one_pos.trans hb
  have h1 : Tendsto (fun D : ℕ => (b⁻¹) ^ D) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hb0.le) (inv_lt_one_of_one_lt₀ hb)
  have h2 : Tendsto (fun D : ℕ => (D : ℝ) ^ 1 / b ^ D) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 hb
  have h3 : Tendsto (fun D : ℕ => A * (b⁻¹) ^ D + B * ((D : ℝ) ^ 1 / b ^ D)) atTop (𝓝 0) := by
    simpa using (h1.const_mul A).add (h2.const_mul B)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.1 (h3.eventually (gt_mem_nhds one_pos))
  refine ⟨D₀, fun D hD => ?_⟩
  have h := hD₀ D hD
  have heq : A * (b⁻¹) ^ D + B * ((D : ℝ) ^ 1 / b ^ D) = (A + B * D) / b ^ D := by
    rw [inv_pow, pow_one]
    field_simp
  rwa [heq, div_lt_one (pow_pos hb0 D)] at h

/-- A proper divisor of a positive natural number `D` lies in `[1, D / 2]`. -/
theorem mem_Icc_one_div_two_of_dvd_of_ne {d D : ℕ} (hD : D ≠ 0) (hdvd : d ∣ D) (hne : d ≠ D) :
    d ∈ Finset.Icc 1 (D / 2) := by
  obtain ⟨a, rfl⟩ := hdvd
  rcases a with _ | _ | a
  · simp at hD
  · simp at hne
  · rw [Finset.mem_Icc, Nat.le_div_iff_mul_le two_pos]
    exact ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hD), Nat.mul_le_mul_left _ (by omega)⟩

end Arithmetic

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [ConnectedSpace X]

/-- The lifts of a geometric point of `X` to a finite étale cover are in bijection with the fibre
at the base point. -/
private theorem nonempty_equiv_lifts (base : GeometricPoint X) (Z : FiniteEtaleOver X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    Nonempty ({w : Spec (.of Ω) ⟶ Z.left // w ≫ Z.hom = t} ≃
      (finiteEtaleFiberFunctor base).obj Z) := by
  obtain ⟨i⟩ := nonempty_finiteEtaleFiberFunctorIso (x := (⟨Ω, t⟩ : GeometricPoint X))
    (x' := base)
  exact ⟨(i.app Z).toEquiv⟩

/-- The points of a finite étale cover over a geometric point are as many as those of the fibre
at the base point. -/
theorem natCard_lifts_eq (base : GeometricPoint X) (Z : FiniteEtaleOver X) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    Nat.card {w : Spec (.of Ω) ⟶ Z.left // w ≫ Z.hom = t} =
      Nat.card ((finiteEtaleFiberFunctor base).obj Z) :=
  Nat.card_congr (nonempty_equiv_lifts base Z t).some

omit [ConnectedSpace ↥X] in
/-- The `m`-fold composite of the underlying morphism of an automorphism in `FiniteEtaleOver X`
is the underlying morphism of its `m`-th power. -/
theorem compPow_left_eq_pow_left (Z : FiniteEtaleOver X) (σ : Aut Z) (m : ℕ) :
    compPow σ.asIso.hom.left m = (σ ^ m).asIso.hom.left := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Aut.mul_asIso, compPow, ih]
    rfl

/-- **Chebotarev density, coset form.** Let `X` be a smooth, proper, geometrically irreducible
curve over a finite field, `S` a finite set of closed points, `U` an open normal subgroup of
`π₁(X, base)` and `g ∈ π₁(X, base)`. Some Frobenius element at a closed point outside `S` lies in
`g U`. -/
theorem exists_frobeniusData_element_mem_smul_of_finite (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [Smooth f] [IsProper f] [GeometricallyIrreducible f] (base : GeometricPoint X)
    {S : Set (closedPoints X)} (hS : S.Finite) (U : Subgroup (EtaleFundamentalGroup X base))
    (hUn : U.Normal) (hUo : IsOpen (U : Set (EtaleFundamentalGroup X base)))
    (g : EtaleFundamentalGroup X base) :
    ∃ x ∉ S, ∃ c : FrobeniusData base x,
      c.element ∈ g • (U : Set (EtaleFundamentalGroup X base)) := by
  classical
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨e', -, hq'⟩ := FiniteField.card k p
  set e : ℕ := (e' : ℕ)
  have hq : Fintype.card k = p ^ e := hq'
  set q := Fintype.card k
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  -- the Galois cover with fibre `π₁ / U` and the deck transformation `σ`
  obtain ⟨Z, hZc, hZgal, z₀, hstab, htrans⟩ := exists_galoisCover_stabilizer_eq U hUn hUo
  have := hZc
  have := hZgal
  set F := finiteEtaleFiberFintypeFunctor X base
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut Z) (show F.obj Z from z₀)
    (show F.obj Z from g • z₀)
  have hσ' : (finiteEtaleFiberFunctor base).map σ.asIso.hom z₀ = g • z₀ := hσ
  have : Finite ((finiteEtaleFiberFunctor base).obj Z) :=
    forall_finite_finiteEtaleFiberFunctor_obj base Z
  have : Finite (Aut Z) := Finite.of_injective _
    (PreGaloisCategory.evaluation_aut_injective_of_isConnected F Z (show F.obj Z from z₀))
  set n := orderOf σ
  have hn : 0 < n := orderOf_pos σ
  let σs : Z.left ≅ Z.left :=
    { hom := σ.asIso.hom.left
      inv := σ.asIso.inv.left
      hom_inv_id := congrArg (fun φ : Z ⟶ Z => φ.left) σ.asIso.hom_inv_id
      inv_hom_id := congrArg (fun φ : Z ⟶ Z => φ.left) σ.asIso.inv_hom_id }
  have hσn : compPow σs.hom n = 𝟙 Z.left := by
    change compPow σ.asIso.hom.left n = _
    rw [compPow_left_eq_pow_left, pow_orderOf_eq_one]
    rfl
  -- the field of constants of `Z` and the action of `σ` on it
  obtain ⟨κ, _, _, _, r, hr, hP, hSm, hG, hC⟩ := exists_constantField_of_finiteEtale k f Z
  have : Finite κ := Module.finite_of_finite k
  let : Fintype κ := Fintype.ofFinite κ
  have : CharP κ p := charP_of_injective_algebraMap (algebraMap k κ).injective p
  have : IsFinite Z.hom := Z.prop.1
  have : IsIntegral Z.left := hC.toIsIntegral
  have : IsProper (r ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ))) := by
    rw [hr]
    infer_instance
  have hσr0 : σs.hom ≫ r ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) := by
    rw [hr, ← Category.assoc]
    change σ.asIso.hom.left ≫ Z.hom ≫ f = _
    rw [← Category.assoc, MorphismProperty.Over.w σ.asIso.hom]
  obtain ⟨θ, hθ⟩ := exists_algHom_comp_specMap r σs.hom hσr0
  obtain ⟨c, hc, hθc⟩ := exists_algHom_eq_iterateFrobenius p e hq θ
  set E := e * c
  have hE : 0 < E := Nat.mul_pos (Nat.pos_of_ne_zero (by
    rintro h0
    rw [h0, pow_zero] at hq
    omega)) hc
  have hσθ : σs.hom ≫ r = r ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius κ p E)) := by
    rw [hθ, hθc]
  -- the algebraic closure
  set Ω := AlgebraicClosure κ
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap κ Ω).injective p
  have : Algebra.IsAlgebraic k κ := Algebra.IsAlgebraic.of_finite k κ
  have : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.trans k κ Ω
  obtain ⟨eκ', -, hqκ'⟩ := FiniteField.card κ p
  have hqκ : Fintype.card κ = p ^ (eκ' : ℕ) := hqκ'
  -- the constants of the count
  set gX := genus f
  set gZ := genus r
  set dZ := Nat.card ((finiteEtaleFiberFunctor base).obj Z)
  set M : ℕ := (hS.toFinset.image fun x : closedPoints X => residueDegree f x.1).sup id
  have hM : ∀ x ∈ S, residueDegree f x.1 ≤ M := fun x hx =>
    Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx))
  have hsq : 1 < Real.sqrt q := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
    exact_mod_cast hq2
  obtain ⟨D₀, hD₀⟩ := exists_forall_ge_add_mul_lt_pow hsq (2 * gZ) (dZ * (2 * gX + 2))
  -- the choice of `m = n j + 1` and `D = c m`
  set j := D₀ + M
  set m := n * j + 1
  set D := c * m
  have hDj : D₀ + M + 1 ≤ D := by
    have : j + 1 ≤ m := by
      change j + 1 ≤ n * j + 1
      have := Nat.le_mul_of_pos_left j hn
      omega
    calc D₀ + M + 1 = j + 1 := rfl
      _ ≤ m := this
      _ ≤ c * m := Nat.le_mul_of_pos_left m hc
  have hD : D ≠ 0 := by omega
  have hlarge : 2 * (gZ : ℝ) + dZ * (2 * gX + 2) * D < Real.sqrt q ^ D := by
    have := hD₀ D (by omega)
    linarith
  have hDM : M < D := by omega
  -- the twisted points
  set T := {z : fieldValuedPoints r Ω // z.1 ≫ compPow σs.hom m =
    Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (E * m))) ≫ z.1}
  have hEm : E * m = e * D := by
    change e * c * m = e * (c * m)
    ring
  have hcompm : compPow σs.hom m = σs.hom := compPow_mul_add_one σs.hom hσn j
  have hbound := abs_natCard_semilinearFixed_sub_le r p (eκ' : ℕ) hqκ σs E hE hσθ hn hσn
    (m := m) (Nat.succ_pos _)
  have hnat : (p ^ E) ^ m = q ^ D := by
    rw [← pow_mul, hEm, pow_mul, ← hq]
  have hpE : ((p ^ E : ℕ) : ℝ) ^ m = Real.sqrt q ^ D * Real.sqrt q ^ D := by
    rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast hnat
  have hsqpow : ∀ a : ℕ, Real.sqrt ((q : ℝ) ^ a) = Real.sqrt q ^ a := fun a => by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by positivity)]
  have hpc : p ^ E = q ^ c := by
    change p ^ (e * c) = _
    rw [hq, ← pow_mul]
  have hsqrtE : Real.sqrt (p ^ E : ℕ) ^ m = Real.sqrt q ^ D := by
    rw [hpc, Nat.cast_pow, hsqpow c, ← pow_mul]
  rw [hpE, hsqrtE] at hbound
  have hTlow : Real.sqrt q ^ D * Real.sqrt q ^ D + 1 - 2 * gZ * Real.sqrt q ^ D ≤ Nat.card T := by
    have := (abs_le.1 hbound).1
    linarith
  set s := Real.sqrt q ^ D
  have hs1 : 1 ≤ s := one_le_pow₀ hsq.le
  have hTpos : 0 < Nat.card T := by
    have h1 : (0 : ℝ) < Nat.card T := by
      have : 2 * (gZ : ℝ) < s := by
        have h0 : (0 : ℝ) ≤ dZ * (2 * gX + 2) * D := by positivity
        linarith
      nlinarith
    exact_mod_cast h1
  have : Finite T := (Nat.card_pos_iff.1 hTpos).2
  -- every twisted point lies over `X(Ω)` and is fixed there by the Frobenius of degree `D`
  have hzX : ∀ z : T, z.1.1 ≫ Z.hom ≫ f = baseMap k Ω := fun z => by
    rw [← hr, ← Category.assoc, z.1.2]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
  have htw : ∀ z : T, z.1.1 ≫ σ.asIso.hom.left =
      Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * D))) ≫ z.1.1 := fun z =>
    (congrArg (fun φ => z.1.1 ≫ φ) hcompm.symm).trans (z.2.trans
      (congrArg (fun N => Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p N)) ≫ z.1.1) hEm))
  set tX : T → fieldValuedPoints f Ω := fun z => ⟨z.1.1 ≫ Z.hom, by
    rw [Category.assoc]; exact hzX z⟩
  have hfixX : ∀ z : T, Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * D))) ≫ (tX z).1 =
      (tX z).1 := fun z => by
    change _ ≫ z.1.1 ≫ Z.hom = z.1.1 ≫ Z.hom
    rw [← Category.assoc, ← htw z, Category.assoc, MorphismProperty.Over.w σ.asIso.hom]
  -- a good point exists
  by_cases hgood : ∃ z : T, residueDegree f (Scheme.SpecToEquivOfField Ω X (tX z).1).1 = D
  · obtain ⟨z, hz⟩ := hgood
    obtain ⟨hcl, cd, w, hw⟩ := exists_frobeniusData_element_smul_eq f Ω p e hq base Z σ.asIso.hom
      z.1.1 (hzX z) hD (htw z) hz
    obtain ⟨c', hc'⟩ := exists_frobeniusData_element_mem_smul Z σ.asIso.hom U g z₀ hstab htrans hσ'
      cd w hw
    refine ⟨_, fun hxS => ?_, c', hc'⟩
    have := hM _ hxS
    change residueDegree f (Scheme.SpecToEquivOfField Ω X (tX z).1).1 ≤ M at this
    omega
  · exfalso
    simp only [not_exists] at hgood
    -- the bad points inject into the lifts of the points of degree at most `D / 2`
    set I := {d : ℕ // d ∈ Finset.Icc 1 (D / 2)}
    set Fx : ℕ → Type u := fun d => {t : fieldValuedPoints f Ω //
      t.1 = Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * d))) ≫ t.1}
    set L : (Σ d : I, Fx d.1) → Type u := fun b =>
      {w : Spec (.of Ω) ⟶ Z.left // w ≫ Z.hom = b.2.1.1}
    have hdeg : ∀ z : T, residueDegree f (Scheme.SpecToEquivOfField Ω X (tX z).1).1 ∈
        Finset.Icc 1 (D / 2) := fun z =>
      mem_Icc_one_div_two_of_dvd_of_ne hD
        (isClosed_and_dvd_of_fixed f Ω p e hq (tX z) hD (hfixX z)).2 (hgood z)
    let ι : T → Σ b : (Σ d : I, Fx d.1), L b := fun z =>
      ⟨⟨⟨_, hdeg z⟩, ⟨tX z, (specMap_iterateFrobenius_residueDegree_comp f Ω p e hq (tX z)
        (by have := (Finset.mem_Icc.1 (hdeg z)).1; omega)).symm⟩⟩, ⟨z.1.1, rfl⟩⟩
    have hι : Function.Injective ι := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun y : Σ b : (Σ d : I, Fx d.1), L b => y.2.1) hab))
    -- the count of the target
    have hFx : ∀ d : I, Finite (Fx d.1) ∧ Nat.card (Fx d.1) ≤ (2 * gX + 2) * s := fun d => by
      have hd := Finset.mem_Icc.1 d.2
      obtain ⟨K, _, _, _, hK⟩ := FrobeniusSplitting.exists_finrank_eq k (n := d.1) (by omega)
      have := Stacks.BombieriStepanov.finite_fieldValuedPoints f K
      refine ⟨Finite.of_equiv _ (fixedIterateFrobeniusEquiv Ω f p e hq K d.1 hK), ?_⟩
      have h1 := natCard_fixed_iterateFrobenius Ω f p e hq K d.1 hK
      have hW := abs_natCard_fieldValuedPoints_sub_le f K
      have hcardK : (Fintype.card K : ℝ) = Real.sqrt q ^ (2 * d.1) := by
        rw [pow_mul, Real.sq_sqrt (by positivity), ← hK]
        exact_mod_cast Module.card_eq_pow_finrank
      have hsK : Real.sqrt (Fintype.card K) = Real.sqrt q ^ d.1 := by
        rw [hcardK, pow_mul', Real.sqrt_sq (by positivity)]
      rw [hsK, hcardK] at hW
      change (Nat.card (Fx d.1) : ℝ) ≤ _
      rw [show Nat.card (Fx d.1) = _ from h1]
      have h2 : Real.sqrt q ^ (2 * d.1) ≤ s := pow_le_pow_right₀ hsq.le (by omega)
      have h3 : Real.sqrt q ^ d.1 ≤ s := pow_le_pow_right₀ hsq.le (by omega)
      have hg0 : (0 : ℝ) ≤ gX := by positivity
      have := (abs_le.1 hW).2
      nlinarith
    have : ∀ d : I, Finite (Fx d.1) := fun d => (hFx d).1
    have hLcard : ∀ b : (Σ d : I, Fx d.1), Nat.card (L b) = dZ := fun b =>
      natCard_lifts_eq base Z b.2.1.1
    have : ∀ b : (Σ d : I, Fx d.1), Finite (L b) := fun b => by
      exact Finite.of_equiv _ (nonempty_equiv_lifts base Z b.2.1.1).some.symm
    let : Fintype (Σ d : I, Fx d.1) := Fintype.ofFinite _
    let : ∀ d : I, Fintype (Fx d.1) := fun d => Fintype.ofFinite _
    have hcard1 : Nat.card (Σ b : (Σ d : I, Fx d.1), L b) =
        Nat.card (Σ d : I, Fx d.1) * dZ := by
      rw [Nat.card_sigma]
      simp only [hLcard, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Nat.card_eq_fintype_card]
    have hcard2 : (Nat.card (Σ d : I, Fx d.1) : ℝ) ≤ D * ((2 * gX + 2) * s) := by
      rw [Nat.card_sigma]
      push_cast
      calc (∑ d : I, (Nat.card (Fx d.1) : ℝ)) ≤ ∑ _d : I, (2 * gX + 2) * s :=
            Finset.sum_le_sum fun d _ => (hFx d).2
        _ = Fintype.card I * ((2 * gX + 2) * s) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ D * ((2 * gX + 2) * s) := by
            have hI : Fintype.card I = D / 2 := by
              rw [Fintype.card_coe, Nat.card_Icc]
              omega
            have hI' : (Fintype.card I : ℝ) ≤ D := by
              rw [hI]
              exact_mod_cast Nat.div_le_self D 2
            exact mul_le_mul_of_nonneg_right hI' (by positivity)
    have hTup : (Nat.card T : ℝ) ≤ D * ((2 * gX + 2) * s) * dZ := by
      have h1 := Nat.card_le_card_of_injective ι hι
      rw [hcard1] at h1
      have h2 : (Nat.card T : ℝ) ≤ (Nat.card (Σ d : I, Fx d.1) : ℝ) * dZ := mod_cast h1
      exact h2.trans (mul_le_mul_of_nonneg_right hcard2 (by positivity))
    have hgZ : (0 : ℝ) ≤ gZ := by positivity
    have hX0 : (0 : ℝ) ≤ dZ * (2 * gX + 2) * D := by positivity
    nlinarith [hTlow, hTup, hlarge, hs1]

/-- **Chebotarev density for the fundamental group of a curve over a finite field.** Let `X` be a
smooth, proper, geometrically irreducible curve over a finite field and `S` a finite set of
closed points of `X`. The Frobenius elements of `π₁(X, base)` at the closed points outside `S`
are dense. -/
theorem dense_frobeniusElements_compl (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    [IsProper f] [GeometricallyIrreducible f] (base : GeometricPoint X)
    {S : Set (closedPoints X)} (hS : S.Finite) : Dense (frobeniusElements base Sᶜ) := by
  have := compactSpace_etaleFundamentalGroup X base
  have := totallyDisconnectedSpace_etaleFundamentalGroup X base
  rw [dense_iff_inter_open]
  rintro O hO ⟨g, hg⟩
  have hopen : IsOpen (g⁻¹ • O) := hO.leftCoset g⁻¹
  have hone : (1 : EtaleFundamentalGroup X base) ∈ g⁻¹ • O :=
    ⟨g, hg, inv_mul_cancel g⟩
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  obtain ⟨x, hx, c, hc⟩ := exists_frobeniusData_element_mem_smul_of_finite f base hS
    N.toOpenSubgroup.toSubgroup inferInstance N.toOpenSubgroup.isOpen g
  refine ⟨c.element, ?_, x, hx, c, rfl⟩
  obtain ⟨u, hu, hcu⟩ := hc
  obtain ⟨o, ho, hou⟩ := hN hu
  rw [← hcu, ← hou]
  simpa using ho

/-- **Equal Frobenius traces off a finite set give equal traces.** Two continuous representations
`ρ, ρ' : π₁(X, base) → GL_n(E)`, `E` a Hausdorff topological ring, whose traces agree at all
Frobenius elements at the closed points outside a finite set `S` have the same trace at every
element of `π₁(X, base)`. -/
theorem trace_eq_of_forall_frobeniusElements (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    [IsProper f] [GeometricallyIrreducible f] (base : GeometricPoint X)
    {S : Set (closedPoints X)} (hS : S.Finite) {n : Type*} [Fintype n] [DecidableEq n]
    {E : Type*} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    (ρ ρ' : EtaleFundamentalGroup X base →* Matrix.GeneralLinearGroup n E)
    (hρ : Continuous fun γ => (ρ γ : Matrix n n E))
    (hρ' : Continuous fun γ => (ρ' γ : Matrix n n E))
    (htr : ∀ F ∈ frobeniusElements base Sᶜ,
      Matrix.trace (ρ F : Matrix n n E) = Matrix.trace (ρ' F : Matrix n n E))
    (γ : EtaleFundamentalGroup X base) :
    Matrix.trace (ρ γ : Matrix n n E) = Matrix.trace (ρ' γ : Matrix n n E) :=
  (dense_frobeniusElements_compl f base hS).induction htr
    (isClosed_eq hρ.matrix_trace hρ'.matrix_trace) γ

end AlgebraicGeometry

end
