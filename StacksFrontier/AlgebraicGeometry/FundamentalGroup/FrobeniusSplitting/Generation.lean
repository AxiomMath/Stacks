module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.SplitPoints
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.QuotientCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.ConstantField
public import StacksFrontier.AlgebraicGeometry.Curves.WeilBound.WeilBound
public import StacksFrontier.AlgebraicGeometry.Curves.EtaleCoverGenus

/-!
# Frobenius elements at finitely many closed points generate `π₁` of a curve over a finite field

**Stacks Tag 03W5.** Let `X` be a smooth, proper, geometrically irreducible curve over a finite
field `k`. There is a finite set of closed points of `X` such that the set of **all** Frobenius
elements at these points topologically generates `π₁(X)`.

## The proof

This is the proof of the source. Let `q = #k` and `g` the genus of `X`, and pick `N` with
`√(q^(N-1)) ≥ 8(g + 1)`. Let `S` be the set of closed points of degree at most `N`; it is finite.
The Frobenius elements at `S` form a conjugation-stable set, so
(`frobeniusElements_topologicalClosure_eq_top`) it suffices to show that a proper open normal
subgroup `U` of `π₁(X)` cannot contain them all. Suppose it does.

* There is a connected Galois finite étale cover `Z ⟶ X` with `d ≥ 2` points in its geometric
  fibres on which `U` acts trivially (`AlgebraicGeometry.exists_connected_cover_of_isOpen_normal`).
* Every point of `X` of degree at most `N` splits completely in `Z`, so for `n ≤ N`,
  `#Z(k_n) ≥ d · #X(k_n)`
  (`AlgebraicGeometry.FrobeniusSplitting.card_mul_le_natCard_fieldValuedPoints`).
* By the Weil bound for `X`, `X` has points over `k_N` and `k_(N-1)`, hence so does `Z`, so `Z` is
  geometrically irreducible over `k`
  (`AlgebraicGeometry.FrobeniusSplitting.isCurve_comp_of_coprime`).
* By the Riemann–Hurwitz formula for the étale cover `Z ⟶ X`, `g_Z - 1 = d (g - 1)`
  (`AlgebraicGeometry.genus_sub_one_eq_of_isGalois`).
* The Weil bound for `Z` and for `X` at `k_N` then give
  `d (q^N + 1 - 2 g q^(N/2)) ≤ #Z(k_N) ≤ q^N + 1 + 2 g_Z q^(N/2)`, which is impossible for
  `d ≥ 2` by the choice of `N`.

## Main results

* `AlgebraicGeometry.exists_finite_closedPoints_frobeniusElements_topologicalClosure_eq_top`:
  **Stacks Tag 03W5.**
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology FrobeniusSplitting WeilBound

section Arithmetic

/-- The arithmetic at the end of the proof of Tag 03W5: if `s ≥ 8 (g + 1)`, `d ≥ 2` and
`g_Z - 1 = d (g - 1)` with `g_Z ≥ 0`, then
`d (s ^ 2 + 1 - 2 g s) ≤ s ^ 2 + 1 + 2 g_Z s` is impossible. -/
theorem not_le_of_genus_eq {s : ℝ} {g d gZ : ℤ} (hs : 8 * ((g : ℝ) + 1) ≤ s) (hg : 0 ≤ g)
    (hd : 2 ≤ d) (hgZ : 0 ≤ gZ) (hRH : gZ - 1 = d * (g - 1)) :
    ¬ ((d : ℝ) * (s ^ 2 + 1 - 2 * g * s) ≤ s ^ 2 + 1 + 2 * gZ * s) := by
  intro h
  have hRH' : (gZ : ℝ) = d * (g - 1) + 1 := by
    have : ((gZ - 1 : ℤ) : ℝ) = ((d * (g - 1) : ℤ) : ℝ) := by rw [hRH]
    push_cast at this
    linarith
  have hgR : (0 : ℝ) ≤ g := by exact_mod_cast hg
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hgZR : (0 : ℝ) ≤ gZ := by exact_mod_cast hgZ
  have hs0 : 0 < s := by linarith
  rw [hRH'] at h
  -- `(d - 1) (s² + 1) ≤ (4 d g - 2 d + 2) s ≤ 8 (d - 1) g s`
  have h1 : ((d : ℝ) - 1) * (s ^ 2 + 1) ≤ 8 * ((d : ℝ) - 1) * g * s := by nlinarith
  have h2 : s ^ 2 + 1 ≤ 8 * g * s := by
    have hd1 : 0 < (d : ℝ) - 1 := by linarith
    nlinarith
  nlinarith

/-- If `n ≥ 2 · 8 (g + 1)` and `q ≥ 2`, then `√q ^ n ≥ 8 (g + 1)`. -/
theorem eight_mul_succ_le_sqrt_pow {q g n : ℕ} (hq : 2 ≤ q) (hn : 2 * (8 * (g + 1)) ≤ n) :
    8 * ((g : ℝ) + 1) ≤ Real.sqrt q ^ n := by
  have hM : 8 * (g + 1) < q ^ (8 * (g + 1)) :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hq _)
  have h1 : ((8 * (g + 1) : ℕ) : ℝ) ≤ Real.sqrt q ^ (2 * (8 * (g + 1))) := by
    rw [pow_mul, Real.sq_sqrt (by positivity)]
    exact_mod_cast hM.le
  have h2 : Real.sqrt q ^ (2 * (8 * (g + 1))) ≤ Real.sqrt q ^ n :=
    pow_le_pow_right₀ (Real.one_le_sqrt.2 (by exact_mod_cast hq.trans' one_le_two)) hn
  push_cast at h1
  linarith

end Arithmetic

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A closed point of a scheme locally of finite type over a finite field has a finite residue
field. -/
theorem finite_residueField_of_residueDegree_ne_zero [LocallyOfFiniteType f] (x : X)
    (hx : residueDegree f x ≠ 0) : Finite (X.residueField x) := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have : Module.Finite k (X.residueField x) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hx)
  exact Module.finite_of_finite k

/-- A curve is connected: it is integral. -/
theorem FrobeniusSplitting.connectedSpace_of_isCurve {K : Type u} [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) [IsCurve K g] : ConnectedSpace Y := by
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (f := g)
  infer_instance

/-- A closed point of `X` with finite residue field carries Frobenius data: an algebraic closure of
its residue field and a path to the base point. -/
theorem nonempty_frobeniusData [ConnectedSpace X] (base : GeometricPoint X) (x : closedPoints X)
    (hx : Finite (X.residueField x.1)) : Nonempty (FrobeniusData base x) := by
  let _ : Fintype (X.residueField x.1) := Fintype.ofFinite _
  let xb := (algebraicClosureGeometricPoint (X.residueField x.1)
    (AlgebraicClosure (X.residueField x.1))).map (X.fromSpecResidueField x.1)
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := xb) (x' := base)
  exact ⟨{ closure := AlgebraicClosure (X.residueField x.1)
           finite_residueField := hx
           path := t }⟩

/-- The Weil bound for a curve over `k` at a finite extension `K`, written with
`s = √#k ^ [K : k]`, so that `#K = s ^ 2`: `|#X(K) - s ^ 2 - 1| ≤ 2 g s`. -/
private theorem abs_natCard_fieldValuedPoints_sub_sqrt_pow_le [IsCurve k f] [Smooth f]
    [IsProper f] [GeometricallyIrreducible f] (K : Type u) [Field K] [Finite K] [Algebra k K] :
    |(Nat.card (fieldValuedPoints f K) : ℝ) - (Real.sqrt (Nat.card k) ^ Module.finrank k K) ^ 2
      - 1| ≤ 2 * genus f * Real.sqrt (Nat.card k) ^ Module.finrank k K := by
  have := Fintype.ofFinite k
  have := Fintype.ofFinite K
  have hcard : (Fintype.card K : ℝ) = (Real.sqrt (Nat.card k) ^ Module.finrank k K) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := k)]
    push_cast
    rfl
  have hW := abs_natCard_fieldValuedPoints_sub_le f K
  rwa [hcard, Real.sqrt_sq (by positivity)] at hW

/-- By the Weil bound, a curve over a finite field `k` of genus `g` has a point over every finite
extension of `k` of degree at least `2 · 8 (g + 1)`. -/
theorem natCard_fieldValuedPoints_pos [IsCurve k f] [Smooth f] [IsProper f]
    [GeometricallyIrreducible f] (K : Type u) [Field K] [Finite K] [Algebra k K]
    (hK : 2 * (8 * (genus f + 1)) ≤ Module.finrank k K) :
    0 < Nat.card (fieldValuedPoints f K) := by
  have hW := abs_natCard_fieldValuedPoints_sub_sqrt_pow_le f K
  have hb : 8 * ((genus f : ℝ) + 1) ≤ Real.sqrt (Nat.card k) ^ Module.finrank k K :=
    eight_mul_succ_le_sqrt_pow Finite.one_lt_card hK
  have hg0 : (0 : ℝ) ≤ genus f := by positivity
  by_contra! h0
  have h0' : (Nat.card (fieldValuedPoints f K) : ℝ) = 0 := by
    exact_mod_cast Nat.le_zero.1 h0
  rw [h0', abs_le] at hW
  nlinarith [hW.1]

/-- Let `f' : Y ⟶ Spec k` be a second curve with `g' - 1 = d (g - 1)` for some `d ≥ 2`. By the
Weil bounds, over a finite extension `K` of `k` of degree at least `2 · 8 (g + 1)`,
`#Y(K) < d · #X(K)`. -/
theorem natCard_fieldValuedPoints_lt_mul {Y : Scheme.{u}} (f' : Y ⟶ Spec (.of k)) [IsCurve k f]
    [Smooth f] [IsProper f] [GeometricallyIrreducible f] [IsCurve k f'] [Smooth f'] [IsProper f']
    [GeometricallyIrreducible f'] (K : Type u) [Field K] [Finite K] [Algebra k K]
    (hK : 2 * (8 * (genus f + 1)) ≤ Module.finrank k K) {d : ℕ} (hd : 2 ≤ d)
    (hRH : (genus f' : ℤ) - 1 = d * ((genus f : ℤ) - 1)) :
    Nat.card (fieldValuedPoints f' K) < d * Nat.card (fieldValuedPoints f K) := by
  have hWY := abs_natCard_fieldValuedPoints_sub_sqrt_pow_le f' K
  have hWX := abs_natCard_fieldValuedPoints_sub_sqrt_pow_le f K
  by_contra! h
  refine not_le_of_genus_eq (s := Real.sqrt (Nat.card k) ^ Module.finrank k K)
    (g := genus f) (d := d) (gZ := genus f')
    (eight_mul_succ_le_sqrt_pow (g := genus f) (n := Module.finrank k K) Finite.one_lt_card hK)
    (by positivity) (by exact_mod_cast hd) (by positivity) hRH ?_
  have hcmpR : (d : ℝ) * Nat.card (fieldValuedPoints f K) ≤
      Nat.card (fieldValuedPoints f' K) := by exact_mod_cast h
  rw [abs_le] at hWY hWX
  have hd0 : (0 : ℝ) ≤ d := by positivity
  push_cast
  nlinarith [hWX.1, hWY.2]

/-- **Stacks Project, Tag 03W5.** For a smooth, geometrically irreducible, proper curve over a
finite field there is a finite set of closed points such that the set of **all** Frobenius elements
at these points topologically generates the étale fundamental group. -/
@[stacks 03W5]
theorem exists_finite_closedPoints_frobeniusElements_topologicalClosure_eq_top (k : Type u)
    [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    [IsProper f] [GeometricallyIrreducible f] (base : GeometricPoint X) :
    letI := FrobeniusSplitting.connectedSpace_of_isCurve f
    ∃ S : Set (closedPoints X), S.Finite ∧
      (Subgroup.closure (frobeniusElements base S)).topologicalClosure = ⊤ := by
  let := FrobeniusSplitting.connectedSpace_of_isCurve f
  classical
  let : Fintype k := Fintype.ofFinite k
  set M := 8 * (genus f + 1)
  set N := 2 * M + 1
  set S : Set (closedPoints X) := ↑(closedPointsDegreeLE f N)
  refine ⟨S, Finset.finite_toSet _, frobeniusElements_topologicalClosure_eq_top base S ?_⟩
  intro U hUn hUo hsub
  by_contra hne
  obtain ⟨Z, _, _, hZtriv, hZd⟩ := exists_connected_cover_of_isOpen_normal U hUn hUo hne
  set d := Nat.card ((finiteEtaleFiberFunctor base).obj Z)
  have : IsFinite Z.hom := Z.prop.1
  -- every point of degree dividing `n ≤ N` splits completely in `Z`
  have hsplit : ∀ (K : Type u) [Field K] [Fintype K] [Algebra k K], Module.finrank k K ≤ N →
      d * Nat.card (fieldValuedPoints f K) ≤ Nat.card (fieldValuedPoints (Z.hom ≫ f) K) := by
    intro K _ _ _ hKN
    refine card_mul_le_natCard_fieldValuedPoints f Z K fun t => ?_
    set xι := Scheme.SpecToEquivOfField K X t.1
    have hσ : residueEmbeddings f K xι.1 := ⟨xι.2, by
      have ht2 := t.2
      rwa [← (Scheme.SpecToEquivOfField K X).symm_apply_apply t.1,
        Scheme.SpecToEquivOfField_symm_apply, fromSpecResidueField_comp_eq_iff] at ht2⟩
    obtain ⟨hcl, hdvd⟩ := isClosed_and_dvd_of_residueEmbeddings f K xι.1 hσ
    have hpos : 0 < Module.finrank k K := Module.finrank_pos
    have hdeg0 : residueDegree f xι.1 ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at hdvd
      omega
    obtain ⟨c⟩ := nonempty_frobeniusData base ⟨_, hcl⟩
      (finite_residueField_of_residueDegree_ne_zero f xι.1 hdeg0)
    refine ⟨hcl, c, fun z => hZtriv _ (hsub ⟨⟨_, hcl⟩, ?_, c, rfl⟩) z⟩
    simpa only [S, closedPointsDegreeLE, Finset.coe_sort_coe, Set.Finite.coe_toFinset,
      Set.mem_setOf_eq] using (Nat.le_of_dvd hpos hdvd).trans hKN
  -- extensions of degree `N - 1` and `N`
  obtain ⟨K₁, _, _, _, hK₁⟩ := exists_finrank_eq k (n := 2 * M) (by omega)
  obtain ⟨K₂, _, _, _, hK₂⟩ := exists_finrank_eq k (n := N) (by omega)
  have hZpts : ∀ (K : Type u) [Field K] [Fintype K] [Algebra k K], 2 * M ≤ Module.finrank k K →
      Module.finrank k K ≤ N → Nonempty (fieldValuedPoints (Z.hom ≫ f) K) := by
    intro K _ _ _ h1 h2
    have : Finite (fieldValuedPoints (Z.hom ≫ f) K) :=
      Stacks.BombieriStepanov.finite_fieldValuedPoints (Z.hom ≫ f) K
    exact (Nat.card_pos_iff.1 ((Nat.mul_pos (by omega)
      (natCard_fieldValuedPoints_pos f K h1)).trans_le (hsplit K h2))).1
  obtain ⟨t₁⟩ := hZpts K₁ (by omega) (by omega)
  obtain ⟨t₂⟩ := hZpts K₂ (by omega) (by omega)
  obtain ⟨_, _, _, _⟩ := isCurve_comp_of_coprime f Z K₁ K₂ (by rw [hK₁, hK₂]; simp [N]) t₁ t₂
  -- Riemann–Hurwitz and the Weil bounds at `k_N`
  exact lt_irrefl _ ((natCard_fieldValuedPoints_lt_mul f (Z.hom ≫ f) K₂ (show 2 * M ≤ _ by omega)
    (d := d) (by exact_mod_cast hZd) (genus_sub_one_eq_of_isGalois Z k f base)).trans_le
    (hsplit K₂ hK₂.le))

end AlgebraicGeometry

end
