module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartTowerRing
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The charts `S_(s)` and `S_(t)` of a two-chart tower

For the graded ring `S = ⨁_k lim_n Γ(Xₙ, Lₙ^{⊗ k})` of a good two-chart tower
(`AlgebraicGeometry.C1590Private.TwoChartTower.CompatibleCharts.ring`), this file proves what the
gluing needs of the homogeneous localizations `S_(s)` and `S_(t)`:

* they are flat over `lim Rₙ` (the equational criterion, from the triviality of relations in
  the graded pieces);
* the evaluation `S_(s) → Γ(Xₙ, Uₙ)` is surjective with kernel `Ker(lim R → Rₙ) · S_(s)`, and
  likewise for `t` and `Vₙ`;
* the evaluations are compatible with the localizations `S_(s), S_(t) → S_(st)`, with the
  transition maps of the tower, and with the structure maps.

## Main results

* `…CompatibleCharts.flat_away`: `S_(x)` is flat over `lim Rₙ` for `x = s, t`.
* `…CompatibleCharts.evalU_surjective`, `…CompatibleCharts.ker_evalU` and their `V` versions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Deformation.Artin.SquareZeroTower HomogeneousLocalization

universe u

namespace AlgebraicGeometry.C1590Private.TwoChartTower

/-! ### Two localization facts about a two-chart datum -/

section Local

variable {X : Scheme.{u}} (D : TwoChartDatum X)

/-- Restriction `Γ(X, V) → Γ(X, U ∩ V)` is the localization away from `a`. -/
theorem isLocalization_resV :
    letI := D.resV.toAlgebra
    IsLocalization.Away D.a Γ(X, D.U ⊓ D.V) :=
  D.isAffineOpen_V.isLocalization_of_eq_basicOpen D.a (homOfLE inf_le_right) D.basicOpen_a.symm

/-- Restriction `Γ(X, U) → Γ(X, U ∩ V)` is the localization away from `b`. -/
theorem isLocalization_resU :
    letI := D.resU.toAlgebra
    IsLocalization.Away D.b Γ(X, D.U ⊓ D.V) :=
  D.isAffineOpen_U.isLocalization_of_eq_basicOpen D.b (homOfLE inf_le_left) D.basicOpen_b.symm

/-- A function on `V` vanishing on `U ∩ V` is killed by a power of `a`. -/
theorem exists_pow_a_mul_eq_zero {y : Γ(X, D.V)} (hy : D.resV y = 0) :
    ∃ N : ℕ, D.a ^ N * y = 0 := by
  let := D.resV.toAlgebra
  have := isLocalization_resV D
  obtain ⟨⟨_, N, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers D.a) _ y).mp hy
  exact ⟨N, h⟩

/-- A function on `U` vanishing on `U ∩ V` is killed by a power of `b`. -/
theorem exists_pow_b_mul_eq_zero {x : Γ(X, D.U)} (hx : D.resU x = 0) :
    ∃ N : ℕ, D.b ^ N * x = 0 := by
  let := D.resU.toAlgebra
  have := isLocalization_resU D
  obtain ⟨⟨_, N, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers D.b) _ x).mp hx
  exact ⟨N, h⟩

/-- Every function on `U` is the `U`-coordinate of a section of some positive power of `L`. -/
theorem exists_cechDiff_eq_zero_fst (x : Γ(X, D.U)) :
    ∃ k, 1 ≤ k ∧ ∃ y, D.cechDiff k (x, y) = 0 := by
  let := D.resV.toAlgebra
  have := isLocalization_resV D
  obtain ⟨⟨y, _, N, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers D.a) (D.resU x)
  have h' : D.resU x * D.resV D.a ^ N = D.resV y := by
    simpa [RingHom.algebraMap_toAlgebra] using h
  refine ⟨N + 1, by omega, D.a * y, ?_⟩
  rw [cechDiff_eq_zero_iff, map_mul, ← h']
  calc D.resU x = D.resU x * (D.resU D.b * D.resV D.a) ^ N * (D.resU D.b * D.resV D.a) := by
        rw [resU_b_mul_resV_a D, one_pow, mul_one, mul_one]
    _ = D.resU D.b ^ (N + 1) * (D.resV D.a * (D.resU x * D.resV D.a ^ N)) := by ring

/-- Every function on `V` is the `V`-coordinate of a section of some positive power of `L`. -/
theorem exists_cechDiff_eq_zero_snd (y : Γ(X, D.V)) :
    ∃ k, 1 ≤ k ∧ ∃ x, D.cechDiff k (x, y) = 0 := by
  let := D.resU.toAlgebra
  have := isLocalization_resU D
  obtain ⟨⟨x, _, N, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers D.b) (D.resV y)
  have h' : D.resV y * D.resU D.b ^ N = D.resU x := by
    simpa [RingHom.algebraMap_toAlgebra] using h
  refine ⟨N + 1, by omega, D.b * x, ?_⟩
  rw [cechDiff_eq_zero_iff, map_mul, ← h']
  ring

end Local

/-! ### Homogeneous fractions of degree zero -/

section Fractions

variable {X : ℕ → Scheme.{u}} {ι : ∀ n, X n ⟶ X (n + 1)}

namespace CompatibleCharts

variable (C : CompatibleCharts ι)

/-- Two homogeneous elements of `S` agree when their degrees and their values in the
ambient ring agree. -/
theorem of_eq_of {i j : ℕ} (h : i = j) (x : C.grade i) (y : C.grade j)
    (hxy : (x : C.Amb) = y) :
    DirectSum.of (fun k => C.grade k) i x = DirectSum.of (fun k => C.grade k) j y :=
  DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext h hxy)

/-- The product of homogeneous elements of degrees `i` and `j` of `S` is the homogeneous element
of degree `i + j` given by the product in the ambient ring. -/
theorem of_mul_of' {i j : ℕ} (x : C.grade i) (y : C.grade j) :
    DirectSum.of (fun k => C.grade k) i x * DirectSum.of (fun k => C.grade k) j y =
      DirectSum.of (fun k => C.grade k) (i + j)
        ⟨(x : C.Amb) * (y : C.Amb), SetLike.mul_mem_graded x.2 y.2⟩ :=
  DirectSum.of_mul_of (A := fun k => C.grade k) x y

/-- The `N`-th power of a compatible family of sections of `L` is a compatible family of
sections of `L^{⊗ N}`. -/
theorem pow_mem_grade {w : C.Amb} (hw : w ∈ C.grade 1) (N : ℕ) : w ^ N ∈ C.grade N := by
  induction N with
  | zero => rw [pow_zero]; exact SetLike.one_mem_graded C.grade
  | succ N ih => rw [pow_succ]; exact SetLike.mul_mem_graded ih hw

variable {w : C.Amb} (hw : w ∈ C.grade 1)

/-- The `N`-th power of the degree-one element `x` of `S` defined by `w` is the homogeneous
element `w ^ N` of degree `N`. -/
theorem xElt_pow (N : ℕ) :
    C.xElt hw ^ N = DirectSum.of (fun k => C.grade k) N ⟨w ^ N, C.pow_mem_grade hw N⟩ := by
  induction N with
  | zero =>
    rw [pow_zero, DirectSum.one_def (A := fun k => C.grade k)]
    exact C.of_eq_of rfl _ _ (pow_zero w).symm
  | succ N ih =>
    rw [pow_succ, ih, xElt, of_mul_of']
    exact C.of_eq_of rfl _ _ (pow_succ w N).symm

/-- A compatible family of sections of `L^{⊗ n}` lies in the degree-`n • 1` part of `S`. -/
theorem of_mem_𝒜_smul {n : ℕ} {c : C.Amb} (hc : c ∈ C.grade n) :
    DirectSum.of (fun k => C.grade k) n ⟨c, hc⟩ ∈ C.𝒜 (n • 1) := by
  rw [smul_eq_mul, mul_one]
  exact Stacks.ExternalGrading.of_mem_summand _ _

/-- **The fraction `c / x^n`** of a compatible family `c` of sections of `L^{⊗ n}`. -/
def mkX (n : ℕ) (c : C.Amb) (hc : c ∈ C.grade n) : Away C.𝒜 (C.xElt hw) :=
  Away.mk C.𝒜 (C.xElt_mem hw) n (DirectSum.of (fun k => C.grade k) n ⟨c, hc⟩)
    (C.of_mem_𝒜_smul hc)

/-- The fraction `c / x^n` as an element of the localization of `S` at the powers of `x`. -/
theorem mkX_val (n : ℕ) (c : C.Amb) (hc : c ∈ C.grade n) :
    (C.mkX hw n c hc).val = Localization.mk (DirectSum.of (fun k => C.grade k) n ⟨c, hc⟩)
      ⟨C.xElt hw ^ n, pow_mem (Submonoid.mem_powers _) n⟩ := rfl

/-- The fraction `c / x^n` depends only on `n` and `c`. -/
theorem mkX_congr {n n' : ℕ} (h : n = n') {c c' : C.Amb} (hcc : c = c') (hc : c ∈ C.grade n)
    (hc' : c' ∈ C.grade n') : C.mkX hw n c hc = C.mkX hw n' c' hc' := by
  subst h hcc; rfl

/-- Multiplying numerator and denominator by `x^N`. -/
theorem mkX_bump (N n : ℕ) (c : C.Amb) (hc : c ∈ C.grade n) :
    C.mkX hw n c hc = C.mkX hw (N + n) (w ^ N * c)
      (SetLike.mul_mem_graded (C.pow_mem_grade hw N) hc) := by
  have hof : DirectSum.of (fun k => C.grade k) (N + n)
      ⟨w ^ N * c, SetLike.mul_mem_graded (C.pow_mem_grade hw N) hc⟩ =
        C.xElt hw ^ N * DirectSum.of (fun k => C.grade k) n ⟨c, hc⟩ := by
    rw [C.xElt_pow hw N, of_mul_of']
  ext
  rw [mkX_val, mkX_val, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [hof, pow_add]
  ring

/-- **Every element of `S_(x)` is `c / x^n` with `n ≥ 1`.** -/
theorem exists_mkX_eq (z : Away C.𝒜 (C.xElt hw)) :
    ∃ (n : ℕ) (c : C.Amb) (hc : c ∈ C.grade n), 1 ≤ n ∧ C.mkX hw n c hc = z := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective C.𝒜 (C.xElt_mem hw) z
  obtain ⟨⟨c, hc⟩, hca⟩ := id ha
  subst hca
  have hn : n • 1 = n := by rw [smul_eq_mul, mul_one]
  refine ⟨1 + n, w * c, SetLike.mul_mem_graded hw (hn ▸ hc), by omega, ?_⟩
  ext
  rw [mkX_val, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  have : DirectSum.of (fun k => C.grade k) (1 + n) ⟨w * c, SetLike.mul_mem_graded hw (hn ▸ hc)⟩ =
      C.xElt hw * DirectSum.of (fun k => C.grade k) (n • 1) ⟨c, hc⟩ := by
    rw [xElt, of_mul_of']
    exact C.of_eq_of (by rw [hn]) _ _ rfl
  rw [this, pow_add, pow_one]
  ring

/-- Fractions `c / x^n` with the same denominator add by adding numerators. -/
theorem mkX_add (n : ℕ) (c c' : C.Amb) (hc : c ∈ C.grade n) (hc' : c' ∈ C.grade n) :
    C.mkX hw n c hc + C.mkX hw n c' hc' = C.mkX hw n (c + c') (add_mem hc hc') := by
  ext
  rw [val_add, mkX_val, mkX_val, mkX_val, Localization.add_mk_self, ← map_add]
  rfl

/-- The fraction `0 / x^n` is zero. -/
theorem mkX_zero (n : ℕ) (h : (0 : C.Amb) ∈ C.grade n) : C.mkX hw n 0 h = 0 := by
  ext
  rw [val_zero, mkX_val]
  have : DirectSum.of (fun k => C.grade k) n ⟨0, h⟩ = 0 := map_zero _
  rw [this, Localization.mk_zero]

/-- A finite sum of fractions `cᵢ / x^n` with the same denominator is `(∑ cᵢ) / x^n`. -/
theorem mkX_sum {ι' : Type*} (s : Finset ι') (n : ℕ) (c : ι' → C.Amb)
    (hc : ∀ i, c i ∈ C.grade n) :
    ∑ i ∈ s, C.mkX hw n (c i) (hc i) =
      C.mkX hw n (∑ i ∈ s, c i) (AddSubgroup.sum_mem _ fun i _ => hc i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, C.mkX_congr hw rfl Finset.sum_empty _ (zero_mem _), mkX_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, mkX_add]
    exact C.mkX_congr hw rfl (Finset.sum_insert ha).symm _ _

/-- If `c / x^n` vanishes in `S_(x)`, then `w ^ N * c = 0` for some `N`. -/
theorem mkX_eq_zero {n : ℕ} {c : C.Amb} {hc : c ∈ C.grade n} (h : C.mkX hw n c hc = 0) :
    ∃ N : ℕ, w ^ N * c = 0 := by
  have h' := congrArg val h
  rw [mkX_val, val_zero, Localization.mk_eq_mk'] at h'
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h'
  refine ⟨N, ?_⟩
  dsimp only at hN
  rw [C.xElt_pow hw N, of_mul_of'] at hN
  have := DirectSum.of_injective (β := fun k => C.grade k) (N + n)
    (hN.trans (map_zero (DirectSum.of (fun k => C.grade k) (N + n))).symm)
  exact congrArg Subtype.val this

end CompatibleCharts

end Fractions

/-! ### The structure maps over `lim Rₙ` -/

section Base

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {X : ℕ → Scheme.{u}} {π : ∀ n, X n ⟶ Spec (.of (R n))} {ι : ∀ n, X n ⟶ X (n + 1)}

namespace CompatibleCharts

variable (C : CompatibleCharts ι)
  (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))

/-- The constant `r ∈ lim Rₙ` in degree zero of `S`. -/
def ofκ (r : limit f) : C.ring :=
  DirectSum.of (fun k => C.grade k) 0 ⟨C.κ π r, C.κ_mem hpb r⟩

/-- The constant `r ∈ lim Rₙ` lies in degree zero of `S`. -/
theorem ofκ_mem (r : limit f) : C.ofκ hpb r ∈ C.𝒜 0 := Stacks.ExternalGrading.of_mem_summand _ _

/-- The constant `1 ∈ lim Rₙ` is the unit of `S`. -/
theorem ofκ_one : C.ofκ hpb 1 = 1 := by
  rw [DirectSum.one_def (A := fun k => C.grade k)]
  exact C.of_eq_of rfl _ _ (map_one (C.κ π))

/-- The constants `lim Rₙ → S` are multiplicative. -/
theorem ofκ_mul (r r' : limit f) : C.ofκ hpb (r * r') = C.ofκ hpb r * C.ofκ hpb r' := by
  rw [ofκ, ofκ, ofκ, of_mul_of']
  exact C.of_eq_of rfl _ _ (map_mul (C.κ π) r r')

/-- The constants `lim Rₙ → S` are additive. -/
theorem ofκ_add (r r' : limit f) : C.ofκ hpb (r + r') = C.ofκ hpb r + C.ofκ hpb r' := by
  rw [ofκ, ofκ, ofκ, ← map_add]
  exact C.of_eq_of rfl _ _ (map_add (C.κ π) r r')

/-- The constant `0 ∈ lim Rₙ` is zero in `S`. -/
theorem ofκ_zero : C.ofκ hpb 0 = 0 := by
  rw [ofκ, ← map_zero (DirectSum.of (fun k => C.grade k) 0)]
  exact C.of_eq_of rfl _ _ (map_zero (C.κ π))

/-- **`lim Rₙ → S_(x)`**, the constants. -/
def awayAlg (x : C.ring) : limit f →+* Away C.𝒜 x where
  toFun r := HomogeneousLocalization.mk
    ⟨0, ⟨C.ofκ hpb r, C.ofκ_mem hpb r⟩, ⟨1, SetLike.one_mem_graded C.𝒜⟩,
      (Submonoid.powers x).one_mem⟩
  map_one' := by
    ext
    simp only [val_mk, val_one, C.ofκ_one]
    exact Localization.mk_one
  map_mul' r r' := by
    ext
    simp only [val_mk, val_mul, Localization.mk_mul, C.ofκ_mul]
    congr 1
    exact Subtype.ext (mul_one _).symm
  map_zero' := by
    ext
    simp only [val_mk, val_zero, C.ofκ_zero, Localization.mk_zero]
  map_add' r r' := by
    ext
    simp only [val_mk, val_add, Localization.add_mk_self, C.ofκ_add]

/-- The constant `r ∈ lim Rₙ` in `S_(x)` is the fraction `r / 1`. -/
theorem awayAlg_val (x : C.ring) (r : limit f) :
    (C.awayAlg hpb x r).val = Localization.mk (C.ofκ hpb r) 1 := rfl

variable {w : C.Amb} (hw : w ∈ C.grade 1)

/-- Multiplying `c / x^n` by a constant `r ∈ lim Rₙ` multiplies its numerator by the image of
`r`. -/
theorem awayAlg_mul_mkX (r : limit f) (n : ℕ) (c : C.Amb) (hc : c ∈ C.grade n) :
    C.awayAlg hpb (C.xElt hw) r * C.mkX hw n c hc =
      C.mkX hw n (C.κ π r * c) (κ_mul_mem hpb r hc) := by
  ext
  rw [val_mul, awayAlg_val, mkX_val, mkX_val, Localization.mk_mul, ofκ, of_mul_of',
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [C.of_eq_of (zero_add n) _ ⟨C.κ π r * c, κ_mul_mem hpb r hc⟩ rfl]

/-- **`S_(x)` is flat over `lim Rₙ`**, by the equational criterion: a relation among fractions
`cᵢ / xⁿ` becomes, after clearing denominators, a relation in one graded piece, where it is
trivial. -/
theorem flat_away (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) :
    letI := (C.awayAlg hpb (C.xElt hw)).toAlgebra
    Module.Flat (limit f) (Away C.𝒜 (C.xElt hw)) := by
  classical
  let := (C.awayAlg hpb (C.xElt hw)).toAlgebra
  refine Module.Flat.of_forall_isTrivialRelation fun {l} {r} {z} hrel => ?_
  choose n c hc hn hz using fun i => C.exists_mkX_eq hw (z i)
  set K := 1 + ∑ i, n i with hKdef
  have hK : ∀ i, n i ≤ K := fun i => by
    have := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hc' : ∀ i, w ^ (K - n i) * c i ∈ C.grade K := fun i => by
    have := SetLike.mul_mem_graded (C.pow_mem_grade hw (K - n i)) (hc i)
    rwa [Nat.sub_add_cancel (hK i)] at this
  have hz' : ∀ i, z i = C.mkX hw K (w ^ (K - n i) * c i) (hc' i) := fun i => by
    rw [← hz i, C.mkX_bump hw (K - n i)]
    exact C.mkX_congr hw (Nat.sub_add_cancel (hK i)) rfl _ _
  have hsum : C.mkX hw K (∑ i, C.κ π (r i) * (w ^ (K - n i) * c i))
      (sum_κ_mul_mem hpb r hc') = 0 := by
    rw [← hrel, ← C.mkX_sum hw Finset.univ K _ (fun i => κ_mul_mem hpb (r i) (hc' i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz' i, Algebra.smul_def, RingHom.algebraMap_toAlgebra, C.awayAlg_mul_mkX hpb hw]
  obtain ⟨N, hN⟩ := C.mkX_eq_zero hw hsum
  have hmem : ∀ i, w ^ N * (w ^ (K - n i) * c i) ∈ C.grade (N + K) := fun i =>
    SetLike.mul_mem_graded (C.pow_mem_grade hw N) (hc' i)
  obtain ⟨m, a, y, hy, hdec, hra⟩ := (hPS (N + K) (by omega)).rel l r _ hmem (by
    rw [← hN, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _)
  refine ⟨m, a, fun j => C.mkX hw (N + K) (y j) (hy j), fun i => ?_, hra⟩
  rw [hz' i, C.mkX_bump hw N, C.mkX_congr hw rfl (hdec i) _ (sum_κ_mul_mem hpb (a i) hy),
    ← C.mkX_sum hw Finset.univ (N + K) _ (fun j => κ_mul_mem hpb (a i j) (hy j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, C.awayAlg_mul_mkX hpb hw]

end CompatibleCharts

end Base

/-! ### Evaluation on the charts -/

section Evaluation

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {X : ℕ → Scheme.{u}} {π : ∀ n, X n ⟶ Spec (.of (R n))} {ι : ∀ n, X n ⟶ X (n + 1)}

namespace CompatibleCharts

variable (C : CompatibleCharts ι)
  (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))

/-- Evaluation at level `n` sends `c / s^k` to the `U`-coordinate of `c` at level `n`. -/
theorem evalU_mkX (n k : ℕ) (c : C.Amb) (hc : c ∈ C.grade k) :
    C.evalU n (C.mkX C.sAmb_mem k c hc) = (c n).1 := by
  rw [mkX, evalU_mk, evalAt_of]

/-- Evaluation at level `n` sends `c / t^k` to the `V`-coordinate of `c` at level `n`. -/
theorem evalV_mkX (n k : ℕ) (c : C.Amb) (hc : c ∈ C.grade k) :
    C.evalV n (C.mkX C.tAmb_mem k c hc) = (c n).2 := by
  rw [mkX, evalV_mk, evalAt_of]

/-- Evaluation at level `n` sends the constant `r ∈ lim Rₙ` to its image at level `n`. -/
theorem evalAt_ofκ (n : ℕ) (r : limit f) :
    C.evalAt n (C.ofκ hpb r) = C.κ π r n := C.evalAt_of n 0 _

/-- Evaluation `S_(s) → Γ(Xₙ, Uₙ)` sends the constant `r ∈ lim Rₙ` to the image of its
`n`-th component under the structure map `Rₙ → Γ(Xₙ, Uₙ)`. -/
theorem evalU_awayAlg (n : ℕ) (r : limit f) :
    C.evalU n (C.awayAlg hpb C.sElt r) =
      TwoChartDatum.baseOfSpecOn (π n) (C.D n).U (towerLimitProj f n r) := by
  simp only [evalU, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, awayAlg_val,
    lift_mk_one, evalAt_ofκ, κ_apply]
  rfl

/-- Evaluation `S_(t) → Γ(Xₙ, Vₙ)` sends the constant `r ∈ lim Rₙ` to the image of its
`n`-th component under the structure map `Rₙ → Γ(Xₙ, Vₙ)`. -/
theorem evalV_awayAlg (n : ℕ) (r : limit f) :
    C.evalV n (C.awayAlg hpb C.tElt r) =
      TwoChartDatum.baseOfSpecOn (π n) (C.D n).V (towerLimitProj f n r) := by
  simp only [evalV, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, awayAlg_val,
    lift_mk_one, evalAt_ofκ, κ_apply]
  rfl

/-- **The evaluation `S_(s) → Γ(Xₙ, Uₙ)` is surjective.** -/
theorem evalU_surjective (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) (n : ℕ) :
    Function.Surjective (C.evalU n) := by
  intro x
  obtain ⟨k, hk, y, hxy⟩ := exists_cechDiff_eq_zero_fst (C.D n) x
  obtain ⟨c, hc, hcn⟩ := (hPS k hk).surj n (x, y) hxy
  exact ⟨C.mkX C.sAmb_mem k c hc, by rw [evalU_mkX, hcn]⟩

/-- **The evaluation `S_(t) → Γ(Xₙ, Vₙ)` is surjective.** -/
theorem evalV_surjective (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) (n : ℕ) :
    Function.Surjective (C.evalV n) := by
  intro y
  obtain ⟨k, hk, x, hxy⟩ := exists_cechDiff_eq_zero_snd (C.D n) y
  obtain ⟨c, hc, hcn⟩ := (hPS k hk).surj n (x, y) hxy
  exact ⟨C.mkX C.tAmb_mem k c hc, by rw [evalV_mkX, hcn]⟩

/-- A fraction whose numerator is a combination, with coefficients vanishing at level `n`, lies in
`Ker(lim R → Rₙ) · S_(x)`. -/
theorem mkX_mem_map_ker {w : C.Amb} (hw : w ∈ C.grade 1) (n k m : ℕ) (r : Fin m → limit f)
    (c : Fin m → C.Amb) (hc : ∀ i, c i ∈ C.grade k) (hr : ∀ i, (r i).1 n = 0) :
    C.mkX hw k (∑ i, C.κ π (r i) * c i) (sum_κ_mul_mem hpb r hc) ∈
      (RingHom.ker (towerLimitProj f n)).map (C.awayAlg hpb (C.xElt hw)) := by
  rw [← C.mkX_sum hw Finset.univ k _ (fun i => κ_mul_mem hpb (r i) (hc i))]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← C.awayAlg_mul_mkX hpb hw (r i) k (c i) (hc i)]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr (hr i)))

/-- A fraction `c / x^k` with `x^N * c` vanishing at level `n` lies in
`Ker(lim R → Rₙ) · S_(x)`. -/
private theorem mkX_mem_map_ker_of_pow_mul_apply_eq_zero
    (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) {w : C.Amb} (hw : w ∈ C.grade 1)
    {n k N : ℕ} (hk : 1 ≤ k) {c : C.Amb} (hc : c ∈ C.grade k) (hcn : (w ^ N * c) n = 0) :
    C.mkX hw k c hc ∈ (RingHom.ker (towerLimitProj f n)).map (C.awayAlg hpb (C.xElt hw)) := by
  have hmem := SetLike.mul_mem_graded (C.pow_mem_grade hw N) hc
  obtain ⟨m, r, c', hc', hr, hdec⟩ := (hPS (N + k) (by omega)).ker _ hmem n hcn
  rw [C.mkX_bump hw N, C.mkX_congr hw rfl hdec _ (sum_κ_mul_mem hpb r hc')]
  exact C.mkX_mem_map_ker hpb hw n (N + k) m r c' hc' hr

/-- **The kernel of `S_(s) → Γ(Xₙ, Uₙ)` is `Ker(lim R → Rₙ) · S_(s)`.** -/
theorem ker_evalU (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) (n : ℕ) :
    RingHom.ker (C.evalU n) = (RingHom.ker (towerLimitProj f n)).map (C.awayAlg hpb C.sElt) := by
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨k, c, hc, hk, rfl⟩ := C.exists_mkX_eq C.sAmb_mem z
    rw [RingHom.mem_ker, evalU_mkX] at hz
    have hcech := (cechDiff_eq_zero_iff (C.D n) k (c n)).mp ((C.mem_grade.mp hc).2 n)
    rw [hz, map_zero] at hcech
    have h2 : (C.D n).resV (c n).2 = 0 :=
      ((isUnit_resU_b (C.D n)).pow k).mul_right_eq_zero.mp hcech.symm
    obtain ⟨N, hN⟩ := exists_pow_a_mul_eq_zero (C.D n) h2
    have hcn : (C.sAmb ^ N * c) n = 0 := by
      rw [Amb.mul_apply, Amb.pow_apply]
      refine Prod.ext ?_ ?_
      · simp [sAmb, hz]
      · simp [sAmb, hN]
    exact C.mkX_mem_map_ker_of_pow_mul_apply_eq_zero hpb hPS C.sAmb_mem hk hc hcn
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, evalU_awayAlg, RingHom.mem_ker.mp hr, map_zero]

/-- **The kernel of `S_(t) → Γ(Xₙ, Vₙ)` is `Ker(lim R → Rₙ) · S_(t)`.** -/
theorem ker_evalV (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) (n : ℕ) :
    RingHom.ker (C.evalV n) = (RingHom.ker (towerLimitProj f n)).map (C.awayAlg hpb C.tElt) := by
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨k, c, hc, hk, rfl⟩ := C.exists_mkX_eq C.tAmb_mem z
    rw [RingHom.mem_ker, evalV_mkX] at hz
    have hcech := (cechDiff_eq_zero_iff (C.D n) k (c n)).mp ((C.mem_grade.mp hc).2 n)
    rw [hz, map_zero, mul_zero] at hcech
    obtain ⟨N, hN⟩ := exists_pow_b_mul_eq_zero (C.D n) hcech
    have hcn : (C.tAmb ^ N * c) n = 0 := by
      rw [Amb.mul_apply, Amb.pow_apply]
      refine Prod.ext ?_ ?_
      · simp [tAmb, hN]
      · simp [tAmb, hz]
    exact C.mkX_mem_map_ker_of_pow_mul_apply_eq_zero hpb hPS C.tAmb_mem hk hc hcn
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, evalV_awayAlg, RingHom.mem_ker.mp hr, map_zero]

/-! ### Compatibilities -/

/-- Evaluation on `U` is compatible with the transition maps `Γ(Xₙ₊₁, Uₙ₊₁) → Γ(Xₙ, Uₙ)`. -/
theorem ρU_evalU (n : ℕ) (z : Away C.𝒜 C.sElt) :
    C.ρU n (C.evalU (n + 1) z) = C.evalU n z := by
  obtain ⟨k, c, hc, -, rfl⟩ := C.exists_mkX_eq C.sAmb_mem z
  rw [evalU_mkX, evalU_mkX, ((C.mem_grade.mp hc).1 n).1]

/-- Evaluation on `V` is compatible with the transition maps `Γ(Xₙ₊₁, Vₙ₊₁) → Γ(Xₙ, Vₙ)`. -/
theorem ρV_evalV (n : ℕ) (z : Away C.𝒜 C.tElt) :
    C.ρV n (C.evalV (n + 1) z) = C.evalV n z := by
  obtain ⟨k, c, hc, -, rfl⟩ := C.exists_mkX_eq C.tAmb_mem z
  rw [evalV_mkX, evalV_mkX, ((C.mem_grade.mp hc).1 n).2]

/-- Evaluation on `U ∩ V` of `a / (st)^k`, multiplied by `b^k`, is the restriction to `U ∩ V`
of the `U`-coordinate of `a` at level `n`. -/
theorem evalUV_mk_mul (n k : ℕ) (a : C.ring) (ha : a ∈ C.𝒜 (k • (1 + 1))) :
    C.evalUV n (Away.mk C.𝒜 (SetLike.mul_mem_graded C.sElt_mem C.tElt_mem) k a ha) *
      (C.D n).resU (C.D n).b ^ k = (C.D n).resU (C.evalAt n a).1 := by
  have h := lift_mk_mul (C.sElt * C.tElt)
    ((C.D n).resU.comp ((RingHom.fst _ _).comp (C.evalAt n)))
    (by simpa [C.evalAt_sElt, C.evalAt_tElt] using isUnit_resU_b (C.D n)) a k
  simpa [evalUV, C.evalAt_sElt, C.evalAt_tElt] using h

/-- The localization `S_(s) → S_(st)`. -/
abbrev awayMapS : Away C.𝒜 C.sElt →+* Away C.𝒜 (C.sElt * C.tElt) :=
  awayMap C.𝒜 C.tElt_mem rfl

/-- The localization `S_(t) → S_(st)`. -/
abbrev awayMapT : Away C.𝒜 C.tElt →+* Away C.𝒜 (C.sElt * C.tElt) :=
  awayMap C.𝒜 C.sElt_mem (mul_comm C.sElt C.tElt)

/-- Evaluation on `U ∩ V` of the image of `z ∈ S_(s)` in `S_(st)` is the restriction of its
evaluation on `U`. -/
theorem evalUV_awayMapS (n : ℕ) (z : Away C.𝒜 C.sElt) :
    C.evalUV n (C.awayMapS z) = (C.D n).resU (C.evalU n z) := by
  obtain ⟨k, c, hc, -, rfl⟩ := C.exists_mkX_eq C.sAmb_mem z
  rw [evalU_mkX, mkX, awayMap_mk]
  have h := C.evalUV_mk_mul n k (DirectSum.of (fun k => C.grade k) k ⟨c, hc⟩ * C.tElt ^ k) (by
    rw [smul_add]
    exact SetLike.mul_mem_graded (C.of_mem_𝒜_smul hc) (SetLike.pow_mem_graded k C.tElt_mem))
  rw [map_mul, map_pow, evalAt_of, C.evalAt_tElt, Prod.fst_mul, Prod.pow_fst, map_mul,
    map_pow] at h
  exact ((isUnit_resU_b (C.D n)).pow k).mul_left_inj.mp h

/-- Evaluation on `U ∩ V` of the image of `z ∈ S_(t)` in `S_(st)` is the restriction of its
evaluation on `V`. -/
theorem evalUV_awayMapT (n : ℕ) (z : Away C.𝒜 C.tElt) :
    C.evalUV n (C.awayMapT z) = (C.D n).resV (C.evalV n z) := by
  obtain ⟨k, c, hc, -, rfl⟩ := C.exists_mkX_eq C.tAmb_mem z
  rw [evalV_mkX, mkX, awayMap_mk]
  have h := C.evalUV_mk_mul n k (DirectSum.of (fun k => C.grade k) k ⟨c, hc⟩ * C.sElt ^ k) (by
    rw [smul_add]
    exact SetLike.mul_mem_graded (C.of_mem_𝒜_smul hc) (SetLike.pow_mem_graded k C.sElt_mem))
  rw [map_mul, map_pow, evalAt_of, C.evalAt_sElt, Prod.fst_mul, Prod.pow_fst, one_pow, mul_one,
    (cechDiff_eq_zero_iff (C.D n) k (c n)).mp ((C.mem_grade.mp hc).2 n), mul_comm] at h
  exact ((isUnit_resU_b (C.D n)).pow k).mul_right_inj.mp h

/-- The element `t / s` of `S_(s)` evaluates to `b` on `Uₙ`. -/
theorem evalU_isLocalizationElem (n : ℕ) :
    C.evalU n (Away.isLocalizationElem C.sElt_mem C.tElt_mem) = (C.D n).b := by
  rw [Away.isLocalizationElem, evalU_mk, pow_one, C.evalAt_tElt]

/-- The element `s / t` of `S_(t)` evaluates to `a` on `Vₙ`. -/
theorem evalV_isLocalizationElem (n : ℕ) :
    C.evalV n (Away.isLocalizationElem C.tElt_mem C.sElt_mem) = (C.D n).a := by
  rw [Away.isLocalizationElem, evalV_mk, pow_one, C.evalAt_sElt]

/-- The constants `lim Rₙ → S_(x)` factor through the degree-zero part of `S`. -/
theorem awayAlg_eq_fromZeroRingHom (x : C.ring) (r : limit f) :
    C.awayAlg hpb x r = fromZeroRingHom C.𝒜 _ ⟨C.ofκ hpb r, C.ofκ_mem hpb r⟩ := rfl

/-- The localization `S_(s) → S_(st)` is compatible with the constants from `lim Rₙ`. -/
theorem awayMapS_awayAlg (r : limit f) :
    C.awayMapS (C.awayAlg hpb C.sElt r) = C.awayAlg hpb (C.sElt * C.tElt) r := by
  rw [awayAlg_eq_fromZeroRingHom, awayAlg_eq_fromZeroRingHom, awayMap_fromZeroRingHom]

/-- The localization `S_(t) → S_(st)` is compatible with the constants from `lim Rₙ`. -/
theorem awayMapT_awayAlg (r : limit f) :
    C.awayMapT (C.awayAlg hpb C.tElt r) = C.awayAlg hpb (C.sElt * C.tElt) r := by
  rw [awayAlg_eq_fromZeroRingHom, awayAlg_eq_fromZeroRingHom, awayMap_fromZeroRingHom]

end CompatibleCharts

end Evaluation

end AlgebraicGeometry.C1590Private.TwoChartTower

end
