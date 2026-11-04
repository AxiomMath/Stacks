module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The limit of a tower of finite `ℤ/ℓⁿ⁺¹`-modules looking free

Let `H : ℕᵒᵖ ⥤ ModuleCat ℤ_ℓ` be a tower whose level `n` is killed by `ℓⁿ⁺¹`, with surjective
transitions whose kernels are `ℓⁿ⁺¹ H(n+1)`, finite levels, and such that elements of
`H(n+k+1)` killed by `ℓᵏ⁺¹` are divisible by `ℓⁿ⁺¹` (the levels look like `(ℤ/ℓⁿ⁺¹)^r`).
This is the shape of `n ↦ H¹(X_k̄, ℤ/ℓⁿ⁺¹)` for a smooth proper curve. Then the limit
`M = lim H(n)` is a free `ℤ_ℓ`-module of finite rank, every projection `M → H(n)` is surjective,
and its kernel is `ℓⁿ⁺¹ M`.

## Main results

* `Stacks.EtaleCohomology.TowerLimit.surjective_π`: the projections `M → H(n)` are onto.
* `Stacks.EtaleCohomology.TowerLimit.exists_eq_smul_of_π_eq_zero`: their kernels are `ℓⁿ⁺¹ M`.
* `Stacks.EtaleCohomology.TowerLimit.isTorsionFree`: the limit is torsion-free.
* `Stacks.EtaleCohomology.TowerLimit.finite`: the limit is a finite `ℤ_ℓ`-module.
* `Stacks.EtaleCohomology.TowerLimit.free`: the limit is a free `ℤ_ℓ`-module of finite rank.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v

namespace Stacks.EtaleCohomology.TowerLimit

variable {p : ℕ} [Fact p.Prime] (F : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[p])

/-- The transition `H(m) → H(n)` for `n ≤ m`. -/
abbrev tr {n m : ℕ} (h : n ≤ m) : F.obj (op m) →ₗ[ℤ_[p]] F.obj (op n) :=
  (F.map (homOfLE h).op).hom

/-- The transitions compose: `H(c) → H(b) → H(a)` is `H(c) → H(a)`. -/
theorem tr_tr {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x : F.obj (op c)) :
    tr F hab (tr F hbc x) = tr F (hab.trans hbc) x := by
  rw [tr, tr, tr, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp]
  rfl

/-- The transition `H(n) → H(n)` is the identity. -/
theorem tr_refl (n : ℕ) (x : F.obj (op n)) : tr F (le_refl n) x = x := by
  rw [tr, show (homOfLE (le_refl n)).op = 𝟙 (op n) from rfl, F.map_id]
  rfl

/-- The projections of the limit are compatible with the transitions. -/
theorem π_tr [HasLimit F] {n m : ℕ} (h : n ≤ m) (x : ↑(limit F)) :
    tr F h ((limit.π F (op m)).hom x) = (limit.π F (op n)).hom x := by
  rw [tr, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, limit.w]

variable {F}

/-- If the successive transitions are surjective, then so are all transitions. -/
theorem surjective_tr (hsurj : ∀ n, Function.Surjective (tr F (Nat.le_succ n))) :
    ∀ {n m : ℕ} (h : n ≤ m), Function.Surjective (tr F h) := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base => exact fun x => ⟨x, tr_refl F n x⟩
  | succ m hnm ih =>
    intro x
    obtain ⟨y, rfl⟩ := ih x
    obtain ⟨z, rfl⟩ := hsurj m y
    exact ⟨z, (tr_tr F hnm m.le_succ z).symm⟩

/-- The map of the underlying type-valued system along `f : i ⟶ j` is the transition. -/
private theorem forget_map_eq_tr {i j : ℕᵒᵖ} (f : i ⟶ j)
    (x : (F ⋙ forget _).obj i) : (F ⋙ forget _).map f x = tr F (leOfHom f.unop) x := by
  induction i using Opposite.rec with | op m => ?_
  induction j using Opposite.rec with | op n => ?_
  rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
  rfl

/-- Two elements of the limit with the same components are equal. -/
theorem limit_ext [HasLimit F] {x y : ↑(limit F)}
    (h : ∀ n, (limit.π F (op n)).hom x = (limit.π F (op n)).hom y) : x = y :=
  Concrete.limit_ext F x y fun j => by
    induction j using Opposite.rec with | op n => exact h n

/-- An element of the limit with prescribed components, from a section of the underlying
system of sets. -/
theorem exists_limit_of_sections [HasLimit F] (s : (F ⋙ forget _).sections) :
    ∃ x : ↑(limit F), ∀ n, (limit.π F (op n)).hom x = s.val (op n) := by
  refine ⟨(preservesLimitIso (forget _) F).inv ((Types.limitEquivSections (F ⋙ forget _)).symm s),
    fun n => ?_⟩
  have h := congrArg (fun g => g ((Types.limitEquivSections (F ⋙ forget _)).symm s))
    (preservesLimitIso_inv_π (forget (ModuleCat.{v} ℤ_[p])) F (op n))
  exact h.trans (Types.limitEquivSections_symm_apply _ s (op n))

/-- An element of the limit from a family compatible with the successive transitions. -/
theorem exists_limit_of_compatible (y : ∀ m, F.obj (op m))
    (hy : ∀ m, tr F (Nat.le_succ m) (y (m + 1)) = y m) :
    ∃ x : ↑(limit F), ∀ m, (limit.π F (op m)).hom x = y m := by
  have hc : ∀ {n m : ℕ} (h : n ≤ m), tr F h (y m) = y n := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => exact tr_refl F n _
    | succ m hnm ih => rw [← tr_tr F hnm (Nat.le_succ m), hy, ih]
  let s : (F ⋙ forget _).sections := ⟨fun j => y j.unop, fun {i j} f => by
    rw [forget_map_eq_tr]
    exact hc _⟩
  exact exists_limit_of_sections s

variable [HasLimit F] (hkill : ∀ n (x : F.obj (op n)), (p : ℤ_[p]) ^ (n + 1) • x = 0)
  (hsurj : ∀ n, Function.Surjective (tr F (Nat.le_succ n)))
  (hker : ∀ n (x : F.obj (op (n + 1))), tr F (Nat.le_succ n) x = 0 →
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y)
  (htors : ∀ n k (x : F.obj (op (n + k + 1))), (p : ℤ_[p]) ^ (k + 1) • x = 0 →
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y)
  (hfin : ∀ n, Finite (F.obj (op n)))

include hsurj hfin in
/-- **The projections of the limit are surjective**, for a tower of finite modules with
surjective transitions. -/
theorem surjective_π (n : ℕ) (y : F.obj (op n)) :
    ∃ x : ↑(limit F), (limit.π F (op n)).hom x = y := by
  have : ∀ j : ℕᵒᵖ, Finite ((F ⋙ forget _).obj j) := fun j => hfin j.unop
  have : ∀ j : ℕᵒᵖ, Nonempty ((F ⋙ forget _).obj j) := fun _ => ⟨0⟩
  obtain ⟨s, hs⟩ := (F ⋙ forget _).eval_section_surjective_of_surjective (fun i j f => by
    simp only [Function.Surjective, forget_map_eq_tr]
    exact surjective_tr hsurj _) (op n) y
  obtain ⟨x, hx⟩ := exists_limit_of_sections s
  exact ⟨x, (hx n).trans hs⟩

omit [HasLimit F] in
include hsurj hker in
/-- The kernel of `H(m) → H(n)` is `ℓⁿ⁺¹ H(m)`. -/
theorem exists_eq_smul_of_tr_eq_zero {n m : ℕ} (h : n ≤ m) (x : F.obj (op m))
    (hx : tr F h x = 0) : ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨0, by rw [← tr_refl F n x, hx, smul_zero]⟩
  | succ m hnm ih =>
    obtain ⟨w, hw⟩ := ih (tr F m.le_succ x) (by rw [tr_tr]; exact hx)
    obtain ⟨w', rfl⟩ := hsurj m w
    obtain ⟨v, hv⟩ := hker m (x - (p : ℤ_[p]) ^ (n + 1) • w')
      (by rw [map_sub, map_smul, hw, sub_self])
    refine ⟨w' + (p : ℤ_[p]) ^ (m - n) • v, ?_⟩
    rw [smul_add, smul_smul, ← pow_add, show n + 1 + (m - n) = m + 1 by omega, ← hv]
    abel

include hkill hsurj hker htors in
/-- **The kernel of `M → H(n)` is `ℓⁿ⁺¹ M`.** -/
theorem exists_eq_smul_of_π_eq_zero (n : ℕ) (x : ↑(limit F)) (hx : (limit.π F (op n)).hom x = 0) :
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y := by
  have hw : ∀ j, ∃ w : F.obj (op (j + n + 1)),
      (limit.π F (op (j + n + 1))).hom x = (p : ℤ_[p]) ^ (n + 1) • w := fun j =>
    exists_eq_smul_of_tr_eq_zero hsurj hker (by omega) _
      (by rw [π_tr]; exact hx)
  choose w hw using hw
  have huniq : ∀ j (a b : F.obj (op (j + n + 1))), (p : ℤ_[p]) ^ (n + 1) • a =
      (p : ℤ_[p]) ^ (n + 1) • b → tr F (by omega : j ≤ j + n + 1) a = tr F (by omega) b := by
    intro j a b hab
    obtain ⟨z, hz⟩ := htors j n (a - b) (by rw [smul_sub, hab, sub_self])
    rw [← sub_eq_zero, ← map_sub, hz, map_smul, hkill]
  have hcomp : ∀ j, tr F (Nat.le_succ j) (tr F (by omega : j + 1 ≤ j + 1 + n + 1) (w (j + 1))) =
      tr F (by omega : j ≤ j + n + 1) (w j) := by
    intro j
    rw [tr_tr, ← tr_tr F (by omega : j ≤ j + n + 1) (by omega : j + n + 1 ≤ j + 1 + n + 1)]
    refine huniq j _ _ ?_
    rw [← map_smul, ← hw, ← hw, π_tr]
  obtain ⟨y, hy⟩ := exists_limit_of_compatible
    (fun j => tr F (by omega : j ≤ j + n + 1) (w j)) hcomp
  refine ⟨y, limit_ext fun j => ?_⟩
  rw [map_smul, hy, ← map_smul, ← hw, π_tr]

include hkill htors in
/-- **The limit is torsion-free.** -/
theorem isTorsionFree : Module.IsTorsionFree ℤ_[p] ↑(limit F) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  refine Or.inr (limit_ext fun n => ?_)
  rw [map_zero]
  obtain ⟨k, u, rfl⟩ : ∃ k : ℕ, ∃ u : ℤ_[p]ˣ, r = u * (p : ℤ_[p]) ^ k :=
    ⟨_, _, PadicInt.unitCoeff_spec hr⟩
  have hk : (p : ℤ_[p]) ^ k • x = 0 := by
    rw [mul_smul] at hrx
    simpa using congrArg (fun z => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • z) hrx
  have hz : (p : ℤ_[p]) ^ (k + 1) • (limit.π F (op (n + k + 1))).hom x = 0 := by
    rw [← map_smul, pow_succ', mul_smul, hk, smul_zero, map_zero]
  obtain ⟨y, hy⟩ := htors n k _ hz
  rw [← π_tr F (by omega : n ≤ n + k + 1), hy, map_smul, hkill]

/-- Two `p`-adic integers congruent modulo `pᴺ⁺¹`, in the sense of the norm, act in the same way
on a module killed by `pᴺ⁺¹`. -/
theorem smul_eq_smul_of_norm_sub_lt {N : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℤ_[p] Y]
    (hY : ∀ y : Y, (p : ℤ_[p]) ^ (N + 1) • y = 0) {a b : ℤ_[p]}
    (hab : ‖a - b‖ < (p : ℝ) ^ (-(N : ℤ))) (y : Y) : a • y = b • y := by
  have h1 : ‖a - b‖ ≤ (p : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
    convert hab using 2
    push_cast
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h1)
  rw [← sub_eq_zero, ← sub_smul, ← hc, mul_smul, hY, smul_zero]

include hkill hsurj hker htors hfin in
/-- **The limit is a finite `ℤ_p`-module**, generated by lifts of the elements of `H(0)`. -/
theorem finite : Module.Finite ℤ_[p] ↑(limit F) := by
  classical
  have := hfin 0
  let : Fintype (F.obj (op 0)) := Fintype.ofFinite _
  choose xg hxg using surjective_π hsurj hfin 0
  let Φ : (F.obj (op 0) → ℤ_[p]) → ↑(limit F) := fun a => ∑ g, a g • xg g
  have hΦadd : ∀ a b, Φ (a + b) = Φ a + Φ b := fun a b => by
    simp only [Φ, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hΦsmul : ∀ (r : ℤ_[p]) a, Φ (r • a) = r • Φ a := fun r a => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hΦsingle : ∀ g, Φ (Pi.single g 1) = xg g := fun g => by
    simp only [Φ, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  refine ⟨⟨Finset.univ.image xg, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  have happrox : ∀ N : ℕ, ∃ a, ∃ y, x - Φ a = (p : ℤ_[p]) ^ N • y := by
    intro N
    induction N with
    | zero => exact ⟨0, x, by simp [Φ]⟩
    | succ N ih =>
      obtain ⟨a, y, hy⟩ := ih
      obtain ⟨y', hy'⟩ := exists_eq_smul_of_π_eq_zero hkill hsurj hker htors 0
        (y - xg ((limit.π F (op 0)).hom y)) (by rw [map_sub, hxg, sub_self])
      refine ⟨a + (p : ℤ_[p]) ^ N • Pi.single ((limit.π F (op 0)).hom y) 1, y', ?_⟩
      rw [hΦadd, hΦsmul, hΦsingle, ← sub_sub, hy, ← smul_sub, hy', smul_smul, ← pow_add]
  let t : ℕ → Set (F.obj (op 0) → ℤ_[p]) := fun N => {a | (limit.π F (op N)).hom (x - Φ a) = 0}
  have hπΦ : ∀ N a, (limit.π F (op N)).hom (Φ a) = ∑ g, a g • (limit.π F (op N)).hom (xg g) :=
    fun N a => by simp only [Φ, map_sum, map_smul]
  have hlc : ∀ N, IsClosed (t N) := by
    intro N
    have : IsLocallyConstant fun a : F.obj (op 0) → ℤ_[p] => (limit.π F (op N)).hom (x - Φ a) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro a
      filter_upwards [Metric.ball_mem_nhds a
        (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _ : (0 : ℝ) < (p : ℝ) ^ (-(N : ℤ)))]
        with b hb
      rw [map_sub, map_sub, hπΦ, hπΦ]
      congr 1
      refine Finset.sum_congr rfl fun g _ => smul_eq_smul_of_norm_sub_lt (hkill N) ?_ _
      have := (dist_le_pi_dist b a g).trans_lt hb
      rwa [dist_eq_norm] at this
    exact (this.isClopen_fiber 0).isClosed
  have hdec : ∀ N, t (N + 1) ⊆ t N := by
    intro N a ha
    simp only [t, Set.mem_setOf_eq] at ha ⊢
    rw [← π_tr F (Nat.le_succ N), ha, map_zero]
  have hne : ∀ N, (t N).Nonempty := by
    intro N
    obtain ⟨a, y, hy⟩ := happrox (N + 1)
    refine ⟨a, ?_⟩
    simp only [t, Set.mem_setOf_eq]
    rw [hy, map_smul, hkill]
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hlc 0).isCompact hlc
  rw [Set.mem_iInter] at ha
  have hxa : x = Φ a := by
    rw [← sub_eq_zero]
    exact limit_ext fun N => by rw [map_zero]; exact ha N
  rw [hxa]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem xg (Finset.mem_univ g))))

include hkill hsurj hker htors hfin in
/-- **The limit is a free `ℤ_p`-module of finite rank.** -/
theorem free : Module.Free ℤ_[p] ↑(limit F) := by
  have := finite hkill hsurj hker htors hfin
  have := isTorsionFree hkill htors
  exact Module.free_of_finite_type_torsion_free'

end Stacks.EtaleCohomology.TowerLimit

end
