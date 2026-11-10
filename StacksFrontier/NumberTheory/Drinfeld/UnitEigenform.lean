module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsStructure
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.UnramifiedTwist
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeData
public import StacksFrontier.NumberTheory.Drinfeld.CommonEigenvector

/-!
# Eigenforms with unit central eigenvalues from nonzero cusp forms

Let `K` be a function field over a finite field `k` of characteristic `p` and `Ω` an
algebraically closed field in which `p` is invertible. We show that as soon as the module `C(Ω)`
of unramified cusp forms with `q_v · U_v f = f` is nonzero, there is an eigenform on `GL₂(A)`
with values in `Ω` all of whose central eigenvalues are `u_v = 1`.

The steps are:
1. The Hecke sum at `v` of a left `GL₂(O)`-invariant function does not depend on the data
   (uniformizer, residue system) of the source's formula: the `q_v + 1` cosets `GL₂(O) gⱼ` are
   the same for any two choices.
2. Hecke operators at distinct places commute, their matrices being supported at different
   places.
3. `C(Ω)` is finite-dimensional (Stacks 03VW) and stable under the `T_v`, so the `T_v` have a
   common eigenvector `f ≠ 0`. It is an eigenform with `u_v = q_v⁻¹`.
4. Twisting by the character `D ↦ c^{deg D}` of the divisor class group, with `c² = q⁻¹`,
   changes `u_v` into `c^{-2 deg v} q_v⁻¹ = 1`.

## Main results

* `Stacks.Drinfeld.heckeOperator_eq_of_isHeckeDataAt` — independence of the data.
* `Stacks.Drinfeld.heckeOperator_comm` — commutation at distinct places.
* `Stacks.Drinfeld.isCuspFormCentralChar_of_mem_cuspFormsCentralChar` — every element of
  `C(Λ)` is an unramified cusp form with `q_v · U_v f = f`, when `p` is invertible in `Λ`.
* `Stacks.Drinfeld.exists_isEigenform_of_cuspFormsCentralChar_ne_bot` — an eigenform with
  `u_v = q_v⁻¹` in `C(Ω)`.
* `Stacks.Drinfeld.exists_isEigenform_one_of_cuspFormsCentralChar_ne_bot` — an eigenform with
  `u_v = 1`.
-/

@[expose] public noncomputable section

open Matrix Module Stacks.Adeles Stacks.Adeles.GlobalFunctionField

universe u w

namespace Stacks.Drinfeld

section Local

variable {K : Type u} [Field K] {v : Place K}

/-- An element of the ideal `(π')` divided by another generator `π` of the same ideal is
integral. -/
theorem mul_inv_mem_integers_of_isUniformizer {π π' : v.integers} (hπ : Place.IsUniformizer v π)
    (hπ' : Place.IsUniformizer v π') (hπ0 : (π : v.completion) ≠ 0) {z : v.integers}
    (hz : z ∈ Ideal.span {π'}) : (z : v.completion) * (π : v.completion)⁻¹ ∈ v.integers :=
  div_mem_integers_of_mem_span (by rwa [hπ, ← hπ']) hπ0

/-- For two choices of data of the Hecke operator at `v`, every local matrix `M'_{j'}` of the
second is `M'_{j'} = u M_j` for a local matrix `M_j` of the first and an integral matrix `u`. -/
theorem exists_isIntMat_heckeLocal_mul_inv {π π' : v.integers} {q q' : ℕ}
    {lam : Fin q → v.integers} {lam' : Fin q' → v.integers} (hπ : Place.IsUniformizer v π)
    (hπ' : Place.IsUniformizer v π') (hπ0' : (π' : v.completion) ≠ 0)
    (hlam : Place.IsResidueSystem v π lam) (j' : Option (Fin q')) :
    ∃ j : Option (Fin q),
      IsIntMat v (heckeLocal v (π' : v.completion) (fun i => (lam' i : v.completion)) j' *
        heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) j) := by
  have hππ : (π : v.completion) * (π' : v.completion)⁻¹ ∈ v.integers :=
    mul_inv_mem_integers_of_isUniformizer hπ' hπ hπ0' (Ideal.subset_span rfl)
  cases j' with
  | none =>
    refine ⟨none, ?_⟩
    have e : heckeLocal v (π' : v.completion) (fun i => (lam' i : v.completion)) none *
        heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) none =
        !![(π : v.completion) * (π' : v.completion)⁻¹, 0; 0, 1] := by
      simp only [heckeLocal, heckeLocalInv]
      rw [mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [_root_.mul_comm]
    rw [e]
    exact isIntMat_of hππ (zero_mem _) (zero_mem _) (one_mem _)
  | some l =>
    obtain ⟨m, hm, -⟩ := hlam (lam' l)
    refine ⟨some m, ?_⟩
    have e : heckeLocal v (π' : v.completion) (fun i => (lam' i : v.completion)) (some l) *
        heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) (some m) =
        !![1, 0; -(((lam' l - lam m : v.integers) : v.completion) * (π' : v.completion)⁻¹),
          (π : v.completion) * (π' : v.completion)⁻¹] := by
      simp only [heckeLocal, heckeLocalInv]
      rw [mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    rw [e]
    exact isIntMat_of (one_mem _) (zero_mem _)
      (neg_mem (mul_inv_mem_integers_of_isUniformizer hπ' hπ hπ0' hm)) hππ

end Local

section Global

variable {K : Type u} [Field K]

/-- Two adelic matrices which are the identity away from `v`, resp. away from `w ≠ v`,
commute. -/
theorem mul_comm_of_localMat_eq_one {v w : Place K} (hvw : v ≠ w) {x y : GL (Fin 2) (AdeleRing K)}
    (hx : ∀ w', w' ≠ v → localMat K w' x = 1) (hy : ∀ w', w' ≠ w → localMat K w' y = 1) :
    x * y = y * x := by
  refine localMat_ext fun w' => ?_
  rw [localMat_mul, localMat_mul]
  by_cases h : w' = v
  · subst h
    rw [hy w' hvw, Matrix.mul_one, Matrix.one_mul]
  · rw [hx w' h, Matrix.mul_one, Matrix.one_mul]

variable {v w : Place K} {q q' : ℕ} {π π' : v.integers} {lam : Fin q → v.integers}
  {lam' : Fin q' → v.integers} {g₀ g₀' : GL (Fin 2) (AdeleRing K)}
  {g : Fin q → GL (Fin 2) (AdeleRing K)} {g' : Fin q' → GL (Fin 2) (AdeleRing K)}

/-- **Hecke operators at distinct places commute.** -/
theorem heckeOperator_comm {Λ : Type w} [AddCommMonoid Λ] (hvw : v ≠ w)
    (hd : IsHeckeDataAt v π lam g₀ g) {r : ℕ} {ϖ : w.integers} {μ : Fin r → w.integers}
    {h₀ : GL (Fin 2) (AdeleRing K)} {h : Fin r → GL (Fin 2) (AdeleRing K)}
    (he : IsHeckeDataAt w ϖ μ h₀ h) (f : GL (Fin 2) (AdeleRing K) → Λ) :
    heckeOperator g₀ g (heckeOperator h₀ h f) = heckeOperator h₀ h (heckeOperator g₀ g f) := by
  funext x
  simp only [heckeOperator_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc,
    mul_comm_of_localMat_eq_one hvw (localMat_heckeFamily hd j).2 (localMat_heckeFamily he i).2]

end Global

section WithK

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

variable {v : Place K} {q q' : ℕ} {π π' : v.integers} {lam : Fin q → v.integers}
  {lam' : Fin q' → v.integers} {g₀ g₀' : GL (Fin 2) (AdeleRing K)}
  {g : Fin q → GL (Fin 2) (AdeleRing K)} {g' : Fin q' → GL (Fin 2) (AdeleRing K)}

include k in
/-- **The Hecke operator does not depend on its data.** On a left `GL₂(O)`-invariant function,
the sums of the source's formula for `T_v` built from two choices of uniformizer and residue
system agree. -/
theorem heckeOperator_eq_of_isHeckeDataAt {Λ : Type w} [AddCommMonoid Λ]
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : ∀ κ x, f (mapO κ * x) = f x)
    (hd : IsHeckeDataAt v π lam g₀ g) (hd' : IsHeckeDataAt v π' lam' g₀' g') :
    heckeOperator g₀' g' f = heckeOperator g₀ g f := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hd.isUniformizer
  have hπ0' := coe_ne_zero_of_isUniformizer k hd'.isUniformizer
  choose σ hσ using exists_isIntMat_heckeLocal_mul_inv hd.isUniformizer hd'.isUniformizer hπ0'
    hd.isResidueSystem (lam' := lam')
  have hloc : ∀ j' w, IsIntMat w
      (localMat K w (heckeFamily g₀' g' j' * (heckeFamily g₀ g (σ j'))⁻¹)) := by
    intro j' w
    rw [localMat_mul, localMat_inv]
    by_cases hw : w = v
    · subst hw
      rw [(localMat_heckeFamily hd' j').1, (localMat_heckeFamily hd _).1, inv_heckeLocal hπ0]
      exact hσ j'
    · rw [(localMat_heckeFamily hd' j').2 w hw, (localMat_heckeFamily hd _).2 w hw, inv_one,
        Matrix.mul_one]
      intro i j
      rw [Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
  have hdet : ∀ j' w,
      (localMat K w (heckeFamily g₀' g' j' * (heckeFamily g₀ g (σ j'))⁻¹)).det⁻¹ ∈ w.integers := by
    intro j' w
    rw [localMat_mul, localMat_inv, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    by_cases hw : w = v
    · subst hw
      rw [(localMat_heckeFamily hd' j').1, (localMat_heckeFamily hd _).1, det_heckeLocal,
        det_heckeLocal, inv_inv, mul_inv, inv_inv]
      exact mul_inv_mem_integers_of_isUniformizer hd.isUniformizer hd'.isUniformizer hπ0
        (Ideal.subset_span rfl)
    · rw [(localMat_heckeFamily hd' j').2 w hw, (localMat_heckeFamily hd _).2 w hw]
      simp
  have hO : ∀ j', ∃ κ : GL (Fin 2) (integralAdeles K),
      mapO κ = heckeFamily g₀' g' j' * (heckeFamily g₀ g (σ j'))⁻¹ := fun j' =>
    exists_mapO_of_isIntMat _ (hloc j') fun w => by
      rw [localMat_inv]
      exact (hloc j' w).inv (hdet j' w)
  have hinj : Function.Injective σ := by
    intro j₁ j₂ h12
    obtain ⟨κ₁, h₁⟩ := hO j₁
    obtain ⟨κ₂, h₂⟩ := hO j₂
    have : mapO (κ₁ * κ₂⁻¹) = heckeFamily g₀' g' j₁ * (heckeFamily g₀' g' j₂)⁻¹ := by
      rw [map_mul, map_inv, h₁, h₂, h12]; group
    exact eq_of_isIntMat_heckeLocal_mul_inv hd'.isUniformizer hπ0' hd'.isResidueSystem
      (isIntMat_heckeLocal_of_mapO hd' hπ0' this)
  have hq : q' = q :=
    (Place.residueCard_eq_of_isResidueSystem hd'.isUniformizer hd'.isResidueSystem).symm.trans
      (Place.residueCard_eq_of_isResidueSystem hd.isUniformizer hd.isResidueSystem)
  have hbij : Function.Bijective σ :=
    (Fintype.bijective_iff_injective_and_card σ).2 ⟨hinj, by simp [hq]⟩
  funext x
  rw [heckeOperator_eq_sum, heckeOperator_eq_sum]
  refine Eq.trans ?_ (hbij.sum_comp (fun j => f (heckeFamily g₀ g j * x)))
  refine Finset.sum_congr rfl fun j' _ => ?_
  obtain ⟨κ, hκ⟩ := hO j'
  rw [show heckeFamily g₀' g' j' = mapO κ * heckeFamily g₀ g (σ j') by
    rw [hκ, inv_mul_cancel_right], mul_assoc, hf]

include k in
/-- An eigenvalue equation for one choice of the data of `T_v` holds for every choice, on a left
`GL₂(O)`-invariant function. -/
theorem isHeckeEigenvalueAt_of_isHeckeDataAt {Λ : Type w} [CommRing Λ]
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : ∀ κ x, f (mapO κ * x) = f x)
    (hd : IsHeckeDataAt v π lam g₀ g) {t : Λ} (ht : ∀ x, heckeOperator g₀ g f x = t * f x) :
    IsHeckeEigenvalueAt v f t := by
  intro q' π' lam' g₀' g' hd' x
  rw [heckeOperator_eq_of_isHeckeDataAt k hf hd hd', ht]

variable {Λ : Type w} [CommRing Λ]

/-- The four linear conditions on an element of `C(Λ)`. -/
def IsCentralCharLinear (f : GL (Fin 2) (AdeleRing K) → Λ) : Prop :=
  (∀ κ x, f (mapO κ * x) = f x) ∧ (∀ γ x, f (x * mapK γ) = f x) ∧ StarCusp K Λ f ∧
    ∀ (v : Place K) (a : GL (Fin 2) (AdeleRing K)), IsCentralDataAt v a →
      ∀ x, (Place.residueCard v : Λ) * centralOperator a f x = f x

include k in
/-- **Every element of `C(Λ)` is an unramified cusp form with `q_v · U_v f = f`**, when `p` is
invertible in `Λ`: the span of such forms consists of such forms. -/
theorem isCuspFormCentralChar_of_mem_cuspFormsCentralChar (hp : IsUnit (ringChar k : Λ))
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : f ∈ cuspFormsCentralChar K Λ) :
    IsCuspFormCentralChar Λ f := by
  suffices h : IsCentralCharLinear f by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨isUnramifiedCuspForm_of_starCusp k hp h1 h2 h3, h4⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
    exact ⟨fun κ x => hf.1.left_invariant x κ, fun γ x => hf.1.right_invariant x γ,
      GlobalFunctionField.IsUnramifiedCuspForm.starCusp hf.1, hf.2⟩
  | zero =>
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, (starForms K Λ).zero_mem,
      fun _ _ _ _ => by simp [centralOperator]⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    refine ⟨fun κ x => ?_, fun γ x => ?_, (starForms K Λ).add_mem h₁.2.2.1 h₂.2.2.1,
      fun v a ha x => ?_⟩
    · simp only [Pi.add_apply, h₁.1, h₂.1]
    · simp only [Pi.add_apply, h₁.2.1, h₂.2.1]
    · have e₁ := h₁.2.2.2 v a ha x
      have e₂ := h₂.2.2.2 v a ha x
      simp only [centralOperator, Pi.add_apply] at e₁ e₂ ⊢
      rw [mul_add, e₁, e₂]
  | smul c f _ h =>
    refine ⟨fun κ x => ?_, fun γ x => ?_, (starForms K Λ).smul_mem c h.2.2.1,
      fun v a ha x => ?_⟩
    · simp only [Pi.smul_apply, h.1]
    · simp only [Pi.smul_apply, h.2.1]
    · have e := h.2.2.2 v a ha x
      simp only [centralOperator, Pi.smul_apply, smul_eq_mul] at e ⊢
      rw [mul_left_comm, e]

variable {Ω : Type w} [Field Ω] [IsAlgClosed Ω]

include k in
/-- **An eigenform in `C(Ω)`.** If `C(Ω)` is nonzero, with `Ω` algebraically closed and `p`
invertible in `Ω`, then it contains an eigenform, whose central eigenvalues are `u_v = q_v⁻¹`. -/
theorem exists_isEigenform_of_cuspFormsCentralChar_ne_bot (hp : IsUnit (ringChar k : Ω))
    (hC : cuspFormsCentralChar K Ω ≠ ⊥) :
    ∃ (f : GL (Fin 2) (AdeleRing K) → Ω) (t : Place K → Ω),
      IsEigenform f t (fun v => ((Place.residueCard v : Ω))⁻¹) := by
  have : Module.Finite Ω (cuspFormsCentralChar K Ω) :=
    Module.Finite.iff_fg.2 (cuspFormsCentralChar_fg k Ω hp)
  have : Nontrivial (cuspFormsCentralChar K Ω) := Submodule.nontrivial_iff_ne_bot.2 hC
  choose π lam g₀ g hd using fun v : Place K => exists_isHeckeDataAt k v
  let T : Place K → End Ω (cuspFormsCentralChar K Ω) := fun v => cuspFormsHecke k Ω hp (hd v)
  have hT : ∀ v w, Commute (T v) (T w) := by
    intro v w
    by_cases hvw : v = w
    · subst hvw
      exact Commute.refl _
    refine LinearMap.ext fun f => Subtype.ext ?_
    change heckeOperator _ _ (heckeOperator _ _ (f : GL (Fin 2) (AdeleRing K) → Ω)) = _
    exact heckeOperator_comm hvw (hd v) (hd w) _
  obtain ⟨f, hf0, hfe⟩ := exists_common_eigenvector T hT
  choose t ht using hfe
  have hfC := isCuspFormCentralChar_of_mem_cuspFormsCentralChar k hp f.2
  refine ⟨(f : GL (Fin 2) (AdeleRing K) → Ω), t, ⟨hfC.1, ?_, fun v => ?_, fun v a ha x => ?_⟩⟩
  · by_contra hne
    push Not at hne
    exact hf0 (Subtype.ext (funext fun x => not_not.1 fun h => hne x (Ne.isUnit h)))
  · exact isHeckeEigenvalueAt_of_isHeckeDataAt k (fun κ x => hfC.1.left_invariant x κ) (hd v)
      fun x => congrFun (congrArg Subtype.val (ht v)) x
  · rw [← hfC.2 v a ha x, ← mul_assoc, inv_mul_cancel₀ (isUnit_residueCard k hp v).ne_zero,
      one_mul]

include k in
/-- The residue field at a place has cardinality a power of `#k`. -/
theorem exists_resCard_eq_pow (v : Place K) : ∃ d : ℕ, v.resCard = Nat.card k ^ d := by
  classical
  have := finite_residueField k v
  let := Fintype.ofFinite (IsLocalRing.ResidueField v.1)
  let := Fintype.ofFinite k
  let φ : k →+* IsLocalRing.ResidueField v.1 :=
    (IsLocalRing.residue v.1).comp ((algebraMap k K).codRestrict v.1.toSubring
      (algebraMap_mem_place v))
  let : Algebra k (IsLocalRing.ResidueField v.1) := φ.toAlgebra
  have : Module.Finite k (IsLocalRing.ResidueField v.1) := Module.Finite.of_finite
  refine ⟨finrank k (IsLocalRing.ResidueField v.1), ?_⟩
  rw [Place.resCard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := k) (V := IsLocalRing.ResidueField v.1)]

variable (K) in
/-- The residue degree `deg v` of a place, with `q_v = q ^ deg v`. -/
def placeDegree (v : Place K) : ℕ := (exists_resCard_eq_pow k v).choose

/-- The residue field at a place `v` has cardinality `#k ^ deg v`. -/
theorem resCard_eq_pow_placeDegree (v : Place K) :
    v.resCard = Nat.card k ^ placeDegree k K v :=
  (exists_resCard_eq_pow k v).choose_spec

variable (K) in
/-- The degree of a divisor, `deg D = ∑ D(v) deg v`. -/
def divisorDegree : (Place K →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun v => (placeDegree k K v : ℤ)

/-- The norm of a divisor `D` equals `#k ^ deg D`. -/
theorem divNorm_eq_zpow_divisorDegree (D : Place K →₀ ℤ) :
    divNorm K D = (Nat.card k : ℚ) ^ divisorDegree k K D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [divNorm_zero, map_zero, zpow_zero]
  | add D E hD hE => rw [divNorm_add k, map_add, zpow_add₀ (by
      have := Fintype.ofFinite k; exact_mod_cast Nat.card_pos.ne'), hD, hE]
  | single v n =>
    rw [divNorm_single, divisorDegree, Finsupp.linearCombination_single, smul_eq_mul,
      resCard_eq_pow_placeDegree k v, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring

/-- **The degree of a principal divisor is zero.** -/
theorem divisorDegree_principalDivisor {y : K} (hy : y ≠ 0) :
    divisorDegree k K (principalDivisor k K y) = 0 := by
  have h := divNorm_principalDivisor k hy
  rw [divNorm_eq_zpow_divisorDegree k] at h
  have hq : (1 : ℚ) < Nat.card k := by
    have := Fintype.ofFinite k
    exact_mod_cast Finite.one_lt_card
  exact (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne') (h.trans (zpow_zero _).symm)

variable (K) in
/-- The character `D ↦ c ^ deg D` of the divisor group. -/
def degreeCharacter (c : Ωˣ) : Multiplicative (Place K →₀ ℤ) →* Ωˣ :=
  (zpowersHom Ωˣ c).comp (AddMonoidHom.toMultiplicative (divisorDegree k K).toAddMonoidHom)

omit [IsAlgClosed Ω] in
/-- The degree character sends a divisor `D` to `c ^ deg D`. -/
theorem degreeCharacter_apply (c : Ωˣ) (D : Place K →₀ ℤ) :
    degreeCharacter k K c (Multiplicative.ofAdd D) = c ^ divisorDegree k K D := rfl

/-- The degree character is trivial on principal divisors. -/
private theorem degreeCharacter_principalDivisor {Ω' : Type w} [Field Ω'] (c : Ω'ˣ) (κ : K)
    (hκ : κ ≠ 0) :
    degreeCharacter k K c (Multiplicative.ofAdd (principalDivisor k K κ)) = 1 := by
  rw [degreeCharacter_apply, divisorDegree_principalDivisor k hκ, zpow_zero]

/-- The degree character at a prime divisor `v` is `c ^ deg v`. -/
private theorem primeValue_degreeCharacter {Ω' : Type w} [Field Ω'] (c : Ω'ˣ) (v : Place K) :
    ((primeValue (degreeCharacter k K c) v : Ω'ˣ) : Ω') = (c : Ω') ^ placeDegree k K v := by
  rw [primeValue, degreeCharacter_apply, divisorDegree, Finsupp.linearCombination_single,
    smul_eq_mul, one_mul, zpow_natCast, Units.val_pow_eq_pow_val]

include k in
/-- **An eigenform with all central eigenvalues `u_v = 1`.** If `C(Ω)` is nonzero, with `Ω`
algebraically closed and `p` invertible in `Ω`, then there is an eigenform with values in `Ω`
and `U_v f = f` at every place: twist an eigenform of `C(Ω)` by `D ↦ c ^ deg D`, `c² = q⁻¹`. -/
theorem exists_isEigenform_one_of_cuspFormsCentralChar_ne_bot (hp : IsUnit (ringChar k : Ω))
    (hC : cuspFormsCentralChar K Ω ≠ ⊥) :
    ∃ (f : GL (Fin 2) (AdeleRing K) → Ω) (t : Place K → Ω), IsEigenform f t (fun _ => 1) := by
  obtain ⟨f, t, hf⟩ := exists_isEigenform_of_cuspFormsCentralChar_ne_bot k hp hC
  have hq0 : ((Nat.card k : ℕ) : Ω) ≠ 0 := by
    have := Fintype.ofFinite k
    have := ringChar.charP k
    obtain ⟨n, -, hn⟩ := FiniteField.card k (ringChar k)
    rw [Nat.card_eq_fintype_card, hn, Nat.cast_pow]
    exact (hp.pow _).ne_zero
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((Nat.card k : Ω))⁻¹ two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hc
    exact inv_ne_zero hq0 hc.symm
  let χ := degreeCharacter k K (Units.mk0 c hc0)
  have hχ : ∀ κ : K, κ ≠ 0 → χ (Multiplicative.ofAdd (principalDivisor k K κ)) = 1 :=
    degreeCharacter_principalDivisor k _
  have hu : (fun v : Place K => (((primeValue χ v)⁻¹ ^ 2 : Ωˣ) : Ω) *
      ((Place.residueCard v : Ω))⁻¹) = fun _ => 1 := by
    funext v
    have hsq : (c ^ placeDegree k K v) ^ 2 = ((Nat.card k : Ω) ^ placeDegree k K v)⁻¹ := by
      rw [← pow_mul, _root_.mul_comm, pow_mul, hc, inv_pow]
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      primeValue_degreeCharacter, Units.val_mk0, Place.residueCard_eq_resCard,
      resCard_eq_pow_placeDegree k v, Nat.cast_pow, inv_pow, hsq, inv_inv,
      mul_inv_cancel₀ (pow_ne_zero _ hq0)]
  have h := GlobalFunctionField.IsEigenform.unramifiedTwist hχ hf
  rw [hu] at h
  exact ⟨_, _, h⟩

include k in
omit [IsAlgClosed Ω] in
/-- **Twisting a central-invariant cusp form into `C(Ω)`.** Let `f` be left `GL₂(O)`- and right
`GL₂(K)`-invariant, satisfy the cusp condition and `U_v f = f` at every place, with `p`
invertible in `Ω`, and let `c ∈ Ωˣ` with `c² = q = #k`. Then the twist
`x ↦ c^{deg div det x} f(x)` is an unramified cusp form with `q_v · U_v f = f` at every place. -/
theorem isCuspFormCentralChar_unramifiedTwist (hp : IsUnit (ringChar k : Ω)) {c : Ωˣ}
    (hc : (c : Ω) ^ 2 = Nat.card k) {f : GL (Fin 2) (AdeleRing K) → Ω}
    (h1 : ∀ κ x, f (mapO κ * x) = f x) (h2 : ∀ γ x, f (x * mapK γ) = f x)
    (h3 : StarCusp K Ω f) (h4 : ∀ v, IsCentralEigenvalueAt v f 1) :
    IsCuspFormCentralChar Ω (unramifiedTwist k (degreeCharacter k K c) f) := by
  refine ⟨IsUnramifiedCuspForm.unramifiedTwist (degreeCharacter_principalDivisor k c)
    (isUnramifiedCuspForm_of_starCusp k hp h1 h2 h3),
    fun v a ha x => ?_⟩
  obtain ⟨π, hπ, hloc⟩ := ha
  have hv := isDiscrete k v
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  set P := primeValue (degreeCharacter k K c) v
  have h0 : detCharacter k (degreeCharacter k K c) a = P⁻¹ ^ 2 := by
    rw [detCharacter_of_isLocalMatrixAt _ hloc, det_diagonal, Fin.prod_univ_two,
      ordC_inv_mul_inv_of_isUniformizer hv hπ hπ0, map_ofAdd_single_neg_two]
  have hU : f (a * x) = f x := by
    have := h4 v a ⟨π, hπ, hloc⟩ x
    rwa [one_mul] at this
  have hq : (P : Ω) ^ 2 = (Place.residueCard v : Ω) := by
    rw [primeValue_degreeCharacter, pow_right_comm, hc,
      Place.residueCard_eq_resCard, resCard_eq_pow_placeDegree k v, Nat.cast_pow]
  have hP : (P : Ω) ^ 2 * ((P⁻¹ ^ 2 : Ωˣ) : Ω) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one]
  change (Place.residueCard v : Ω) * ((detCharacter k (degreeCharacter k K c) (a * x) : Ω) *
    f (a * x)) = (detCharacter k (degreeCharacter k K c) x : Ω) * f x
  rw [map_mul, h0, Units.val_mul, hU, ← hq]
  linear_combination ((detCharacter k (degreeCharacter k K c) x : Ω) * f x) * hP

end WithK

end Stacks.Drinfeld

end
