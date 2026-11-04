module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.UnramifiedReciprocity.Transfer

/-!
# The transfer of a Frobenius element in a tower `A ⊆ B ⊆ C`

Let a finite group `Γ` act on a ring `C` fixing the image of `A`, let `H ≤ Γ` fix the image of
`B` (in the application `Γ = Gal(M/F)`, `H = Gal(M/K)` for a tower of function fields
`F ⊆ K ⊆ M` with rings `A ⊆ B ⊆ C`), and let `φ : H →* 𝒜` be a homomorphism to a commutative
group which is *Frobenius-compatible* with a family `Frob P ∈ 𝒜` indexed by the primes `P` of
`B`: an element `y ∈ H` acting on `C / Q'` as `x ↦ x ^ (N P) ^ m`, `P = Q' ∩ B`, satisfies
`φ(y) = Frob P ^ m`. (For `φ` the restriction to an abelian extension `L / K` inside `M`,
unramified at `P`, this is the defining property of the Frobenius of `P` in `Gal(L / K)`.)

If `σ ∈ Γ` is an arithmetic Frobenius at a prime `Q` of `C` with finite residue field, the
transfer `V = transfer φ` satisfies `V(σ) = ∏_O Frob(P_O) ^ (#O / f(P_O))`, the product over the
orbits `O` of the decomposition group `D_Q` on `Γ / H`, where `P_O` is the prime of `B` below
`g⁻¹ Q` for `gH ∈ O` and `f(P_O)` its residue degree over `A`
(`Stacks.Adeles.GlobalFunctionField.transfer_eq_prod_orbitRel_frob`). If `τ` lies in the
inertia group of `Q`, `V(τ) = 1`
(`Stacks.Adeles.GlobalFunctionField.transfer_eq_one_of_mem_inertia`).

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.primeBelow` — the prime `g⁻¹ Q ∩ B` of the coset `gH`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.primeBelow_mk`,
  `Stacks.Adeles.GlobalFunctionField.primeBelow_smul`.
* `Stacks.Adeles.GlobalFunctionField.transfer_eq_prod_orbitRel_frob`.
* `Stacks.Adeles.GlobalFunctionField.transfer_eq_one_of_mem_inertia`.
-/

@[expose] public noncomputable section

open MulAction Subgroup Pointwise

namespace Stacks.Adeles.GlobalFunctionField

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [Algebra B C] [IsScalarTower A B C]
  {Γ : Type*} [Group Γ] [MulSemiringAction Γ C] (H : Subgroup Γ) [SMulCommClass H B C]

/-- The prime of `B` below `g⁻¹ Q`, attached to the coset `gH`. -/
public def primeBelow (Q : Ideal C) (x : Γ ⧸ H) : Ideal B := (x.out⁻¹ • Q).under B

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] in
public theorem primeBelow_mk (Q : Ideal C) (g : Γ) :
    primeBelow (B := B) H Q (g : Γ ⧸ H) = (g⁻¹ • Q).under B := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [primeBelow, hh, mul_inv_rev, mul_smul]
  exact Ideal.under_smul B (g⁻¹ • Q) (h⁻¹ : H)

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] in
public theorem primeBelow_smul (Q : Ideal C) {d : Γ} (hd : d ∈ stabilizer Γ Q) (x : Γ ⧸ H) :
    primeBelow (B := B) H Q (d • x) = primeBelow H Q x := by
  induction x using QuotientGroup.induction_on with | H g => ?_
  rw [Quotient.smul_coe, smul_eq_mul, primeBelow_mk, primeBelow_mk, mul_inv_rev, mul_smul,
    inv_smul_eq_iff.2 (mem_stabilizer_iff.1 hd).symm]

variable {𝒜 : Type*} [CommGroup 𝒜] (φ : H →* 𝒜) (Frob : Ideal B → 𝒜)

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] in
/-- An element `y` with `y x ≡ x ^ q` modulo `Q` acts as `x ↦ x ^ q ^ n` through `y ^ n`. -/
theorem pow_smul_sub_pow_mem {Q : Ideal C} {σ : Γ} {q : ℕ} (hσ : ∀ x : C, σ • x - x ^ q ∈ Q)
    (n : ℕ) (x : C) : σ ^ n • x - x ^ q ^ n ∈ Q := by
  rw [← Ideal.Quotient.eq]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, pow_succ, pow_mul]
    have h := Ideal.Quotient.eq.2 (hσ (σ ^ n • x))
    rw [h, map_pow, ih, ← map_pow]

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] in
/-- If `σ x ≡ x ^ q` modulo `Q`, then `g⁻¹ σ ^ n g` acts on `C / g⁻¹ Q` as `x ↦ x ^ q ^ n`. -/
theorem conj_pow_smul_sub_pow_mem {Q : Ideal C} {σ : Γ} {q : ℕ}
    (hσ : ∀ x : C, σ • x - x ^ q ∈ Q) (g : Γ) (n : ℕ) (x : C) :
    (g⁻¹ * σ ^ n * g) • x - x ^ q ^ n ∈ g⁻¹ • Q := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, smul_sub, smul_pow', mul_smul,
    mul_smul, smul_inv_smul]
  exact pow_smul_sub_pow_mem hσ n (g • x)

/-- A prime ideal with finite residue ring is maximal. -/
private theorem isMaximal_of_finite_quotient (p : Ideal A) [p.IsPrime] [Finite (A ⧸ p)] :
    p.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ p))

/-- If `C / Q` is finite, so is `A / (Q ∩ A)`. -/
private theorem finite_quotient_under (Q : Ideal C) [Finite (C ⧸ Q)] : Finite (A ⧸ Q.under A) :=
  Finite.of_injective _ Ideal.algebraMap_quotient_injective

variable [SMulCommClass Γ A C]

omit [SMulCommClass Γ A C] in
/-- **The residue degree divides the exponent of a Frobenius power fixing `B`.** If `y` fixes the
image of `B` and acts on `C / Q'` as `x ↦ x ^ q ^ n`, `q = #(A / Q' ∩ A)`, then the residue degree
`f` of `P = Q' ∩ B` over `A` divides `n`, and `y` acts as `x ↦ x ^ (#(B / P)) ^ (n / f)`. -/
theorem inertiaDeg_dvd_of_smul_sub_pow_mem (Q' : Ideal C) [Q'.IsPrime] [Finite (C ⧸ Q')]
    {y : Γ} (hy : ∀ b : B, y • algebraMap B C b = algebraMap B C b) (n : ℕ)
    (hyQ : ∀ x : C, y • x - x ^ Nat.card (A ⧸ Q'.under A) ^ n ∈ Q') :
    (Q'.under B).inertiaDeg A ∣ n ∧
      ∀ x : C, y • x - x ^ (Nat.card (B ⧸ Q'.under B)) ^ (n / (Q'.under B).inertiaDeg A) ∈ Q' := by
  set P := Q'.under B
  set p := Q'.under A
  have hpP : p = P.under A := by
    rw [Ideal.under_under]
  have : Finite (B ⧸ P) := finite_quotient_under Q'
  have : Finite (A ⧸ p) := finite_quotient_under Q'
  have : P.IsMaximal := isMaximal_of_finite_quotient P
  have : p.IsMaximal := isMaximal_of_finite_quotient p
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  have : P.LiesOver p := ⟨hpP⟩
  let := Fintype.ofFinite (A ⧸ p)
  let := Fintype.ofFinite (B ⧸ P)
  have hf : P.inertiaDeg A = Module.finrank (A ⧸ p) (B ⧸ P) := Ideal.inertiaDeg_eq_of_isMaximal p P
  -- On `B / P`, `z ^ q ^ n = z`.
  have hfix : ∀ z : B ⧸ P, z ^ Fintype.card (A ⧸ p) ^ n = z := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h := hyQ (algebraMap B C b)
    rw [hy, ← map_pow, ← map_sub] at h
    rw [Nat.card_eq_fintype_card] at h
    rw [← map_pow, eq_comm, Ideal.Quotient.eq]
    exact h
  have hpow : FiniteField.frobeniusAlgHom (A ⧸ p) (B ⧸ P) ^ n = 1 := by
    refine AlgHom.ext fun z => ?_
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply]
    exact hfix z
  have hdvd : P.inertiaDeg A ∣ n := by
    rw [hf, ← FiniteField.orderOf_frobeniusAlgHom]
    exact orderOf_dvd_of_pow_eq_one hpow
  refine ⟨hdvd, fun x => ?_⟩
  have hcard : Nat.card (B ⧸ P) ^ (n / P.inertiaDeg A) = Nat.card (A ⧸ p) ^ n := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := A ⧸ p),
      ← hf, ← pow_mul, Nat.mul_div_cancel' hdvd]
  rw [hcard]
  exact hyQ x

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] [SMulCommClass ↥H B C]
  [SMulCommClass Γ A C] in
theorem finite_quotient_smul (Q : Ideal C) [Finite (C ⧸ Q)] (g : Γ) : Finite (C ⧸ g • Q) :=
  Finite.of_equiv _ (Ideal.quotientEquiv (I := Q) (J := g • Q)
    (f := MulSemiringAction.toRingEquiv Γ C g)
    (hIJ := by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv

/-- If `h` carries `b⁻¹ Q` to `a⁻¹ Q`, then `a h b⁻¹` stabilizes `Q`. -/
private theorem mul_mul_inv_mem_stabilizer {Q : Ideal C} {a b h : Γ}
    (hh : h • b⁻¹ • Q = a⁻¹ • Q) : a * h * b⁻¹ ∈ stabilizer Γ Q := by
  rw [mem_stabilizer_iff, mul_smul, mul_smul, hh, smul_inv_smul]

/-- For `h ∈ H`, `a h b⁻¹` carries the coset `bH` to `aH`. -/
private theorem mul_mul_inv_smul_mk {a b h : Γ} (hh : h ∈ H) :
    (a * h * b⁻¹) • (b : Γ ⧸ H) = (a : Γ ⧸ H) := by
  rw [Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right]
  exact QuotientGroup.eq.2 (by simpa using hh)

variable [Finite Γ]

/-- **The transfer of an arithmetic Frobenius element, orbit by orbit.** -/
public theorem transfer_eq_prod_orbitRel_frob (Q : Ideal C) [Q.IsPrime] [Finite (C ⧸ Q)]
    [Fintype (Quotient (orbitRel (stabilizer Γ Q) (Γ ⧸ H)))] {σ : Γ} (hσ : IsArithFrobAt A σ Q)
    (hφ : ∀ (Q' : Ideal C) [Q'.IsPrime] [Finite (C ⧸ Q')] (y : H) (m : ℕ),
      (∀ x : C, y • x - x ^ (Nat.card (B ⧸ Q'.under B)) ^ m ∈ Q') →
        φ y = Frob (Q'.under B) ^ m) :
    MonoidHom.transfer φ σ = ∏ O : Quotient (orbitRel (stabilizer Γ Q) (Γ ⧸ H)),
      Frob (primeBelow H Q O.out) ^
        (Nat.card (orbit (stabilizer Γ Q) O.out) /
          (primeBelow (B := B) H Q O.out).inertiaDeg A) := by
  refine transfer_eq_prod_orbitRel_pow φ (stabilizer Γ Q) hσ.mem_stabilizer
    (fun x => Frob (primeBelow H Q x)) (fun x => (primeBelow (B := B) H Q x).inertiaDeg A)
    (fun d hd x => by rw [primeBelow_smul H Q hd]; exact ⟨rfl, rfl⟩) ?_
  intro g n hgn
  simp only [primeBelow_mk]
  set Q' := g⁻¹ • Q
  have : Finite (C ⧸ Q') := finite_quotient_smul Q g⁻¹
  have hy : ∀ b : B, (g⁻¹ * σ ^ n * g) • algebraMap B C b = algebraMap B C b := fun b =>
    smul_algebraMap (⟨_, hgn⟩ : H) b
  have hQ' : Q'.under A = Q.under A := Ideal.under_smul A Q g⁻¹
  have hyQ : ∀ x : C, (g⁻¹ * σ ^ n * g) • x - x ^ Nat.card (A ⧸ Q'.under A) ^ n ∈ Q' := by
    rw [hQ']
    exact conj_pow_smul_sub_pow_mem hσ g n
  obtain ⟨hdvd, hact⟩ := inertiaDeg_dvd_of_smul_sub_pow_mem Q' hy n hyQ
  exact ⟨hdvd, hφ Q' ⟨_, hgn⟩ _ hact⟩

omit [SMulCommClass (↥H) B C] in
/-- **The transfer kills inertia.** -/
public theorem transfer_eq_one_of_mem_inertia (Q : Ideal C) [Q.IsPrime] {τ : Γ}
    (hτ : τ ∈ Q.inertia Γ)
    (hφ : ∀ (Q' : Ideal C) [Q'.IsPrime] [Finite (C ⧸ Q')] (y : H) (m : ℕ),
      (∀ x : C, y • x - x ^ (Nat.card (B ⧸ Q'.under B)) ^ m ∈ Q') →
        φ y = Frob (Q'.under B) ^ m) [Finite (C ⧸ Q)] :
    MonoidHom.transfer φ τ = 1 := by
  refine transfer_eq_one_of_forall φ fun g n hgn => ?_
  have : Finite (C ⧸ g⁻¹ • Q) := finite_quotient_smul Q g⁻¹
  have h1 : ∀ x : C, τ • x - x ^ 1 ∈ Q := fun x => by
    rw [pow_one]
    exact hτ x
  have := hφ (g⁻¹ • Q) ⟨_, hgn⟩ 0 (fun x => by
    have := conj_pow_smul_sub_pow_mem h1 g n x
    rwa [one_pow, pow_zero, pow_one] at *)
  rwa [pow_zero] at this

section Galois

variable [IsDomain A] [IsDomain B] [IsDomain C] [Module.Finite A C] [Module.Flat A C]
  [Module.Finite B C] [Module.Flat B C] [IsGaloisGroup Γ A C] [IsGaloisGroup H B C]

omit [SMulCommClass Γ A C] [SMulCommClass ↥H B C] [IsDomain A] [IsDomain B] [Module.Finite A C]
  [Module.Flat A C] [Module.Finite B C] [Module.Flat B C] [IsGaloisGroup Γ A C]
  [IsGaloisGroup H B C] in
/-- The residue field of a prime with finite residue ring is perfect. -/
theorem perfectField_residueField_of_finite (p : Ideal A) [p.IsPrime] [Finite (A ⧸ p)] :
    PerfectField p.ResidueField := by
  have := isMaximal_of_finite_quotient p
  have : Finite p.ResidueField := Finite.of_surjective _
    p.bijective_algebraMap_quotient_residueField.surjective
  exact PerfectField.ofFinite

omit [SMulCommClass (↥H) B C] in
/-- **The `D_Q`-orbit of `gH` has `e f` elements**, `e` and `f` the ramification index and the
residue degree over `A` of the prime `g⁻¹ Q ∩ B` of `B`. -/
public theorem natCard_orbit_stabilizer (Q : Ideal C) [Q.IsPrime] [Finite (C ⧸ Q)] (g : Γ) :
    Nat.card (orbit (stabilizer Γ Q) (g : Γ ⧸ H)) =
      ((g⁻¹ • Q).under B).ramificationIdx A * ((g⁻¹ • Q).under B).inertiaDeg A := by
  set Q' := g⁻¹ • Q
  set P := Q'.under B
  have : Finite (C ⧸ Q') := finite_quotient_smul Q g⁻¹
  have : Finite (A ⧸ Q.under A) := finite_quotient_under Q
  have : Finite (B ⧸ P) := finite_quotient_under Q'
  have := perfectField_residueField_of_finite (Q.under A)
  have := perfectField_residueField_of_finite P
  -- `#D_Q = e(Q) f(Q)` and `#Stab_H(Q') = e(Q' | P) f(Q' | P)`.
  have hD : Nat.card (stabilizer Γ Q) = Q.ramificationIdx A * Q.inertiaDeg A := by
    rw [Ideal.card_stabilizer_eq (Q.under A) Q, Ideal.ramificationIdxIn_eq_ramificationIdx _ Q Γ,
      Ideal.inertiaDegIn_eq_inertiaDeg _ Q Γ]
  have hH : Nat.card (stabilizer H Q') = Q'.ramificationIdx B * Q'.inertiaDeg B := by
    have := Ideal.card_stabilizer_eq (G := H) P Q'
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q' H,
      Ideal.inertiaDegIn_eq_inertiaDeg _ Q' H] at this
    exact this
  have he : Q.ramificationIdx A = P.ramificationIdx A * Q'.ramificationIdx B := by
    rw [← Ideal.ramificationIdx_tower P Q', Ideal.ramificationIdx_smul]
  have hf : Q.inertiaDeg A = P.inertiaDeg A * Q'.inertiaDeg B := by
    rw [← Ideal.inertiaDeg_tower P Q', Ideal.inertiaDeg_smul]
  -- The stabilizer of `gH` in `D_Q` is `g Stab_H(Q') g⁻¹`.
  have hstab : Nat.card (stabilizer (stabilizer Γ Q) (g : Γ ⧸ H)) = Nat.card (stabilizer H Q') := by
    refine Nat.card_congr
      { toFun := fun d => ⟨⟨g⁻¹ * d.1.1 * g, ?_⟩, ?_⟩
        invFun := fun h => ⟨⟨g * h.1.1 * g⁻¹, ?_⟩, ?_⟩
        left_inv := fun d => by ext; simp [mul_assoc]
        right_inv := fun h => by ext; simp [mul_assoc] }
    · have h := mem_stabilizer_iff.1 d.2
      rw [Subgroup.smul_def, Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at h
      have := H.inv_mem h
      simpa [mul_assoc] using this
    · rw [mem_stabilizer_iff]
      show (g⁻¹ * d.1.1 * g) • (g⁻¹ • Q) = g⁻¹ • Q
      rw [← mul_smul, mul_assoc, mul_assoc, mul_inv_cancel, mul_one, mul_smul,
        mem_stabilizer_iff.1 d.1.2]
    · exact mul_mul_inv_mem_stabilizer (mem_stabilizer_iff.1 h.2)
    · exact mul_mul_inv_smul_mk H h.1.2
  have horb := (stabilizer (stabilizer Γ Q) (g : Γ ⧸ H)).card_mul_index
  rw [index_stabilizer, ← Nat.card_coe_set_eq, hstab, hH, hD, he, hf] at horb
  have hpos : Q'.ramificationIdx B * Q'.inertiaDeg B ≠ 0 := by
    rw [← hH]
    exact Nat.card_pos.ne'
  have : Q'.ramificationIdx B * Q'.inertiaDeg B *
      Nat.card (orbit (stabilizer Γ Q) (g : Γ ⧸ H)) =
      Q'.ramificationIdx B * Q'.inertiaDeg B * (P.ramificationIdx A * P.inertiaDeg A) := by
    rw [horb]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this

/-- **The transfer of a Frobenius element**: `V(σ) = ∏_{P | p} Frob P ^ e(P | p)`, the product over
the primes `P` of `B` above `p = Q ∩ A`. -/
public theorem transfer_eq_finprod_frob_pow_ramificationIdx [FaithfulSMul B C] (Q : Ideal C)
    [Q.IsPrime] [Finite (C ⧸ Q)] {σ : Γ} (hσ : IsArithFrobAt A σ Q)
    (hφ : ∀ (Q' : Ideal C) [Q'.IsPrime] [Finite (C ⧸ Q')] (y : H) (m : ℕ),
      (∀ x : C, y • x - x ^ (Nat.card (B ⧸ Q'.under B)) ^ m ∈ Q') →
        φ y = Frob (Q'.under B) ^ m) :
    MonoidHom.transfer φ σ =
      ∏ᶠ P ∈ (Q.under A).primesOver B, Frob P ^ P.ramificationIdx A := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  rw [transfer_eq_prod_orbitRel_frob (H := H) (φ := φ) (Frob := Frob) Q hσ hφ]
  -- The exponent `#O / f` is `e`.
  have hexp : ∀ O : Quotient (orbitRel (stabilizer Γ Q) (Γ ⧸ H)),
      Nat.card (orbit (stabilizer Γ Q) O.out) / (primeBelow (B := B) H Q O.out).inertiaDeg A =
        (primeBelow (B := B) H Q O.out).ramificationIdx A := by
    intro O
    have h := natCard_orbit_stabilizer (A := A) (B := B) (H := H) Q O.out.out
    rw [QuotientGroup.out_eq'] at h
    rw [h, ← primeBelow_mk H Q, QuotientGroup.out_eq']
    have hpos : (primeBelow (B := B) H Q O.out).inertiaDeg A ≠ 0 := by
      intro h0
      rw [← primeBelow_mk H Q, QuotientGroup.out_eq', h0, mul_zero] at h
      have : Nonempty (orbit (stabilizer Γ Q) O.out) := ⟨⟨O.out, mem_orbit_self _⟩⟩
      exact (Nat.card_pos (α := orbit (stabilizer Γ Q) O.out)).ne' h
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hpos)
  simp_rw [hexp]
  rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
  refine finprod_mem_eq_of_bijOn (fun O => primeBelow (B := B) H Q O.out) ⟨?_, ?_, ?_⟩
    fun _ _ => rfl
  · -- The prime below `g⁻¹ Q` lies over `p`.
    intro O _
    refine ⟨Ideal.IsPrime.under B _, ⟨?_⟩⟩
    show Q.under A = ((O.out.out⁻¹ • Q).under B).under A
    rw [Ideal.under_under, Ideal.under_smul]
  · -- Injectivity: `H` is transitive on the primes of `C` above a prime of `B`.
    intro O _ O' _ hOO'
    rw [← Quotient.out_eq' O, ← Quotient.out_eq' O']
    refine Quotient.sound' ?_
    rw [orbitRel_apply]
    obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B C H
      (O'.out.out⁻¹ • Q) (O.out.out⁻¹ • Q) (by
        exact hOO'.symm)
    refine ⟨⟨O.out.out * h * O'.out.out⁻¹, ?_⟩, ?_⟩
    · exact mul_mul_inv_mem_stabilizer hh.symm
    · have := mul_mul_inv_smul_mk H (a := O.out.out) (b := O'.out.out) h.2
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  · -- Surjectivity: going up from `B` to `C`, then transitivity of `Γ` above `p`.
    rintro P ⟨hP, hPp⟩
    have : Algebra.IsIntegral B C := Algebra.IsInvariant.isIntegral B C H
    obtain ⟨⟨Q'', hQ''P, hQ''⟩⟩ := Ideal.nonempty_primesOver (S := C) P
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A C Γ Q Q'' (by
      rw [← Ideal.under_under (B := B) Q'', ← hQ''.over, ← hPp.over])
    refine ⟨Quotient.mk'' (((g⁻¹ : Γ) : Γ ⧸ H)), Set.mem_univ _, ?_⟩
    simp only
    have hmem : (Quotient.mk'' ((g⁻¹ : Γ) : Γ ⧸ H) :
        Quotient (orbitRel (stabilizer Γ Q) (Γ ⧸ H))).out ∈
          orbit (stabilizer Γ Q) ((g⁻¹ : Γ) : Γ ⧸ H) := by
      rw [← orbitRel_apply]
      exact Quotient.exact' (Quotient.out_eq' _)
    obtain ⟨d, hd⟩ := hmem
    change d • _ = _ at hd
    rw [← hd, Subgroup.smul_def, primeBelow_smul H Q d.2, primeBelow_mk, inv_inv, ← hg, hQ''.over]

end Galois

section Compatible

variable {D : Type*} [CommRing D] [Algebra B D] [Algebra D C] [IsScalarTower B D C]
  {𝒢 : Type*} [CommGroup 𝒢] [MulSemiringAction 𝒢 D] [SMulCommClass 𝒢 B D]

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] [SMulCommClass ↥H B C] [Finite Γ] in
/-- **Restriction to an unramified abelian subextension is Frobenius-compatible.** Let `H` act on
`C` and the commutative group `𝒢` on `D` (`B ⊆ D ⊆ C`), compatibly through `r : H →* 𝒢`. If every
prime `R` of `D` has trivial inertia in `𝒢` and `Frob (R ∩ B)` is an arithmetic Frobenius at `R`,
then `y ∈ H` acting on `C / Q'` as `x ↦ x ^ (#(B / Q' ∩ B)) ^ m` restricts to `Frob (Q' ∩ B) ^ m`:
the hypothesis of `Stacks.Adeles.GlobalFunctionField.transfer_eq_prod_orbitRel_frob`. -/
public theorem frobCompatible_of_inertia_eq_bot (r : H →* 𝒢)
    (hr : ∀ (y : H) (x : D), y • algebraMap D C x = algebraMap D C (r y • x))
    (Frob : Ideal B → 𝒢)
    (hFrob : ∀ (R : Ideal D) [R.IsPrime], IsArithFrobAt B (Frob (R.under B)) R)
    (hunr : ∀ (R : Ideal D) [R.IsPrime], R.inertia 𝒢 = ⊥)
    (Q' : Ideal C) [Q'.IsPrime] (y : H) (m : ℕ)
    (hy : ∀ x : C, y • x - x ^ (Nat.card (B ⧸ Q'.under B)) ^ m ∈ Q') :
    r y = Frob (Q'.under B) ^ m := by
  set R := Q'.under D
  have hRB : R.under B = Q'.under B := Ideal.under_under Q'
  have h1 : ∀ x : D, r y • x - x ^ (Nat.card (B ⧸ R.under B)) ^ m ∈ R := by
    intro x
    rw [hRB, Ideal.mem_under, map_sub, map_pow, ← hr]
    exact hy _
  have h2 : ∀ x : D, Frob (R.under B) ^ m • x - x ^ (Nat.card (B ⧸ R.under B)) ^ m ∈ R :=
    pow_smul_sub_pow_mem (hFrob R) m
  have hin : r y * (Frob (R.under B) ^ m)⁻¹ ∈ R.inertia 𝒢 := by
    intro x
    simpa [mul_smul] using sub_mem (h1 ((Frob (R.under B) ^ m)⁻¹ • x))
      (h2 ((Frob (R.under B) ^ m)⁻¹ • x))
  rw [hunr R, Subgroup.mem_bot, mul_inv_eq_one] at hin
  rw [hin, hRB]

end Compatible

end Stacks.Adeles.GlobalFunctionField

end
