module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.CurveModel
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.LocalPrincipality
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Every closed point is periodic under a Frobenius-semilinear automorphism

Let `C` be a smooth proper curve over an algebraically closed field `Ω` of characteristic `p`
which is algebraic over `𝔽_p`, and `Ψ` a `q`-semilinear automorphism of `C` (`q = p ^ n`). **Every
closed point `x` of `C` is periodic under `Ψ`** (`Stacks.Zeta.exists_iterate_closedPointPerm_eq`).

The proof is the coordinate argument, run on the function field `K`. A function `a` regular at a
closed point `y` has a value `a(y) ∈ Ω` (`a - a(y)` vanishes at `y`, the residue field being
`Ω`), and pullback `τ` along `Ψ` satisfies `(τ a)(y) = a(Ψ y) ^ q`. Choose generators
`a_1, …, a_r` of `K` over `Ω` (`K` is essentially of finite type over `Ω`), one of them
nonconstant, and write `τ a_i = b_i / t_i` with `b_i, t_i` polynomials in the `a_j`. All the
finitely many coefficients involved, and the values of the `a_j` at the finitely many relevant
points, lie in a finite subfield `F = 𝔽_{p^M}` of `Ω`, because `Ω` is algebraic over `𝔽_p`.
Outside the finite set `Z` of poles of the `a_i` and zeros of the `t_i`, the property "all `a_j`
take values in `F`" passes from `y` to `Ψ y`; and only finitely many points have this property, a
nonconstant `a_j` taking each of the finitely many values of `F` finitely often. So the orbit of
`x` is finite.

## Main results

* `Stacks.Zeta.valueSubring`: the functions regular at `y` with value in a subfield `F`.
* `Stacks.Zeta.frobFixed`: the subfield `𝔽_{p^M}` of `Ω`, and
  `Stacks.Zeta.exists_mem_frobFixed`: under algebraicity, finitely many elements lie in one.
* `Stacks.Zeta.exists_iterate_closedPointPerm_eq`: the periodicity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

-- Mathlib's `instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent` (a simple nilpotent additive group
-- is commutative) is tried first for `AddCommGroup C.functionField`; its failure sends instance
-- search back through every `IsVariety ?k ?f` instance and every `Field ?k`, which times out
-- (seen on `Neg C.functionField`). It is irrelevant here.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Stacks.Zeta

/-! ### Finite subfields -/

section FiniteSubfield

variable {Ω : Type u} [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]

/-- The subfield `𝔽_{p ^ M} = {c : c ^ p ^ M = c}` of `Ω`. -/
def frobFixed (M : ℕ) : Subfield Ω := (iterateFrobenius Ω p M).eqLocusField (RingHom.id Ω)

/-- `c ∈ 𝔽_{p ^ M}` if and only if `c ^ p ^ M = c`. -/
theorem mem_frobFixed {M : ℕ} {c : Ω} : c ∈ frobFixed (Ω := Ω) p M ↔ c ^ p ^ M = c := Iff.rfl

/-- `𝔽_{p ^ M}` is contained in `𝔽_{p ^ (M * j)}`. -/
theorem frobFixed_le_mul (M j : ℕ) : frobFixed (Ω := Ω) p M ≤ frobFixed p (M * j) := fun c hc => by
  rw [mem_frobFixed] at hc ⊢
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hc]

variable [IsAlgClosed Ω]

/-- For `M > 0`, the subfield `𝔽_{p ^ M}` of an algebraically closed field is finite. -/
theorem finite_frobFixed {M : ℕ} (hM : 0 < M) : Finite (frobFixed (Ω := Ω) p M) := by
  have h := Stacks.Lang.natCard_pow_eq_self (Ω := Ω) p M hM
  have hne : Nat.card {a : Ω // a ^ p ^ M = a} ≠ 0 := by
    rw [h]; exact pow_ne_zero _ hp.out.ne_zero
  exact Nat.finite_of_card_ne_zero hne

omit [IsAlgClosed Ω] in
/-- `x ↦ x ^ (p ^ n)` maps `𝔽_{p ^ M}` into itself, and only elements of `𝔽_{p ^ M}` land there. -/
theorem pow_mem_frobFixed_iff {M : ℕ} (n : ℕ) {d : Ω} :
    d ^ p ^ n ∈ frobFixed p M ↔ d ∈ frobFixed p M := by
  rw [mem_frobFixed, mem_frobFixed, ← pow_mul, mul_comm, pow_mul]
  change iterateFrobenius Ω p n (d ^ p ^ M) = iterateFrobenius Ω p n d ↔ _
  exact (iterateFrobenius Ω p n).injective.eq_iff

omit [IsAlgClosed Ω] in
/-- **An element algebraic over `𝔽_p` lies in a finite field `𝔽_{p ^ M}`, `M ≥ 1`.** -/
theorem exists_mem_frobFixed_of_isAlgebraic (c : Ω)
    (hc : letI := ZMod.algebra Ω p; IsAlgebraic (ZMod p) c) :
    ∃ M, 0 < M ∧ c ∈ frobFixed p M := by
  let := ZMod.algebra Ω p
  set E := IntermediateField.adjoin (ZMod p) ({c} : Set Ω)
  have : FiniteDimensional (ZMod p) E := IntermediateField.adjoin.finiteDimensional hc.isIntegral
  have : Finite E := Module.finite_of_finite (ZMod p)
  let : Fintype E := Fintype.ofFinite E
  have : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  obtain ⟨M, -, hM⟩ := FiniteField.card E p
  refine ⟨M, M.pos, ?_⟩
  have h := FiniteField.pow_card (⟨c, IntermediateField.mem_adjoin_simple_self _ c⟩ : E)
  rw [hM] at h
  exact congrArg Subtype.val h

omit [IsAlgClosed Ω] in
/-- **Finitely many algebraic elements lie in one finite field `𝔽_{p ^ M}`.** -/
theorem exists_mem_frobFixed (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω)
    (s : Finset Ω) : ∃ M, 0 < M ∧ ∀ c ∈ s, c ∈ frobFixed p M := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s _ ih =>
    obtain ⟨M, hM, hs⟩ := ih
    obtain ⟨N, hN, ha⟩ := exists_mem_frobFixed_of_isAlgebraic p a
      (by let := ZMod.algebra Ω p; exact halg.isAlgebraic a)
    refine ⟨N * M, Nat.mul_pos hN hM, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact frobFixed_le_mul p N M ha
    · rw [Nat.mul_comm]; exact frobFixed_le_mul p M N (hs c hc)

end FiniteSubfield

/-- A polynomial with coefficients in a subring, evaluated at elements of the subring, lies in
it. -/
theorem aeval_mem_subring {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subring A)
    {ι : Type*} (a : ι → A) (ha : ∀ i, a i ∈ S) (P : MvPolynomial ι R)
    (hP : ∀ m, algebraMap R A (P.coeff m) ∈ S) : MvPolynomial.aeval a P ∈ S := by
  rw [P.as_sum, map_sum]
  refine S.sum_mem fun m _ => ?_
  rw [MvPolynomial.aeval_monomial]
  exact S.mul_mem (hP m) (prod_mem fun i _ => pow_mem (ha i) _)

/-! ### Values of functions at closed points -/

section Values

/-- A rational function `h` *vanishes* at the closed point `y`: it is zero or has positive order
there. -/
def VanishesAt {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] (y : ClosedPoint C)
    (h : C.functionField) : Prop :=
  h = 0 ∨ 1 ≤ C.ord h y.1

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

omit [IsAlgClosed Ω] [IsProper g] in
include g in
/-- The sum of two functions vanishing at `y` vanishes at `y`. -/
theorem vanishesAt_add {y : ClosedPoint C} {h h' : C.functionField} (hh : VanishesAt y h)
    (hh' : VanishesAt y h') : VanishesAt y (h + h') := by
  by_cases h0 : h + h' = 0
  · exact Or.inl h0
  rcases hh with rfl | hh
  · rwa [zero_add]
  rcases hh' with rfl | hh'
  · rw [add_zero]; exact Or.inr hh
  have := dvr_closedPoint g y
  have := Scheme.ord_add (x := y.1) h0
  exact Or.inr (by omega)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
/-- The product of a function regular at `y` with a function vanishing at `y` vanishes at `y`. -/
theorem vanishesAt_mul {y : ClosedPoint C} {f h : C.functionField} (hf : 0 ≤ C.ord f y.1)
    (hh : VanishesAt y h) : VanishesAt y (f * h) := by
  by_cases f0 : f = 0
  · left; rw [f0, zero_mul]
  rcases hh with rfl | hh
  · left; rw [mul_zero]
  have h0 : h ≠ 0 := by rintro rfl; simp at hh
  right
  rw [Scheme.ord_mul f0 h0]
  omega

omit [IsAlgClosed Ω] [IsProper g] in
/-- A constant function has nonnegative order at every closed point. -/
theorem ord_algebraMap_nonneg (c : Ω) (y : ClosedPoint C) :
    letI := ffAlg g
    0 ≤ C.ord (algebraMap Ω C.functionField c) y.1 := by
  let := ffAlg g
  by_cases hc : c = 0
  · simp [hc]
  · rw [ord_algebraMap_const g hc y]

omit [IsAlgClosed Ω] [IsProper g] in
/-- The negative of a function vanishing at `y` vanishes at `y`. -/
theorem vanishesAt_neg {y : ClosedPoint C} {h : C.functionField} (hh : VanishesAt y h) :
    VanishesAt y (-h) := by
  let := ffAlg g
  have : -h = algebraMap Ω C.functionField (-1) * h := by
    rw [RingHom.map_neg, RingHom.map_one, neg_one_mul]
  rw [this]
  exact vanishesAt_mul g (ord_algebraMap_nonneg g _ y) hh

omit [IsAlgClosed Ω] [IsProper g] in
/-- If `f - c` vanishes at `y` for a constant `c`, then `f` is regular at `y`. -/
theorem ord_nonneg_of_vanishesAt_sub {y : ClosedPoint C} {f : C.functionField} {c : Ω} :
    letI := ffAlg g
    VanishesAt y (f - algebraMap Ω C.functionField c) → 0 ≤ C.ord f y.1 := by
  let := ffAlg g
  intro h
  by_cases f0 : f = 0
  · simp [f0]
  have hf : f = (f - algebraMap Ω C.functionField c) + algebraMap Ω C.functionField c := by ring
  have := dvr_closedPoint g y
  have h1 := Scheme.ord_add (x := y.1) (f := f - algebraMap Ω C.functionField c)
    (g := algebraMap Ω C.functionField c) (by rw [← hf]; exact f0)
  rw [← hf] at h1
  have h2 := ord_algebraMap_nonneg g c y
  rcases h with h | h
  · rw [h, zero_add] at hf; rw [hf]; exact h2
  · omega

/-- The functions regular at the closed point `y` whose value at `y` lies in the subfield `F`:
`f ≡ c` modulo the maximal ideal at `y` for some `c ∈ F`. -/
def valueSubring (y : ClosedPoint C) (F : Subfield Ω) : Subring C.functionField :=
  letI := ffAlg g
  { carrier := {f | ∃ c ∈ F, VanishesAt y (f - algebraMap Ω C.functionField c)}
    mul_mem' := by
      rintro f f' ⟨c, hc, hf⟩ ⟨c', hc', hf'⟩
      refine ⟨c * c', F.mul_mem hc hc', ?_⟩
      have : f * f' - algebraMap Ω C.functionField (c * c') =
          f * (f' - algebraMap Ω C.functionField c') +
            algebraMap Ω C.functionField c' * (f - algebraMap Ω C.functionField c) := by
        rw [RingHom.map_mul]; ring
      rw [this]
      exact vanishesAt_add g (vanishesAt_mul g (ord_nonneg_of_vanishesAt_sub g hf) hf')
        (vanishesAt_mul g (ord_algebraMap_nonneg g c' y) hf)
    one_mem' := ⟨1, F.one_mem, Or.inl (by rw [RingHom.map_one, sub_self])⟩
    add_mem' := by
      rintro f f' ⟨c, hc, hf⟩ ⟨c', hc', hf'⟩
      refine ⟨c + c', F.add_mem hc hc', ?_⟩
      have : f + f' - algebraMap Ω C.functionField (c + c') =
          (f - algebraMap Ω C.functionField c) + (f' - algebraMap Ω C.functionField c') := by
        rw [RingHom.map_add]; ring
      rw [this]
      exact vanishesAt_add g hf hf'
    zero_mem' := ⟨0, F.zero_mem, Or.inl (by rw [RingHom.map_zero, sub_zero])⟩
    neg_mem' := by
      rintro f ⟨c, hc, hf⟩
      refine ⟨-c, F.neg_mem hc, ?_⟩
      have : -f - algebraMap Ω C.functionField (-c) = -(f - algebraMap Ω C.functionField c) := by
        rw [RingHom.map_neg]; ring
      rw [this]
      exact vanishesAt_neg g hf }

omit [IsAlgClosed Ω] [IsProper g] in
/-- `f ∈ valueSubring g y F` if and only if `f - c` vanishes at `y` for some `c ∈ F`. -/
theorem mem_valueSubring {y : ClosedPoint C} {F : Subfield Ω} {f : C.functionField} :
    letI := ffAlg g
    f ∈ valueSubring g y F ↔ ∃ c ∈ F, VanishesAt y (f - algebraMap Ω C.functionField c) :=
  Iff.rfl

omit [IsAlgClosed Ω] [IsProper g] in
/-- A constant function with value in `F` lies in `valueSubring g y F`. -/
theorem algebraMap_mem_valueSubring {y : ClosedPoint C} {F : Subfield Ω} {c : Ω} (hc : c ∈ F) :
    letI := ffAlg g
    algebraMap Ω C.functionField c ∈ valueSubring g y F := by
  let := ffAlg g
  exact ⟨c, hc, Or.inl (sub_self _)⟩

omit [IsAlgClosed Ω] [IsProper g] in
/-- A function with a nonzero value in `F` at `y` is invertible in `valueSubring g y F`. -/
theorem inv_mem_valueSubring {y : ClosedPoint C} {F : Subfield Ω} {t : C.functionField}
    (ht : t ∈ valueSubring g y F) (hnv : ¬ VanishesAt y t) : t⁻¹ ∈ valueSubring g y F := by
  let := ffAlg g
  obtain ⟨e, he, hte⟩ := ht
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [RingHom.map_zero, sub_zero] at hte
    exact hnv hte
  have ht0 : t ≠ 0 := fun h => hnv (Or.inl h)
  have hord : C.ord t y.1 = 0 := by
    have h1 := ord_nonneg_of_vanishesAt_sub g hte
    have h2 : ¬ 1 ≤ C.ord t y.1 := fun h => hnv (Or.inr h)
    omega
  have hinv : C.ord t⁻¹ y.1 = 0 := by
    have := Scheme.ord_mul (x := y.1) ht0 (inv_ne_zero ht0)
    rw [mul_inv_cancel₀ ht0, Stacks.BombieriStepanov.scheme_ord_one, hord] at this
    omega
  refine ⟨e⁻¹, F.inv_mem he, ?_⟩
  have he' : algebraMap Ω C.functionField e ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap Ω C.functionField).injective).2 he0
  have : t⁻¹ - algebraMap Ω C.functionField e⁻¹ =
      (t⁻¹ * algebraMap Ω C.functionField e⁻¹) * -(t - algebraMap Ω C.functionField e) := by
    have hinv' : algebraMap Ω C.functionField e⁻¹ = (algebraMap Ω C.functionField e)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← RingHom.map_mul, inv_mul_cancel₀ he0, RingHom.map_one])
    rw [hinv']
    field_simp
    ring
  rw [this]
  refine vanishesAt_mul g ?_ (vanishesAt_neg g hte)
  by_cases he1 : algebraMap Ω C.functionField e⁻¹ = 0
  · rw [he1, mul_zero]; simp
  rw [Scheme.ord_mul (inv_ne_zero ht0) he1, hinv, zero_add]
  exact ord_algebraMap_nonneg g _ y

variable (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))

omit [IsAlgClosed Ω] [IsProper g] in
include hΨ in
/-- **Values move with `Ψ`**: if `f` has value `c` at `Ψ y`, then `τ f` has value `c ^ q` at
`y`. -/
theorem tau_mem_valueSubring {y : ClosedPoint C} {F : Subfield Ω}
    (hF : ∀ c ∈ F, c ^ p ^ n ∈ F) {f : C.functionField}
    (hf : f ∈ valueSubring g (closedPointPerm Ψ y) F) : tau Ψ f ∈ valueSubring g y F := by
  let := ffAlg g
  obtain ⟨c, hc, h⟩ := hf
  refine ⟨c ^ p ^ n, hF c hc, ?_⟩
  have : tau Ψ f - algebraMap Ω C.functionField (c ^ p ^ n) =
      tau Ψ (f - algebraMap Ω C.functionField c) := by
    rw [RingEquiv.map_sub, tau_algebraMap g p n Ψ hΨ, RingHom.map_pow]
  rw [this]
  rcases h with h | h
  · left; rw [h, RingEquiv.map_zero]
  · right; rw [ord_functionFieldRingEquivOfIso_symm]; exact h

omit [IsProper g] in
include hΨ in
/-- **Values move back along `Ψ`**: if `τ f` has value in `F` at `y` and `F` is closed under
`q`-th roots, then `f` has value in `F` at `Ψ y`. -/
theorem mem_valueSubring_of_tau_mem {y : ClosedPoint C} {F : Subfield Ω}
    (hF : ∀ d : Ω, d ^ p ^ n ∈ F → d ∈ F) {f : C.functionField}
    (hf : tau Ψ f ∈ valueSubring g y F) : f ∈ valueSubring g (closedPointPerm Ψ y) F := by
  let := ffAlg g
  obtain ⟨c, hc, h⟩ := hf
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos hp.out.pos n)
  refine ⟨d, hF d (hd ▸ hc), ?_⟩
  have : tau Ψ (f - algebraMap Ω C.functionField d) =
      tau Ψ f - algebraMap Ω C.functionField c := by
    rw [RingEquiv.map_sub, tau_algebraMap g p n Ψ hΨ, ← RingHom.map_pow, hd]
  rcases h with h | h
  · left
    rw [← this] at h
    exact (map_eq_zero_iff (tau Ψ) (tau Ψ).injective).1 h
  · right
    rw [← this, ord_functionFieldRingEquivOfIso_symm] at h
    exact h

end Values

/-! ### Periodicity -/

section Periodic

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
/-- The function field of a curve is essentially of finite type over the base field. -/
theorem essFiniteType_ffAlg :
    letI := ffAlg g
    Algebra.EssFiniteType Ω C.functionField := by
  have := varietyFunctionField_essFiniteType (⟨C, g⟩ : Variety Ω)
  have h : varietyFunctionFieldAlgebra (⟨C, g⟩ : Variety Ω) = ffAlg g :=
    Algebra.algebra_ext _ _ fun c =>
      Stacks.BombieriStepanov.functionFieldAlgebraMap_eq_fieldToStalk _ c
  rwa [h] at this

omit [IsAlgClosed Ω] in
include g in
/-- A nonzero function vanishes at only finitely many closed points. -/
theorem finite_setOf_vanishesAt {t : C.functionField} (ht : t ≠ 0) :
    {y : ClosedPoint C | VanishesAt y t}.Finite :=
  (finite_setOf_ord_ne_zero g ht).subset fun y hy => by
    rcases hy with h | h
    · exact absurd h ht
    · change C.ord t y.1 ≠ 0; omega

omit [IsAlgClosed Ω] in
include g in
/-- A function has a pole at only finitely many closed points. -/
theorem finite_setOf_ord_neg (a : C.functionField) :
    {y : ClosedPoint C | C.ord a y.1 < 0}.Finite := by
  by_cases ha : a = 0
  · subst ha; simp
  exact (finite_setOf_ord_ne_zero g ha).subset fun y hy => by
    change C.ord a y.1 ≠ 0; exact (Set.mem_ofPred.1 hy).ne

variable (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))

include hΨ in
/-- **Every closed point is periodic** under a Frobenius-semilinear automorphism of a smooth
proper curve over an algebraically closed field algebraic over `𝔽_p`. -/
theorem exists_iterate_closedPointPerm_eq
    (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω) (x : ClosedPoint C) :
    ∃ k, 0 < k ∧ (closedPointPerm Ψ)^[k] x = x := by
  classical
  let := ffAlg g
  let σ := closedPointPerm Ψ
  have := essFiniteType_ffAlg g
  obtain ⟨σ₀, hσ₀⟩ := (Algebra.essFiniteType_iff Ω C.functionField).1 inferInstance
  obtain ⟨w, hw0, hw1⟩ := IsCurve.exists_ord_eq_one Ω g x.2 (ne_genericPoint_of_isClosed g x.2)
  let G : Finset C.functionField := insert w σ₀
  let T : Set C.functionField := ↑G
  let R := Algebra.adjoin Ω T
  have hR : Algebra.adjoin Ω (σ₀ : Set C.functionField) ≤ R :=
    Algebra.adjoin_mono (by
      intro a ha
      exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha)))
  -- `τ a = b a / t a` with `b a, t a ∈ Ω[G]`
  have hτ : ∀ a : C.functionField,
      ∃ t : C.functionField, t ≠ 0 ∧ t ∈ R ∧ tau Ψ a * t ∈ R := fun a => by
    obtain ⟨t, ht, htu, hat⟩ := hσ₀ (tau Ψ a)
    exact ⟨t, htu.ne_zero, hR ht, hR hat⟩
  choose t ht0 htR hbR using hτ
  have hrange : ∀ z ∈ R, ∃ P : MvPolynomial T Ω,
      MvPolynomial.aeval (Subtype.val : T → C.functionField) P = z := fun z hz => by
    have hz' : z ∈ Algebra.adjoin Ω T := hz
    rw [Algebra.adjoin_eq_range] at hz'
    exact hz'
  choose! Pt hPt using fun a : C.functionField => hrange (t a) (htR a)
  choose! Pb hPb using fun a : C.functionField => hrange (tau Ψ a * t a) (hbR a)
  -- the finite set of coefficients
  let coef : Finset Ω := G.biUnion fun a => (Pt a).coeffs ∪ (Pb a).coeffs
  -- the bad points: poles of the generators and zeros of the denominators
  let Z : Set (ClosedPoint C) := (⋃ a ∈ G, {y | C.ord a y.1 < 0}) ∪
    ⋃ a ∈ G, {y | VanishesAt y (t a)}
  have hZ : Z.Finite :=
    ((G.finite_toSet.biUnion fun a _ => finite_setOf_ord_neg g a).union
      (G.finite_toSet.biUnion fun a _ => finite_setOf_vanishesAt g (ht0 a)))
  let Good : Subfield Ω → ClosedPoint C → Prop := fun F y => ∀ a ∈ G, a ∈ valueSubring g y F
  -- stability of `Good F` outside `Z`
  have hstep : ∀ M, (∀ c ∈ coef, c ∈ frobFixed p M) → ∀ y, y ∉ Z →
      Good (frobFixed p M) y → Good (frobFixed p M) (σ y) := by
    intro M hcoef y hyZ hy a ha
    refine mem_valueSubring_of_tau_mem g p n Ψ hΨ (fun d hd => (pow_mem_frobFixed_iff p n).1 hd) ?_
    let S := valueSubring g y (frobFixed p M)
    have hgen : ∀ i : T, (i : C.functionField) ∈ S := fun i => hy i i.2
    have hcoefS : ∀ P : MvPolynomial T Ω, (∀ c ∈ P.coeffs, c ∈ frobFixed p M) →
        MvPolynomial.aeval (Subtype.val : T → C.functionField) P ∈ S := fun P hP =>
      aeval_mem_subring S _ hgen P fun m => by
        by_cases hm : P.coeff m = 0
        · rw [hm, map_zero]; exact S.zero_mem
        · exact algebraMap_mem_valueSubring g (hP _ (MvPolynomial.coeff_mem_coeffs m hm))
    have htS : t a ∈ S := by
      rw [← hPt a]
      exact hcoefS _ fun c hc => hcoef c (Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_union_left _ hc⟩)
    have hbS : tau Ψ a * t a ∈ S := by
      rw [← hPb a]
      exact hcoefS _ fun c hc => hcoef c (Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_union_right _ hc⟩)
    have htnv : ¬ VanishesAt y (t a) := fun h =>
      hyZ (Or.inr (Set.mem_biUnion (x := a) ha h))
    have := S.mul_mem hbS (inv_mem_valueSubring g htS htnv)
    rwa [mul_assoc, mul_inv_cancel₀ (ht0 a), mul_one] at this
  -- `Good F` holds at only finitely many points: `w` is not constant
  have hfinGood : ∀ M, 0 < M → {y | Good (frobFixed p M) y}.Finite := by
    intro M hM
    have := finite_frobFixed (Ω := Ω) p hM
    have hwc : ∀ c : Ω, w - algebraMap Ω C.functionField c ≠ 0 := fun c h => by
      rw [sub_eq_zero] at h
      rw [h] at hw1
      by_cases hc : c = 0
      · rw [hc, map_zero, Scheme.ord_zero] at hw1; exact one_ne_zero hw1.symm
      · rw [ord_algebraMap_const g hc x] at hw1; exact zero_ne_one hw1
    refine (Set.finite_iUnion fun c : frobFixed (Ω := Ω) p M =>
      finite_setOf_vanishesAt g (hwc c)).subset fun y hy => ?_
    obtain ⟨c, hc, hvan⟩ := hy w (Finset.mem_insert_self w σ₀)
    exact Set.mem_iUnion.2 ⟨⟨c, hc⟩, hvan⟩
  by_contra hnot
  push Not at hnot
  have hinj : Function.Injective fun k : ℕ => (⇑σ)^[k] x := by
    intro i j hij
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (by omega)
    have h1 : (⇑σ)^[i] ((⇑σ)^[j - i] x) = (⇑σ)^[i] x := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]
      exact hij.symm
    exact hnot (j - i) (by omega) (σ.injective.iterate i h1)
  -- the orbit leaves `Z` for good
  have hT : {k : ℕ | (⇑σ)^[k] x ∈ Z}.Finite := hZ.preimage hinj.injOn
  obtain ⟨k₀, hk₀⟩ := hT.bddAbove
  let y₀ := (⇑σ)^[k₀ + 1] x
  have hout : ∀ k, (⇑σ)^[k] y₀ ∉ Z := fun k h => by
    have := hk₀ (show k + (k₀ + 1) ∈ {k : ℕ | (⇑σ)^[k] x ∈ Z} by
      rw [Set.mem_ofPred, Function.iterate_add_apply]; exact h)
    omega
  -- values of the generators at `y₀` and the coefficients lie in one finite field
  have hval : ∀ a ∈ G, ∃ c : Ω, VanishesAt y₀ (a - algebraMap Ω C.functionField c) := fun a ha => by
    have hreg : 0 ≤ C.ord a y₀.1 := by
      by_contra h
      exact hout 0 (Or.inl (Set.mem_biUnion (x := a) ha (not_le.1 h)))
    obtain ⟨c, hc | hc⟩ := exists_one_le_ord_sub g y₀.2 hreg
    · exact ⟨c, Or.inl (sub_eq_zero.2 hc)⟩
    · exact ⟨c, Or.inr hc⟩
  choose! val hvalv using hval
  obtain ⟨M, hM, hMs⟩ := exists_mem_frobFixed p halg (coef ∪ G.image val)
  have hgood : ∀ k, Good (frobFixed p M) ((⇑σ)^[k] y₀) := by
    intro k
    induction k with
    | zero =>
      intro a ha
      exact ⟨val a, hMs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)),
        hvalv a ha⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hstep M (fun c hc => hMs c (Finset.mem_union_left _ hc)) _ (hout k) ih
  have hinj' : Function.Injective fun k : ℕ => (⇑σ)^[k] y₀ := fun i j h => by
    have := hinj (a₁ := i + (k₀ + 1)) (a₂ := j + (k₀ + 1)) (by
      simp only [Function.iterate_add_apply]; exact h)
    omega
  exact Set.infinite_of_injective_forall_mem (s := {y | Good (frobFixed p M) y}) hinj'
    (fun k => hgood k) (hfinGood M hM)

end Periodic

end Stacks.Zeta

end
