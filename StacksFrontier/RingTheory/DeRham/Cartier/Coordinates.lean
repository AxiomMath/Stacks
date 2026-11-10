module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.RingTheory.DeRham.Cartier.Cartan

/-!
# The Cartier isomorphism in coordinates

Let `p` be a prime and `A → B` a ring map with `B` of characteristic `p`. Suppose `t₁, …, tₙ ∈ B`
are **Frobenius coordinates**:

* the differentials `dt₁, …, dtₙ` form a basis of `Ω[B⁄A]`, and
* the monomials `t^α`, `0 ≤ αⱼ < p`, form a basis of `B` over itself acting through the
  Frobenius, that is `(c_α)_α ↦ ∑_α c_α^p t^α` is a bijection `B^{[0,p)^n} → B`.

A polynomial algebra over a perfect ring has Frobenius coordinates
(`StacksFrontier.RingTheory.DeRham.Cartier.Polynomial`); so does an algebra étale over one, by the
relative Frobenius isomorphism of an étale map. This file proves that then **the inverse Cartier
map `C⁻¹ : Ω^i_{B/A} ⟶ H^i(F_*Ω^•_{B/A})` is bijective in every degree**.

The proof uses the Euler vector fields `θⱼ = tⱼ ∂/∂tⱼ` (the `B`-linear forms `tⱼ · dtⱼ^*`) and
their Lie derivatives `Lⱼ = d ι_{θⱼ} + ι_{θⱼ} d`. On the twisted spanning set
`c^p t^α dt_s` of `Ω^i_{B/A}` (with `s` a set of `i` indices) the operator `Lⱼ` is diagonal, with
eigenvalue the `j`-th weight `αⱼ + [j ∈ s]`. Hence `πⱼ = 1 - Lⱼ^{p-1}` is, by Fermat, the
projector onto the weights divisible by `p`, and `π = π₁ ⋯ πₙ` kills every spanning form except
the `c^p t_s^{p-1} dt_s`, which it fixes. On the other hand `Lⱼ^{p-1}` sends closed forms to
exact forms (Cartan's formula, `KaehlerDifferential.Cartier.lie_pow_eq_deRhamDifferential`), so
every closed form is cohomologous to its image under `π`, which is `C⁻¹` of a form; and an
exact form `dη` in the span of the `t_s^{p-1} dt_s` is `π(dη) = d(πη) = 0`, since the forms
`t_s^{p-1} dt_s` are closed.

## Main definitions

* `KaehlerDifferential.Cartier.monomial`: `t^α = ∏ⱼ tⱼ^{αⱼ}`.
* `KaehlerDifferential.Cartier.eulerField`: the Euler vector field `θⱼ = tⱼ ∂/∂tⱼ`.
* `KaehlerDifferential.Cartier.weightProj`: the projector `πⱼ = 1 - Lⱼ^{p-1}`.
* `KaehlerDifferential.Cartier.IsFrobeniusCoordinates`: the two conditions above.

## Main results

* `KaehlerDifferential.Cartier.lie_eulerField_spanForm`: `Lⱼ (c^p t^α dt_σ) = (αⱼ + #σ⁻¹(j)) ·
  c^p t^α dt_σ`.
* `KaehlerDifferential.Cartier.inverseCartier_bijective_of_isFrobeniusCoordinates`: **the
  Cartier isomorphism** for an algebra with Frobenius coordinates.

## References

* N. Katz, *Nilpotent connections and the monodromy theorem*, Publ. Math. IHÉS 39 (1970), §7.
* P. Deligne and L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987), §1.
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential exteriorPower

universe u

namespace KaehlerDifferential.Cartier

/-! ### Derivations on monomials -/

section Monomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {ι : Type*}

/-- A derivation scaling each `u l` by `λ l` scales a monomial by its weight:
`δ(∏ u_l^{a_l}) = (∑ a_l λ_l) ∏ u_l^{a_l}`. -/
theorem derivation_prod_pow (δ : Derivation A B B) (u lam : ι → B)
    (hδ : ∀ l, δ (u l) = lam l * u l) (a : ι → ℕ) (s : Finset ι) :
    δ (∏ l ∈ s, u l ^ a l) = (∑ l ∈ s, (a l : B) * lam l) * ∏ l ∈ s, u l ^ a l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
      rw [Finset.prod_insert hl, Finset.sum_insert hl, Derivation.leibniz, ih,
        Derivation.leibniz_pow, hδ, smul_eq_mul, smul_eq_mul, smul_eq_mul, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos (a l) with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, a l = m + 1 := ⟨a l - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel]
        push_cast
        ring

end Monomial

/-! ### Fermat's little theorem for the weights -/

section Fermat

variable (p : ℕ) [Fact p.Prime]

/-- In characteristic `p`, `w^{p-1} • x` is `x` when `p ∤ w` and `0` when `p ∣ w`. -/
theorem pow_pred_nsmul_eq (B : Type*) [CommRing B] [CharP B p] {M : Type*} [AddCommGroup M]
    [Module B M] (w : ℕ) (x : M) :
    w ^ (p - 1) • x = if (p ∣ w) then 0 else x := by
  have hp : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  rw [← Nat.cast_smul_eq_nsmul B, Nat.cast_pow]
  split_ifs with h
  · rw [(CharP.cast_eq_zero_iff B p w).2 h, zero_pow (by omega), zero_smul]
  · have hz : (w : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h1 := ZMod.pow_card_sub_one_eq_one hz
    have h2 := congrArg (ZMod.castHom (dvd_refl p) B) h1
    rw [map_pow, map_one, map_natCast] at h2
    rw [h2, one_smul]

end Fermat

section Coordinates

variable (p : ℕ) [Fact p.Prime] (A : Type u) {B : Type u} [CommRing A] [CommRing B]
  [Algebra A B] [CharP B p] {n : ℕ} (t : Fin n → B)

/-- The monomial `t^α = ∏ⱼ tⱼ^{αⱼ}`. -/
def monomial (α : Fin n → ℕ) : B := ∏ j, t j ^ α j

variable (b : Module.Basis (Fin n) B (Ω[B⁄A]))

/-- **The Euler vector field** `θⱼ = tⱼ ∂/∂tⱼ`, the `B`-linear form `tⱼ · dtⱼ^*` on `Ω[B⁄A]`,
for a basis `b` of `Ω[B⁄A]`. -/
def eulerField (j : Fin n) : Ω[B⁄A] →ₗ[B] B :=
  t j • b.coord j

/-- The spanning forms `c^p t^α dt_σ` of the twisted forms. -/
def spanForm (c : B) (α : Fin n → ℕ) {i : ℕ} (σ : Fin i → Fin n) : ⋀[B]^i (Ω[B⁄A]) :=
  (c ^ p * monomial t α) • ιMulti B i fun k ↦ D A B (t (σ k))

/-- **The projector onto the weights divisible by `p`** in the `j`-th variable,
`πⱼ = 1 - Lⱼ^{p-1}`. -/
def weightProj (j : Fin n) (i : ℕ) : ⋀[B]^i (Ω[B⁄A]) →ₗ[A] ⋀[B]^i (Ω[B⁄A]) :=
  LinearMap.id - lie A (eulerField A t b j) i ^ (p - 1)

/-- The composite `π_{j₁} ∘ ⋯ ∘ π_{j_k}` of the projectors along a list of variables. -/
def projList (l : List (Fin n)) (i : ℕ) : ⋀[B]^i (Ω[B⁄A]) →ₗ[A] ⋀[B]^i (Ω[B⁄A]) :=
  l.foldr (fun j f ↦ weightProj p A t b j i ∘ₗ f) LinearMap.id

/-- The form `t_s^{p-1} dt_s = t_{σ(1)}^{p-1} dt_{σ(1)} ∧ ⋯ ∧ t_{σ(i)}^{p-1} dt_{σ(i)}` attached
to a set `s` of `i` variables, `σ` its increasing enumeration. -/
def cartierBasisForm {i : ℕ} (s : Set.powersetCard (Fin n) i) : ⋀[B]^i (Ω[B⁄A]) :=
  ιMulti B i fun k ↦ t (Set.powersetCard.ofFinEmbEquiv.symm s k) ^ (p - 1) •
    D A B (t (Set.powersetCard.ofFinEmbEquiv.symm s k))

/-- The twisted-semilinear map `∑_s c_s dt_s ↦ ∑_s c_s^p t_s^{p-1} dt_s`, which represents the
inverse Cartier map on forms. -/
def cartierRep (i : ℕ) (ω : ⋀[B]^i (Ω[B⁄A])) : ⋀[B]^i (Ω[B⁄A]) :=
  ∑ s, ((b.exteriorPower i).repr ω s) ^ p • cartierBasisForm p A t s

variable (B) in
/-- **Frobenius coordinates** `t₁, …, tₙ`: the monomials `t^α` with `0 ≤ αⱼ < p` form a basis of
`B` over itself acting through the Frobenius, that is `(c_α) ↦ ∑_α c_α^p t^α` is bijective. -/
def IsFrobeniusCoordinates : Prop :=
  Function.Bijective fun c : (Fin n → Fin p) → B ↦
    ∑ α, c α ^ p * monomial t (fun j ↦ (α j : ℕ))

variable {A t b} (hb : ∀ j, b j = D A B (t j))
include hb

/-- `θⱼ(dt_l)` is `t_l` when `l = j` and `0` otherwise. -/
theorem eulerField_D (j l : Fin n) :
    eulerField A t b j (D A B (t l)) = if l = j then t l else 0 := by
  rw [← hb, eulerField, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

/-- `θⱼ(d t^α) = αⱼ t^α`. -/
theorem eulerField_D_monomial (j : Fin n) (α : Fin n → ℕ) :
    eulerField A t b j (D A B (monomial t α)) = (α j : B) * monomial t α := by
  classical
  have h := derivation_prod_pow ((eulerField A t b j).compDer (D A B)) t
    (fun l ↦ if l = j then 1 else 0) (fun l ↦ by
      change eulerField A t b j (D A B (t l)) = _
      rw [eulerField_D hb]
      split_ifs <;> simp) α Finset.univ
  change (eulerField A t b j).compDer (D A B) (∏ l, t l ^ α l) = _
  rw [h, monomial]
  simp

/-- **The Lie derivative of `dt_{σ(1)} ∧ ⋯ ∧ dt_{σ(i)}`** along `θⱼ` is the number of `k` with
`σ k = j` times the form. -/
theorem lie_eulerField_ιMulti_D (j : Fin n) {i : ℕ} (σ : Fin i → Fin n) :
    lie A (eulerField A t b j) i (ιMulti B i fun k ↦ D A B (t (σ k))) =
      (∑ k, if σ k = j then 1 else 0 : ℕ) • ιMulti B i fun k ↦ D A B (t (σ k)) := by
  induction i with
  | zero =>
      have h0 := deRhamDifferential_zero_smul_ιMulti (A := A) (1 : B)
        (fun k : Fin 0 ↦ D A B (t (σ k)))
      rw [one_smul, Derivation.map_one_eq_zero] at h0
      have hz : (ιMulti B 1 fun _ : Fin 1 ↦ (0 : Ω[B⁄A])) = 0 :=
        map_zero (exteriorPower.oneEquiv B (Ω[B⁄A])).symm
      rw [lie_zero_apply, h0, hz, map_zero]
      simp
  | succ i ih =>
      have hcons : (ιMulti B (i + 1) fun k ↦ D A B (t (σ k))) =
          wedgeLeft (D A B (t (σ 0))) i (ιMulti B i fun k ↦ D A B (t (σ k.succ))) := by
        rw [wedgeLeft_ιMulti]
        congr 1
        funext k
        refine Fin.cases rfl (fun k ↦ rfl) k
      rw [hcons, lie_wedgeLeft_D, ih (fun k ↦ σ k.succ), map_nsmul, eulerField_D hb,
        Fin.sum_univ_succ]
      by_cases h : σ 0 = j
      · rw [ite_eq_left h, ite_eq_left h, add_smul, one_smul]
      · rw [ite_eq_right h, ite_eq_right h, map_zero, exteriorPower.wedgeLeft_zero,
          LinearMap.zero_apply, zero_add, zero_add]

omit [Fact p.Prime] in
/-- **The spanning forms are eigenvectors of the Lie derivatives**:
`Lⱼ (c^p t^α dt_σ) = (αⱼ + #σ⁻¹(j)) · c^p t^α dt_σ`. -/
theorem lie_eulerField_spanForm (j : Fin n) (c : B) (α : Fin n → ℕ) {i : ℕ}
    (σ : Fin i → Fin n) :
    lie A (eulerField A t b j) i (spanForm p A t c α σ) =
      (α j + ∑ k, if σ k = j then 1 else 0 : ℕ) • spanForm p A t c α σ := by
  rw [spanForm, lie_smul, lie_eulerField_ιMulti_D hb, Derivation.leibniz, D_pow_char p A c,
    smul_zero, add_zero, map_smul, eulerField_D_monomial hb]
  simp only [← Nat.cast_smul_eq_nsmul B, Nat.cast_add, smul_smul, smul_eq_mul]
  rw [← add_smul]
  congr 1
  ring

omit [Fact p.Prime] in
/-- The powers of the Lie derivatives on the spanning forms. -/
theorem lie_eulerField_pow_spanForm (j : Fin n) (m : ℕ) (c : B) (α : Fin n → ℕ) {i : ℕ}
    (σ : Fin i → Fin n) :
    (lie A (eulerField A t b j) i ^ m) (spanForm p A t c α σ) =
      (α j + ∑ k, if σ k = j then 1 else 0 : ℕ) ^ m • spanForm p A t c α σ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_nsmul, lie_eulerField_spanForm p hb, smul_smul,
        ← pow_succ]

end Coordinates

/-! ### The projectors -/

/-- `πⱼ x = x - Lⱼ^{p-1} x`. -/
private theorem weightProj_apply (p : ℕ) {A : Type u} {B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {n : ℕ} (t : Fin n → B) (b : Module.Basis (Fin n) B (Ω[B⁄A])) (j : Fin n)
    (i : ℕ) (x : ⋀[B]^i (Ω[B⁄A])) :
    weightProj p A t b j i x = x - (lie A (eulerField A t b j) i ^ (p - 1)) x := rfl

/-- `projList` of a cons applies `πⱼ` last. -/
private theorem projList_cons (p : ℕ) {A : Type u} {B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {n : ℕ} (t : Fin n → B) (b : Module.Basis (Fin n) B (Ω[B⁄A])) (j : Fin n)
    (l : List (Fin n)) (i : ℕ) (x : ⋀[B]^i (Ω[B⁄A])) :
    projList p A t b (j :: l) i x = weightProj p A t b j i (projList p A t b l i x) := rfl

section Projectors

variable (p : ℕ) [Fact p.Prime] {A : Type u} {B : Type u} [CommRing A] [CommRing B]
  [Algebra A B] [CharP B p] {n : ℕ} {t : Fin n → B} {b : Module.Basis (Fin n) B (Ω[B⁄A])}
  (hb : ∀ j, b j = D A B (t j))
include hb

/-- `πⱼ` on a spanning form: the identity when its `j`-th weight is divisible by `p`, zero
otherwise. -/
theorem weightProj_spanForm (j : Fin n) (c : B) (α : Fin n → ℕ) {i : ℕ} (σ : Fin i → Fin n) :
    weightProj p A t b j i (spanForm p A t c α σ) =
      if p ∣ (α j + ∑ k, if σ k = j then 1 else 0) then spanForm p A t c α σ else 0 := by
  rw [weightProj_apply, lie_eulerField_pow_spanForm p hb, pow_pred_nsmul_eq p B]
  split_ifs <;> simp

/-- The composite projector on a spanning form. -/
theorem projList_spanForm (l : List (Fin n)) (c : B) (α : Fin n → ℕ) {i : ℕ}
    (σ : Fin i → Fin n) :
    projList p A t b l i (spanForm p A t c α σ) =
      if ∀ j ∈ l, p ∣ (α j + ∑ k, if σ k = j then 1 else 0) then spanForm p A t c α σ
      else 0 := by
  induction l with
  | nil => simp [projList]
  | cons j l ih =>
      rw [projList_cons, ih]
      by_cases hl : ∀ j ∈ l, p ∣ (α j + ∑ k, if σ k = j then 1 else 0)
      · rw [ite_eq_left hl, weightProj_spanForm p hb]
        by_cases hj : p ∣ (α j + ∑ k, if σ k = j then 1 else 0)
        · rw [ite_eq_left hj, ite_eq_left]
          intro j' hj'
          rcases List.mem_cons.1 hj' with rfl | h
          · exact hj
          · exact hl j' h
        · rw [ite_eq_right hj, ite_eq_right]
          exact fun h ↦ hj (h j List.mem_cons_self)
      · rw [ite_eq_right hl, map_zero, ite_eq_right]
        exact fun h ↦ hl fun j' hj' ↦ h j' (List.mem_cons_of_mem _ hj')

omit hb [Fact p.Prime] [CharP B p] in
/-- The projectors commute with `d`. -/
theorem deRhamDifferential_projList (l : List (Fin n)) (i : ℕ) (x : ⋀[B]^i (Ω[B⁄A])) :
    deRhamDifferential (A := A) i (projList p A t b l i x) =
      projList p A t b l (i + 1) (deRhamDifferential i x) := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
      rw [projList_cons, projList_cons, ← ih, weightProj_apply, weightProj_apply, map_sub,
        deRhamDifferential_lie_pow]

omit hb [Fact p.Prime] in
/-- The projectors are linear for the Frobenius action. -/
theorem projList_pow_char_smul (l : List (Fin n)) (i : ℕ) (c : B) (x : ⋀[B]^i (Ω[B⁄A])) :
    projList p A t b l i (c ^ p • x) = c ^ p • projList p A t b l i x := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
      rw [projList_cons, projList_cons, ih, weightProj_apply, weightProj_apply,
        lie_pow_pow_char_smul A _ p, smul_sub]

omit hb in
/-- **A closed form is cohomologous to its projection**, and the projection is closed. -/
theorem projList_closed (l : List (Fin n)) (i : ℕ) (x : ⋀[B]^i (Ω[B⁄A]))
    (hx : deRhamDifferential (A := A) i x = 0) :
    deRhamDifferential (A := A) i (projList p A t b l i x) = 0 ∧
      twist p (x - projList p A t b l i x) ∈ exactForms p A B i := by
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  induction l with
  | nil =>
      refine ⟨hx, ?_⟩
      rw [show projList p A t b [] i x = x from rfl, sub_self, map_zero]
      exact zero_mem _
  | cons j l ih =>
      obtain ⟨hcl, hex⟩ := ih
      set y := projList p A t b l i x
      rw [projList_cons]
      have hw : weightProj p A t b j i y = y - (lie A (eulerField A t b j) i ^ (m + 1)) y := by
        rw [weightProj_apply, hm]
      refine ⟨?_, ?_⟩
      · rw [hw, map_sub, hcl, deRhamDifferential_lie_pow_eq_zero A _ i (m + 1) y hcl, sub_zero]
      · have hlie : twist p ((lie A (eulerField A t b j) i ^ (m + 1)) y) ∈ exactForms p A B i := by
          cases i with
          | zero =>
              rw [lie_pow_zero_eq_zero_of_closed A _ m y hcl, map_zero]
              exact zero_mem _
          | succ k =>
              exact (twist_mem_exactForms_succ _).2
                ⟨_, (lie_pow_eq_deRhamDifferential A _ k m y hcl).symm⟩
        have : (x - weightProj p A t b j i y : ⋀[B]^i (Ω[B⁄A])) =
            (x - y) + (lie A (eulerField A t b j) i ^ (m + 1)) y := by
          rw [hw]; abel
        rw [this, map_add]
        exact add_mem hex hlie

end Projectors


/-! ### The Cartier isomorphism -/

section Main

variable (p : ℕ) [Fact p.Prime] {A : Type u} {B : Type u} [CommRing A] [CommRing B]
  [Algebra A B] [CharP B p] {n : ℕ} {t : Fin n → B} {b : Module.Basis (Fin n) B (Ω[B⁄A])}

/-- The increasing enumeration of a set of variables. -/
abbrev enum {i : ℕ} (s : Set.powersetCard (Fin n) i) : Fin i → Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm s

/-- The increasing enumeration of a set of variables is injective. -/
theorem enum_injective {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    Function.Injective (enum s) :=
  (Set.powersetCard.ofFinEmbEquiv.symm s).injective

/-- The values of the increasing enumeration of `s` are the elements of `s`. -/
theorem exists_enum_eq_iff {i : ℕ} (s : Set.powersetCard (Fin n) i) (j : Fin n) :
    (∃ k, enum s k = j) ↔ j ∈ (s : Finset (Fin n)) :=
  Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s j

/-- The number of `k` with `σ_s(k) = j` is `[j ∈ s]`. -/
theorem sum_enum_eq {i : ℕ} (s : Set.powersetCard (Fin n) i) (j : Fin n) :
    (∑ k, if enum s k = j then 1 else 0 : ℕ) = if j ∈ (s : Finset (Fin n)) then 1 else 0 := by
  classical
  rw [Finset.sum_boole, Nat.cast_id]
  split_ifs with hj
  · obtain ⟨k, hk⟩ := (exists_enum_eq_iff s j).2 hj
    rw [Finset.card_eq_one]
    refine ⟨k, Finset.eq_singleton_iff_unique_mem.2 ⟨by simp [hk], fun k' hk' ↦ ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    exact enum_injective s (hk'.trans hk.symm)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun k _ hk ↦ hj ((exists_enum_eq_iff s j).1 ⟨k, hk⟩)

/-- The exponent vector of `t_s^{p-1}`. -/
def cartierExponent {i : ℕ} (s : Set.powersetCard (Fin n) i) : Fin n → Fin p :=
  fun j ↦ if j ∈ (s : Finset (Fin n)) then ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
    else ⟨0, (Fact.out : p.Prime).pos⟩

/-- **The weights of a spanning form are all divisible by `p` exactly when it is `c^p t_s^{p-1}
dt_s`.** -/
theorem forall_dvd_iff {i : ℕ} (s : Set.powersetCard (Fin n) i) (α : Fin n → Fin p) :
    (∀ j ∈ List.finRange n, p ∣ ((α j : ℕ) + ∑ k, if enum s k = j then 1 else 0)) ↔
      α = cartierExponent p s := by
  have hp := (Fact.out : p.Prime).two_le
  constructor
  · intro h
    funext j
    have hj := h j (List.mem_finRange j)
    rw [sum_enum_eq] at hj
    apply Fin.ext
    have hα := (α j).2
    simp only [cartierExponent]
    split_ifs at hj ⊢ with hs
    · obtain ⟨m, hm⟩ := hj
      rcases m with _ | _ | m
      · omega
      · simp only at hm ⊢; omega
      · nlinarith
    · obtain ⟨m, hm⟩ := hj
      rcases m with _ | m
      · simpa using hm
      · nlinarith
  · rintro rfl j _
    rw [sum_enum_eq]
    simp only [cartierExponent]
    split_ifs
    · exact ⟨1, by simp; omega⟩
    · simp

variable {p}

omit [CharP B p] in
/-- The monomial with exponent vector `cartierExponent p s` is `∏ₖ t_{σ_s(k)}^{p-1}`. -/
theorem monomial_cartierExponent {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    monomial t (fun j ↦ (cartierExponent p s j : ℕ)) = ∏ k, t (enum s k) ^ (p - 1) := by
  classical
  rw [monomial]
  have h1 : (∏ j, t j ^ (cartierExponent p s j : ℕ)) =
      ∏ j, if j ∈ (s : Finset (Fin n)) then t j ^ (p - 1) else 1 := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp only [cartierExponent]
    split_ifs <;> simp
  rw [h1, Finset.prod_ite_mem, Finset.univ_inter]
  have h2 : ((s : Finset (Fin n))) =
      Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨fun hj ↦ (exists_enum_eq_iff s j).2 hj, fun hj ↦ (exists_enum_eq_iff s j).1 hj⟩
  rw [h2, Finset.prod_map]
  rfl

variable (p) in
omit [CharP B p] in
/-- `t_s^{p-1} dt_s` is the spanning form with `c = 1`, exponent vector `cartierExponent p s` and
`σ` the increasing enumeration of `s`. -/
theorem cartierBasisForm_eq_spanForm {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    cartierBasisForm p A t s =
      spanForm p A t 1 (fun j ↦ (cartierExponent p s j : ℕ)) (enum s) := by
  rw [cartierBasisForm, spanForm, one_pow, one_mul, monomial_cartierExponent]
  exact (ιMulti B i).toMultilinearMap.map_smul_univ (fun k ↦ t (enum s k) ^ (p - 1))
    (fun k ↦ D A B (t (enum s k)))

end Main

section Theorem

variable (p : ℕ) [Fact p.Prime] {A : Type u} {B : Type u} [CommRing A] [CommRing B]
  [Algebra A B] [CharP B p] {n : ℕ} {t : Fin n → B} {b : Module.Basis (Fin n) B (Ω[B⁄A])}
  (hb : ∀ j, b j = D A B (t j))
include hb

/-- The basis of `Ω^i_{B/A}` induced by `b` consists of the forms `dt_s`. -/
theorem exteriorPower_basis_eq {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    b.exteriorPower i s = ιMulti B i fun k ↦ D A B (t (enum s k)) := by
  rw [exteriorPower.basis_apply, ιMulti_family]
  congr 1
  funext k
  exact hb _

omit hb in
/-- `cartierRep` is additive. -/
theorem cartierRep_add (i : ℕ) (ω ω' : ⋀[B]^i (Ω[B⁄A])) :
    cartierRep p A t b i (ω + ω') = cartierRep p A t b i ω + cartierRep p A t b i ω' := by
  simp only [cartierRep, map_add, Finsupp.add_apply, add_pow_char, add_smul,
    Finset.sum_add_distrib]

omit hb [CharP B p] in
/-- `cartierRep` sends `0` to `0`. -/
theorem cartierRep_zero (i : ℕ) : cartierRep p A t b i 0 = 0 := by
  simp [cartierRep, zero_pow (Fact.out : p.Prime).ne_zero]

omit hb [CharP B p] in
/-- `cartierRep (c dt_s) = c^p t_s^{p-1} dt_s`. -/
theorem cartierRep_smul_basis {i : ℕ} (c : B) (s : Set.powersetCard (Fin n) i) :
    cartierRep p A t b i (c • b.exteriorPower i s) = c ^ p • cartierBasisForm p A t s := by
  classical
  rw [cartierRep, map_smul, Module.Basis.repr_self, Finset.sum_eq_single s]
  · simp
  · intro s' _ hs'
    simp [Ne.symm hs', zero_pow (Fact.out : p.Prime).ne_zero]
  · simp

omit hb [Fact p.Prime] [CharP B p] in
/-- The forms `t_s^{p-1} dt_s` are closed. -/
theorem deRhamDifferential_cartierBasisForm {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    deRhamDifferential (A := A) i (cartierBasisForm p A t s) = 0 :=
  ιMulti_mem_closedForms _ fun k ↦ by
    rw [ιMulti_one_smul]
    exact deRhamDifferential_pow_pred_smul_D p _

omit hb [Fact p.Prime] in
/-- The forms `cartierRep ω` are closed. -/
theorem deRhamDifferential_cartierRep (i : ℕ) (ω : ⋀[B]^i (Ω[B⁄A])) :
    deRhamDifferential (A := A) i (cartierRep p A t b i ω) = 0 := by
  rw [cartierRep, map_sum]
  exact Finset.sum_eq_zero fun s _ ↦ by
    rw [deRhamDifferential_pow_smul, deRhamDifferential_cartierBasisForm, smul_zero]

omit hb in
variable (t b) in
/-- `cartierRep ω`, as a closed form. -/
abbrev cartierRepClass (i : ℕ) (ω : ⋀[B]^i (Ω[B⁄A])) : closedForms p A B i :=
  ⟨twist p (cartierRep p A t b i ω),
    (twist_mem_closedForms _).2 (deRhamDifferential_cartierRep p i ω)⟩

/-- **`cartierRep` represents the inverse Cartier map.** -/
theorem inverseCartier_eq_cohomologyMk_cartierRep (i : ℕ) (ω : ⋀[B]^i (Ω[B⁄A])) :
    inverseCartier p A B i ω = cohomologyMk p A B i (cartierRepClass p t b i ω) := by
  conv_lhs => rw [← (b.exteriorPower i).sum_repr ω]
  rw [map_sum]
  have hcl : cartierRepClass p t b i ω =
      ∑ s, (b.exteriorPower i).repr ω s • wedgeClosed p A B i (cartierForm p ∘ (t ∘ enum s)) := by
    apply Subtype.ext
    change twist p (∑ s, ((b.exteriorPower i).repr ω s) ^ p • cartierBasisForm p A t s) = _
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Submodule.coe_smul, coe_wedgeClosed_cartierForm, smul_twist]
    rfl
  rw [hcl, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, map_smul, exteriorPower_basis_eq hb, inverseCartier_ιMulti_D]
  rfl

omit hb in
variable (t b) in
/-- `cartierRep` as an additive map. -/
def cartierRepHom (i : ℕ) : ⋀[B]^i (Ω[B⁄A]) →+ ⋀[B]^i (Ω[B⁄A]) where
  toFun := cartierRep p A t b i
  map_zero' := cartierRep_zero p i
  map_add' := cartierRep_add p i

/-- **Every form projects into the image of `cartierRep`.** -/
theorem exists_projList_eq_cartierRep (hF : IsFrobeniusCoordinates p B t) (i : ℕ)
    (x : ⋀[B]^i (Ω[B⁄A])) :
    ∃ ω, projList p A t b (List.finRange n) i x = cartierRep p A t b i ω := by
  classical
  choose c hc using fun s : Set.powersetCard (Fin n) i ↦ hF.2 ((b.exteriorPower i).repr x s)
  have hx : x = ∑ s, ∑ α, spanForm p A t (c s α) (fun j ↦ (α j : ℕ)) (enum s) := by
    conv_lhs => rw [← (b.exteriorPower i).sum_repr x]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← hc s, Finset.sum_smul, exteriorPower_basis_eq hb]
    rfl
  have hproj : projList p A t b (List.finRange n) i x =
      ∑ s, c s (cartierExponent p s) ^ p • cartierBasisForm p A t s := by
    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_sum]
    simp only [projList_spanForm p hb, forall_dvd_iff]
    rw [Finset.sum_ite_eq' Finset.univ (cartierExponent p s), ite_eq_left (Finset.mem_univ _),
      cartierBasisForm_eq_spanForm, spanForm, spanForm, smul_smul, one_pow, one_mul]
  refine ⟨∑ s, c s (cartierExponent p s) • b.exteriorPower i s, ?_⟩
  rw [hproj]
  change _ = cartierRepHom p t b i _
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  exact (cartierRep_smul_basis p _ s).symm

/-- `projList` fixes the image of `cartierRep`. -/
theorem projList_cartierRep (i : ℕ) (ω : ⋀[B]^i (Ω[B⁄A])) :
    projList p A t b (List.finRange n) i (cartierRep p A t b i ω) = cartierRep p A t b i ω := by
  rw [cartierRep, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [projList_pow_char_smul, cartierBasisForm_eq_spanForm, projList_spanForm p hb,
    ite_eq_left ((forall_dvd_iff p s _).2 rfl)]

omit [CharP B p] in
/-- The coefficients of `cartierRep ω`: `c_s^p t_s^{p-1}`. -/
theorem repr_cartierRep (i : ℕ) (ω : ⋀[B]^i (Ω[B⁄A])) (s : Set.powersetCard (Fin n) i) :
    (b.exteriorPower i).repr (cartierRep p A t b i ω) s =
      (b.exteriorPower i).repr ω s ^ p * monomial t (fun j ↦ (cartierExponent p s j : ℕ)) := by
  have h : cartierRep p A t b i ω = ∑ s, ((b.exteriorPower i).repr ω s ^ p *
      monomial t (fun j ↦ (cartierExponent p s j : ℕ))) • b.exteriorPower i s := by
    rw [cartierRep]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [cartierBasisForm_eq_spanForm, spanForm, one_pow, one_mul, smul_smul,
      exteriorPower_basis_eq hb]
  rw [h, Module.Basis.repr_sum_self]

/-- **The Cartier isomorphism for an algebra with Frobenius coordinates**: if `dt₁, …, dtₙ` is a
basis of `Ω[B⁄A]` and the `t^α`, `0 ≤ αⱼ < p`, are a basis of `B` over itself through the
Frobenius, then `C⁻¹ : Ω^i_{B/A} ⟶ H^i(F_*Ω^•_{B/A})` is bijective in every degree `i`. -/
theorem inverseCartier_bijective_of_isFrobeniusCoordinates (hF : IsFrobeniusCoordinates p B t)
    (i : ℕ) : Function.Bijective (inverseCartier p A B i) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    rw [inverseCartier_eq_cohomologyMk_cartierRep p hb, cohomologyMk_eq_zero_iff] at hω
    have hzero : cartierRep p A t b i ω = 0 := by
      cases i with
      | zero => exact (twist_mem_exactForms_zero _).1 hω
      | succ k =>
          obtain ⟨η, hη⟩ := (twist_mem_exactForms_succ _).1 hω
          rw [← projList_cartierRep p hb, ← hη, ← deRhamDifferential_projList]
          obtain ⟨ω', hω'⟩ := exists_projList_eq_cartierRep p hb hF k η
          rw [hω', deRhamDifferential_cartierRep]
    refine (b.exteriorPower i).ext_elem fun s ↦ ?_
    have hc := repr_cartierRep p hb i ω s
    rw [hzero, map_zero, Finsupp.zero_apply] at hc
    have hinj := hF.1 (a₁ := Pi.single (cartierExponent p s) ((b.exteriorPower i).repr ω s))
      (a₂ := 0) (by
        beta_reduce
        rw [Finset.sum_eq_single (cartierExponent p s)]
        · simp [hc.symm, zero_pow (Fact.out : p.Prime).ne_zero]
        · intro α _ hα
          simp [hα, zero_pow (Fact.out : p.Prime).ne_zero]
        · simp)
    simpa using congrFun hinj (cartierExponent p s)
  · intro y
    obtain ⟨z, rfl⟩ := cohomologyMk_surjective p A B i y
    obtain ⟨-, hex⟩ := projList_closed p (List.finRange n) i
      ((twist p).symm (z : twistedForms p A B i))
      ((mem_closedForms _).1 z.2) (t := t) (b := b)
    obtain ⟨ω, hω⟩ := exists_projList_eq_cartierRep p hb hF i
      ((twist p).symm (z : twistedForms p A B i))
    refine ⟨ω, ?_⟩
    rw [inverseCartier_eq_cohomologyMk_cartierRep p hb, eq_comm, cohomologyMk_eq_iff]
    rwa [hω, map_sub, AddEquiv.apply_symm_apply] at hex

end Theorem

end KaehlerDifferential.Cartier

end
