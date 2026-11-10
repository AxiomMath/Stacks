module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.EndomorphismDegree
public import StacksFrontier.Algebra.Polynomial.MultiplicativeNorm

/-!
# The degree of a polynomial in an endomorphism of an abelian variety

For a commutative group object `G` of a cartesian monoidal category, the endomorphisms of `G`
which are homomorphisms form a ring (addition is the group law of `G ⟶ G`, multiplication is
composition). This file models that ring by the subring `Stacks.Groupoids.postcompSubring G` of
postcomposition maps in `AddMonoid.End (Additive (G ⟶ G))`, and defines, for a homomorphism
`α : G ⟶ G` and `R ∈ ℤ[X]`, the morphism `R(α)` (`Stacks.Groupoids.endPolyEval`).

For an abelian variety `A` of dimension `g` over a field `k`, the function `R ↦ deg R(α)` on
`ℤ[X]` is multiplicative (`Stacks.Groupoids.endDegree_comp`), equal to `c ^ (2 g)` on constants,
and polynomial in the coefficients of `R`
(`Stacks.Groupoids.exists_mvPolynomial_endDegree_prod_zpow`), so it is the norm form of the monic
polynomial `χ_α(t) = deg (α - t)` of degree `2 g` (`Stacks.Polynomial.exists_eq_normForm`):
`deg R(α) = ∏ R(β_i)` over the roots `β_i` of `χ_α` ([Mumford, *Abelian varieties*, §19,
Theorem 4], first half).

## Main definitions

* `Stacks.Groupoids.postcompSubring` — the ring of postcomposition endomorphisms.
* `Stacks.Groupoids.endPolyEval` — `R(α)` for `R ∈ ℤ[X]` and a homomorphism `α : G ⟶ G`.

## Main results

* `Stacks.Groupoids.endPolyEval_mul`, `endPolyEval_add`, `endPolyEval_C`, `endPolyEval_X` — the
  ring structure.
* `Stacks.Groupoids.endDegree_zpow_id_eq_pow` — `deg [c] = c ^ (2 g)` for all `c ∈ ℤ`.
* `Stacks.Groupoids.exists_endDegree_endPolyEval_eq_normForm` — `deg R(α) = N(R mod χ_α)`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

namespace Stacks.Groupoids

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (G : C) [GrpObj G] [IsCommMonObj G]

/-- The postcomposition endomorphisms of the commutative group `G ⟶ G`: the additive maps
`E` of `Additive (G ⟶ G)` with `E x = x ≫ E 𝟙` for all `x`. They form a subring of
`AddMonoid.End (Additive (G ⟶ G))`, a model of the endomorphism ring of `G`
(multiplication is composition in the opposite order). -/
def postcompSubring : Subring (AddMonoid.End (Additive (G ⟶ G))) where
  carrier := {E | ∀ y : Additive (G ⟶ G), (E y).toMul = y.toMul ≫ (E (.ofMul (𝟙 G))).toMul}
  mul_mem' {E F} hE hF y := by
    change (E (F y)).toMul = y.toMul ≫ (E (F (.ofMul (𝟙 G)))).toMul
    rw [hE (F y), hF y, hE (F _), hF (.ofMul (𝟙 G))]
    simp
  one_mem' y := by simp
  add_mem' {E F} hE hF y := by
    change (E y).toMul * (F y).toMul = y.toMul ≫ ((E (.ofMul (𝟙 G))).toMul *
      (F (.ofMul (𝟙 G))).toMul)
    rw [hE, hF, MonObj.comp_mul]
  zero_mem' y := by
    change (1 : G ⟶ G) = y.toMul ≫ 1
    rw [MonObj.comp_one]
  neg_mem' {E} hE y := by
    change ((E y).toMul)⁻¹ = y.toMul ≫ ((E (.ofMul (𝟙 G))).toMul)⁻¹
    rw [hE, GrpObj.comp_inv]

variable {G}

/-- The morphism `G ⟶ G` of an element of `postcompSubring G`: its value at `𝟙 G`. -/
def postcompHom (E : postcompSubring G) : G ⟶ G := (E.1 (.ofMul (𝟙 G))).toMul

/-- An element `E` of `postcompSubring G` acts on `x : G ⟶ G` as postcomposition with
`postcompHom E`. -/
theorem postcompHom_apply (E : postcompSubring G) (x : G ⟶ G) :
    (E.1 (.ofMul x)).toMul = x ≫ postcompHom E := E.2 (.ofMul x)

/-- `postcompHom` sends a product to the composite in the opposite order. -/
theorem postcompHom_mul (E F : postcompSubring G) :
    postcompHom (E * F) = postcompHom F ≫ postcompHom E :=
  E.2 (F.1 (.ofMul (𝟙 G)))

/-- `postcompHom` sends a sum to the product in the group `G ⟶ G`. -/
theorem postcompHom_add (E F : postcompSubring G) :
    postcompHom (E + F) = postcompHom E * postcompHom F := rfl

/-- `postcompHom` sends an integer multiple to the corresponding power in `G ⟶ G`. -/
theorem postcompHom_zsmul (n : ℤ) (E : postcompSubring G) :
    postcompHom (n • E) = postcompHom E ^ n := rfl

/-- `postcompHom` sends `1` to the identity `𝟙 G`. -/
theorem postcompHom_one : postcompHom (1 : postcompSubring G) = 𝟙 G := rfl

/-- `postcompHom` sends the integer `n` to `(𝟙 G) ^ n`. -/
theorem postcompHom_intCast (n : ℤ) : postcompHom (n : postcompSubring G) = (𝟙 G) ^ n := by
  rw [← zsmul_one, postcompHom_zsmul, postcompHom_one]

/-- `postcompHom` as an additive map to `Additive (G ⟶ G)`. -/
def postcompHomAdd : postcompSubring G →+ Additive (G ⟶ G) where
  toFun E := .ofMul (postcompHom E)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Postcomposition with a homomorphism `α : G ⟶ G` of group objects, as an additive map of
`Additive (G ⟶ G)`. -/
def postcompAddHom (α : G ⟶ G) [IsMonHom α] : AddMonoid.End (Additive (G ⟶ G)) where
  toFun x := .ofMul (x.toMul ≫ α)
  map_zero' := by
    change (1 : G ⟶ G) ≫ α = 1
    exact MonObj.one_comp α
  map_add' x y := by
    change (x.toMul * y.toMul) ≫ α = x.toMul ≫ α * y.toMul ≫ α
    exact MonObj.mul_comp _ _ α

/-- Postcomposition with a homomorphism `α : G ⟶ G`, as an element of `postcompSubring G`. -/
def postcompOf (α : G ⟶ G) [IsMonHom α] : postcompSubring G :=
  ⟨postcompAddHom α, fun y => by
    change y.toMul ≫ α = y.toMul ≫ 𝟙 G ≫ α
    rw [Category.id_comp]⟩

/-- The morphism of postcomposition with `α` is `α`. -/
theorem postcompHom_postcompOf (α : G ⟶ G) [IsMonHom α] : postcompHom (postcompOf α) = α :=
  Category.id_comp α

/-- **A polynomial in an endomorphism of a commutative group object.** For a homomorphism
`α : G ⟶ G` and `R = ∑ r_k X^k ∈ Polynomial ℤ`, the morphism `R(α) = ∏ (α^{∘k})^{r_k}` (product in
the commutative group `G ⟶ G`, `α^{∘k}` the `k`-fold composite). -/
def endPolyEval (α : G ⟶ G) [IsMonHom α] (R : Polynomial ℤ) : G ⟶ G :=
  postcompHom (aeval (postcompOf α) R)

/-- `(R * S)(α) = S(α) ≫ R(α)`. -/
theorem endPolyEval_mul (α : G ⟶ G) [IsMonHom α] (R S : Polynomial ℤ) :
    endPolyEval α (R * S) = endPolyEval α S ≫ endPolyEval α R := by
  simp [endPolyEval, postcompHom_mul]

/-- `(R + S)(α) = R(α) * S(α)`, the product taken in the group `G ⟶ G`. -/
theorem endPolyEval_add (α : G ⟶ G) [IsMonHom α] (R S : Polynomial ℤ) :
    endPolyEval α (R + S) = endPolyEval α R * endPolyEval α S := by
  simp [endPolyEval, postcompHom_add]

/-- A constant polynomial `c` evaluates to `(𝟙 G) ^ c`. -/
theorem endPolyEval_C (α : G ⟶ G) [IsMonHom α] (c : ℤ) :
    endPolyEval α (Polynomial.C c) = (𝟙 G) ^ c := by
  simp [endPolyEval, postcompHom_intCast]

/-- The polynomial `X` evaluates to `α`. -/
theorem endPolyEval_X (α : G ⟶ G) [IsMonHom α] : endPolyEval α Polynomial.X = α := by
  simp [endPolyEval, postcompHom_postcompOf]

/-- `(X - n)(α) = α * ((𝟙 G) ^ n)⁻¹`. -/
theorem endPolyEval_X_sub_C (α : G ⟶ G) [IsMonHom α] (n : ℤ) :
    endPolyEval α (Polynomial.X - Polynomial.C n) = α * ((𝟙 G) ^ n)⁻¹ := by
  rw [sub_eq_add_neg, endPolyEval_add, endPolyEval_X, ← Polynomial.C_neg, endPolyEval_C, zpow_neg]

/-- Postcomposition with `R(α)` is `R` applied to postcomposition with `α`. -/
theorem comp_endPolyEval (α : G ⟶ G) [IsMonHom α] (R : Polynomial ℤ) (x : G ⟶ G) :
    x ≫ endPolyEval α R = ((aeval (postcompOf α) R).1 (.ofMul x)).toMul :=
  (postcompHom_apply _ x).symm

/-- For `R = ∑ r_k X^k`, `R(α)` is the product of the `(X^k)(α) ^ r_k` in the group `G ⟶ G`. -/
theorem endPolyEval_ofCoeffs (α : G ⟶ G) [IsMonHom α] {m : ℕ} (r : Fin (m + 1) → ℤ) :
    endPolyEval α (Stacks.Polynomial.ofCoeffs r) =
      ∏ k : Fin (m + 1), endPolyEval α (Polynomial.X ^ (k : ℕ)) ^ r k := by
  have h := map_sum (postcompHomAdd (G := G)) (fun k => aeval (postcompOf α)
    (Polynomial.C (r k) * Polynomial.X ^ (k : ℕ))) Finset.univ
  simp only [Stacks.Polynomial.ofCoeffs, endPolyEval, map_sum]
  change (postcompHomAdd (∑ k, _)).toMul = _
  rw [h, toMul_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_one_mul]
  rfl

end General

section AbelianVariety

universe u

variable {k : Type u} [Field k] (A : Over (AlgebraicGeometry.Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- `deg [c] = c ^ (2 g)` for every integer `c`, `0` included: the degree of `[c]` is a
polynomial in `c` (`Stacks.Groupoids.exists_mvPolynomial_endDegree_prod_zpow`) which agrees with
`c ^ (2 g)` away from `0` (`Stacks.Groupoids.endDegree_zpow_id`). -/
theorem endDegree_zpow_id_eq_pow (c : ℤ) :
    (endDegree A ((𝟙 A : A ⟶ A) ^ c) : ℤ) = c ^ (2 * abelianVarietyDimension A) := by
  obtain ⟨P, -, hP⟩ := exists_mvPolynomial_endDegree_prod_zpow A (fun _ : Fin 1 => 𝟙 A)
  set F : Polynomial ℚ := MvPolynomial.aeval (fun _ => Polynomial.X) P
  have hF : ∀ t : ℤ, F.eval (t : ℚ) = (endDegree A ((𝟙 A : A ⟶ A) ^ t) : ℚ) := fun t => by
    have := hP (fun _ => t)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton] at this
    rw [this, ← Polynomial.coe_aeval_eq_eval]
    change (Polynomial.aeval (t : ℚ)).comp (MvPolynomial.aeval fun _ => Polynomial.X) P = _
    rw [MvPolynomial.comp_aeval]
    simp [MvPolynomial.aeval_eq_eval]
  have hX : F = Polynomial.X ^ (2 * abelianVarietyDimension A) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((n + 1 : ℕ) : ℚ)) (fun a b h => by simpa using h) fun n => ?_)
    have h := hF (n + 1)
    rw [endDegree_zpow_id A _ (by lia)] at h
    simp only [Set.mem_ofPred_eq, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast at h ⊢
    rw [h]
    norm_cast
  have h := hF c
  rw [hX, Polynomial.eval_pow, Polynomial.eval_X] at h
  exact_mod_cast h.symm

/-- **The degree of `R(α)` is the norm form of `χ_α(t) = deg (α - t)`** (Mumford, *Abelian
varieties*, §19, Theorem 4). For a homomorphism `α : A ⟶ A` of an abelian variety `A` of
dimension `g` over `k` there is a monic `χ ∈ ℚ[X]` of degree `2 g` with `χ(n) = deg (α - n)`
for all integers `n` and `deg R(α) = N_{(ℚ[X]/χ)/ℚ}(R)` for every `R ∈ ℤ[X]`; here `R(α)` is
`Stacks.Groupoids.endPolyEval α R`, and the group law of `A ⟶ A` is written multiplicatively. -/
theorem exists_endDegree_endPolyEval_eq_normForm (α : A ⟶ A) [IsMonHom α] :
    ∃ χ : Polynomial ℚ, χ.Monic ∧ χ.natDegree = 2 * abelianVarietyDimension A ∧
      (∀ n : ℤ, χ.eval (n : ℚ) = endDegree A (α * ((𝟙 A) ^ n)⁻¹)) ∧
      ∀ R : Polynomial ℤ, (endDegree A (endPolyEval α R) : ℚ) =
        Stacks.Polynomial.normForm χ R := by
  obtain ⟨χ, hmon, hdeg, hev, hR⟩ := Stacks.Polynomial.exists_eq_normForm
    (D := fun R => (endDegree A (endPolyEval α R) : ℤ)) (N := 2 * abelianVarietyDimension A)
    (fun R S => by simp only [endPolyEval_mul, endDegree_comp, Nat.cast_mul, mul_comm])
    (fun c => by simp only [endPolyEval_C, endDegree_zpow_id_eq_pow])
    (even_two_mul _)
    (fun m => by
      obtain ⟨P, -, hP⟩ := exists_mvPolynomial_endDegree_prod_zpow A
        (fun k : Fin (m + 1) => endPolyEval α (Polynomial.X ^ (k : ℕ)))
      exact ⟨P, fun r => by simpa only [endPolyEval_ofCoeffs, Int.cast_natCast] using hP r⟩)
  refine ⟨χ, hmon, hdeg, fun n => ?_, fun R => ?_⟩
  · rw [hev n, endPolyEval_X_sub_C]
    simp
  · rw [← hR R]
    simp

end AbelianVariety

end Stacks.Groupoids
