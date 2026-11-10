module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixReduction

/-!
# Invariants of an open subgroup of inertia as invariants of inertia in a permutation twist

Let `W : G → GL_m(K)`, `X` a finite `G`-set with base point `x₀`, `I ⊆ G` a subgroup, and `Y`
a nonzero vector fixed by `W(h)` for every `h ∈ I` fixing `x₀`.  The vector `ξ` of `K^m ⊗ K[X]`
with `ξ(i x₀) = W(i) Y` for `i ∈ I` and `ξ(x) = 0` off the orbit `I x₀` is well defined, nonzero,
and fixed by `(W ⊗ K[X])(I)`; if `F` fixes `x₀`, normalizes `I`, and `W(F) Y = c Y`, then
`(W ⊗ K[X])(F) ξ = c ξ`.  For `X = G/N`, `N` an open normal subgroup, this turns local invariants
of the subgroup `I ∩ N` into local invariants of `I` itself in a representation of `G`.

## Main results

* `Stacks.EtaleCohomology.kroneckerMonoidHom_permMatrix_mulVec`: `(A ⊗ P_g) v` in coordinates.
* `Stacks.EtaleCohomology.exists_permutationTwist_vector`: the vector `ξ` exists, is nonzero, is
  fixed by `(W ⊗ K[X])(I)`, and satisfies `(W ⊗ K[X])(F) ξ = c ξ` for `F` as above.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [DecidableEq X] {n m : ℕ}
  (e : Fin n ≃ X) {K : Type*} [CommRing K]

/-- **`(A ⊗ P_g) v`, coordinatewise**: the `(a, x)` entry is `(A v(·, g⁻¹ x))_a`. -/
public theorem kroneckerMonoidHom_permMatrix_mulVec (A : Matrix (Fin m) (Fin m) K) (g : G)
    (v : Fin (m * n) → K) (a : Fin m) (i : Fin n) :
    (kroneckerMonoidHom (A, permMatrix e K g) *ᵥ v) (finProdFinEquiv (a, i)) =
      (A *ᵥ fun b => v (finProdFinEquiv (b, e.symm (g⁻¹ • e i)))) a := by
  classical
  simp only [kroneckerMonoidHom_apply, Matrix.mulVec, dotProduct, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, permMatrix, Matrix.of_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (e.symm (g⁻¹ • e i))]
  · simp
  · intro j _ hj
    have : e i ≠ g • e j := fun h' => hj (by rw [h', inv_smul_smul, Equiv.symm_apply_apply])
    simp [this]
  · simp

/-- Applying `W g` after `W h` to a vector is applying `W (g * h)`. -/
private theorem mulVec_mulVec_units {m : ℕ} (W : G →* GL (Fin m) K) (g h : G)
    (v : Fin m → K) :
    ((W g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        (((W h : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v) =
      ((W (g * h) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]

/-- **The permutation twist of an invariant vector.**  If `Y ≠ 0` is fixed by `W(h)` for the
`h ∈ I` fixing `x₀`, there is a nonzero `ξ` fixed by `(W ⊗ P)(I)`, and every `F` fixing `x₀` and
normalizing `I` with `W(F) Y = c Y` satisfies `(W ⊗ P)(F) ξ = c ξ`. -/
public theorem exists_permutationTwist_vector (W : G →* GL (Fin m) K) (I : Subgroup G) (x₀ : X)
    (Y : Fin m → K) (hY : Y ≠ 0)
    (hYfix : ∀ h ∈ I, h • x₀ = x₀ → ((W h : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ Y = Y) :
    ∃ ξ : Fin (m * n) → K, ξ ≠ 0 ∧
      (∀ g ∈ I, ((kroneckerRepresentation W (permMatrixRepresentation e K) g :
        GL (Fin (m * n)) K) : Matrix (Fin (m * n)) (Fin (m * n)) K) *ᵥ ξ = ξ) ∧
      ∀ (F : G) (c : K), F • x₀ = x₀ → F ∈ Subgroup.normalizer (I : Set G) →
        ((W F : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ Y = c • Y →
        ((kroneckerRepresentation W (permMatrixRepresentation e K) F :
          GL (Fin (m * n)) K) : Matrix (Fin (m * n)) (Fin (m * n)) K) *ᵥ ξ = c • ξ := by
  classical
  let comp : X → Fin m → K := fun x =>
    if h : ∃ i ∈ I, i • x₀ = x then ((W h.choose : GL (Fin m) K) : Matrix _ _ K) *ᵥ Y else 0
  have hcomp : ∀ i ∈ I, comp (i • x₀) = ((W i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ Y := by
    intro i hi
    have hex : ∃ j ∈ I, j • x₀ = i • x₀ := ⟨i, hi, rfl⟩
    simp only [comp, dite_eq_left hex]
    obtain ⟨hjI, hj⟩ := hex.choose_spec
    set j := hex.choose
    have hji : i⁻¹ * j ∈ I := I.mul_mem (I.inv_mem hi) hjI
    have hfix : (i⁻¹ * j) • x₀ = x₀ := by rw [mul_smul, hj, inv_smul_smul]
    calc ((W j : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ Y
        = ((W i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
            (((W (i⁻¹ * j) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ Y) := by
          rw [mulVec_mulVec_units, mul_inv_cancel_left]
      _ = _ := by rw [hYfix _ hji hfix]
  have hcomp0 : ∀ x, (¬ ∃ i ∈ I, i • x₀ = x) → comp x = 0 := fun x hx => by
    simp only [comp, dite_eq_right hx]
  let ξ : Fin (m * n) → K := fun p => comp (e (finProdFinEquiv.symm p).2) (finProdFinEquiv.symm p).1
  have hξ : ∀ a i, ξ (finProdFinEquiv (a, i)) = comp (e i) a := fun a i => by
    simp only [ξ, Equiv.symm_apply_apply]
  have hact : ∀ g a i, (((kroneckerRepresentation W (permMatrixRepresentation e K) g :
      GL (Fin (m * n)) K) : Matrix (Fin (m * n)) (Fin (m * n)) K) *ᵥ ξ) (finProdFinEquiv (a, i)) =
      (((W g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ comp (g⁻¹ • e i)) a := fun g a i => by
    rw [show ((kroneckerRepresentation W (permMatrixRepresentation e K) g :
      GL (Fin (m * n)) K) : Matrix (Fin (m * n)) (Fin (m * n)) K) =
        kroneckerMonoidHom (((W g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K),
          permMatrix e K g) from rfl, kroneckerMonoidHom_permMatrix_mulVec]
    congr 1
    funext b
    rw [hξ, Equiv.apply_symm_apply]
  have hext : ∀ v w : Fin (m * n) → K, (∀ a i, v (finProdFinEquiv (a, i)) =
      w (finProdFinEquiv (a, i))) → v = w := fun v w h => by
    funext p
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective p
    exact h a i
  refine ⟨ξ, ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := Function.ne_iff.1 hY
    intro h0
    have := congrFun h0 (finProdFinEquiv (b, e.symm x₀))
    rw [hξ, Equiv.apply_symm_apply, show x₀ = (1 : G) • x₀ from (one_smul G x₀).symm,
      hcomp 1 I.one_mem, map_one, Units.val_one, Matrix.one_mulVec] at this
    exact hb this
  · intro g hg
    refine hext _ _ fun a i => ?_
    rw [hact, hξ]
    by_cases hx : ∃ j ∈ I, j • x₀ = e i
    · obtain ⟨j, hj, hjx⟩ := hx
      rw [← hjx, ← mul_smul, hcomp _ (I.mul_mem (I.inv_mem hg) hj), hcomp _ hj,
        mulVec_mulVec_units, mul_inv_cancel_left]
    · have hx' : ¬ ∃ j ∈ I, j • x₀ = g⁻¹ • e i := by
        rintro ⟨j, hj, hjx⟩
        exact hx ⟨g * j, I.mul_mem hg hj, by rw [mul_smul, hjx, smul_inv_smul]⟩
      rw [hcomp0 _ hx, hcomp0 _ hx', Matrix.mulVec_zero]
  · intro F c hFx hFN hFY
    refine hext _ _ fun a i => ?_
    rw [hact, Pi.smul_apply, hξ]
    by_cases hx : ∃ j ∈ I, j • x₀ = e i
    · obtain ⟨j, hj, hjx⟩ := hx
      have hj' : F⁻¹ * j * F ∈ I := (Subgroup.mem_normalizer_iff''.1 hFN j).1 hj
      rw [← hjx, show F⁻¹ • j • x₀ = (F⁻¹ * j * F) • x₀ by rw [mul_smul, mul_smul, hFx],
        hcomp _ hj', hcomp _ hj,
        mulVec_mulVec_units,
        show F * (F⁻¹ * j * F) = j * F by group, ← mulVec_mulVec_units, hFY,
        Matrix.mulVec_smul, Pi.smul_apply]
    · have hx' : ¬ ∃ j ∈ I, j • x₀ = F⁻¹ • e i := by
        rintro ⟨j, hj, hjx⟩
        refine hx ⟨F * j * F⁻¹, (Subgroup.mem_normalizer_iff.1 hFN j).1 hj, ?_⟩
        rw [mul_smul, mul_smul, show F⁻¹ • x₀ = x₀ by rw [inv_smul_eq_iff, hFx], hjx,
          smul_inv_smul]
      rw [hcomp0 _ hx, hcomp0 _ hx', Matrix.mulVec_zero, Pi.zero_apply, smul_zero]

end Stacks.EtaleCohomology

end
