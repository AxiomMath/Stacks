module

public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.NodeExample.FiniteEtale
public import Mathlib.RingTheory.DualNumber

/-!
# The nodal power map is neither flat nor unramified

The squaring map on both branches of the node over `ℚ` has unit different, but it is neither
flat nor unramified, so a unit different does not force either.

## Main results

* `Stacks.Discriminant.NodeExample.powerMap_two_not_flat` and
  `Stacks.Discriminant.NodeExample.powerMap_two_not_formallyUnramified`: the squaring map on
  both branches over `ℚ` is neither flat nor unramified.

## References

* [Stacks Project, Tag 0BWP](https://stacks.math.columbia.edu/tag/0BWP)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant.NodeExample

universe u

variable (k : Type u) [Field k]

/-- A ring map out of the target node with prescribed images of `u` and `v` and given on `ℚ`. -/
private lemma exists_targetNode_hom {C : Type*} [CommRing C] [Algebra ℚ C] (a b : C)
    (h : a * b = 0) :
    ∃ ψ : targetNodeRing ℚ →+* C, ψ (u ℚ) = a ∧ ψ (v ℚ) = b ∧
      ∀ q : ℚ, ψ (algebraMap ℚ (targetNodeRing ℚ) q) = algebraMap ℚ C q := by
  classical
  let g : MvPolynomial Bool ℚ →+* C :=
    MvPolynomial.eval₂Hom (algebraMap ℚ C) (fun i => if i = false then a else b)
  refine ⟨Ideal.Quotient.lift _ g (by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp [g, h]), ?_, ?_, fun q => ?_⟩
  · change (Ideal.Quotient.lift _ g _) (Ideal.Quotient.mk _ (MvPolynomial.X false)) = a
    rw [Ideal.Quotient.lift_mk]
    simp [g]
  · change (Ideal.Quotient.lift _ g _) (Ideal.Quotient.mk _ (MvPolynomial.X true)) = b
    rw [Ideal.Quotient.lift_mk]
    simp [g]
  · change (Ideal.Quotient.lift _ g _) (Ideal.Quotient.mk _ (MvPolynomial.C q)) = _
    rw [Ideal.Quotient.lift_mk]
    simp [g]

private lemma targetNode_v_not_mul_sq (w : targetNodeRing ℚ) :
    v ℚ ≠ (v ℚ) ^ 2 * w := by
  obtain ⟨ψ, -, hψv, -⟩ := exists_targetNode_hom (C := DualNumber ℚ) 0 DualNumber.eps
    (zero_mul _)
  have he2 : (DualNumber.eps : DualNumber ℚ) * DualNumber.eps = 0 := DualNumber.eps_mul_eps
  have he0 : (DualNumber.eps : DualNumber ℚ) ≠ 0 := by
    intro he
    have hs := congrArg TrivSqZeroExt.snd he
    simp [DualNumber.snd_eps] at hs
  exact fun h => he0 (by simpa [map_mul, map_pow, pow_two, hψv, he2] using congrArg ψ h)

/-- Even with equal branch degrees and unit different, the power map is not flat. -/
@[stacks 0BWP "nonflat example"]
theorem powerMap_two_not_flat
    (f : nodeRing ℚ →+* targetNodeRing ℚ)
    (hx : f (x ℚ) = u ℚ ^ 2) (hy : f (y ℚ) = v ℚ ^ 2)
    (hk : ∀ a : ℚ, f (algebraMap ℚ (nodeRing ℚ) a) =
      algebraMap ℚ (targetNodeRing ℚ) a) :
    letI : Algebra (nodeRing ℚ) (targetNodeRing ℚ) := f.toAlgebra
    ¬ Module.Flat (nodeRing ℚ) (targetNodeRing ℚ) := by
  classical
  let A := nodeRing ℚ
  let B := targetNodeRing ℚ
  let : Algebra A B := f.toAlgebra
  intro hflat
  let coeff : Fin 2 → A := fun i => if i = 0 then x ℚ else y ℚ
  let elems : Fin 2 → B := fun i => if i = 0 then v ℚ else u ℚ
  have hleft : (coeff 0) • (elems 0) = 0 := by
    change (x ℚ) • (v ℚ) = 0
    rw [Algebra.smul_def]
    change f (x ℚ) * v ℚ = 0
    rw [hx]
    calc
      (u ℚ) ^ 2 * v ℚ = u ℚ * (u ℚ * v ℚ) := by ring
      _ = 0 := by rw [targetNode_uv_zero, mul_zero]
  have hright : (coeff 1) • (elems 1) = 0 := by
    change (y ℚ) • (u ℚ) = 0
    rw [Algebra.smul_def]
    change f (y ℚ) * u ℚ = 0
    rw [hy]
    calc
      (v ℚ) ^ 2 * u ℚ = v ℚ * (v ℚ * u ℚ) := by ring
      _ = 0 := by rw [mul_comm (v ℚ) (u ℚ), targetNode_uv_zero, mul_zero]
  have hrel : ∑ i : Fin 2, coeff i • elems i = 0 := by
    rw [Fin.sum_univ_two]
    simp [hleft, hright]
  have htriv := Module.Flat.iff_forall_isTrivialRelation.mp hflat hrel
  rcases htriv with ⟨l, a, z, ha, hcoef⟩
  have hsyzygy (j : Fin l) :
      ∃ c d : A, a 0 j = y ℚ * c ∧ a 1 j = x ℚ * d := by
    have hj : x ℚ * a 0 j + y ℚ * a 1 j = 0 := by
      simpa [coeff, Fin.sum_univ_two, mul_comm] using hcoef j
    exact node_coordinate_syzygy ℚ (a 0 j) (a 1 j) hj
  choose c d hac had using hsyzygy
  have hvdiv : v ℚ = (v ℚ) ^ 2 * (∑ j : Fin l, c j • z j) := by
    let w : B := ∑ j : Fin l, algebraMap A B (c j) * z j
    calc
      v ℚ = ∑ j : Fin l, a 0 j • z j := by simpa [elems] using ha 0
      _ = ∑ j : Fin l, algebraMap A B (a 0 j) * z j := by
        simp [A, B, Algebra.smul_def]
      _ = ∑ j : Fin l,
          algebraMap A B (y ℚ) * (algebraMap A B (c j) * z j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hac j, map_mul]
        ring
      _ = algebraMap A B (y ℚ) * w := by
        dsimp [w]
        rw [Finset.mul_sum]
      _ = (v ℚ) ^ 2 * (∑ j : Fin l, c j • z j) := by
        rw [show algebraMap A B (y ℚ) = f (y ℚ) by rfl, hy]
        dsimp [w]
        simp [A, B, Algebra.smul_def]
  exact targetNode_v_not_mul_sq _ hvdiv

/-- The same map is not unramified, despite its unit different. -/
@[stacks 0BWP "not unramified example"]
theorem powerMap_two_not_formallyUnramified
    (f : nodeRing ℚ →+* targetNodeRing ℚ)
    (hx : f (x ℚ) = u ℚ ^ 2) (hy : f (y ℚ) = v ℚ ^ 2)
    (hk : ∀ a : ℚ, f (algebraMap ℚ (nodeRing ℚ) a) =
      algebraMap ℚ (targetNodeRing ℚ) a) :
    ¬ RingHom.FormallyUnramified f := by
  classical
  let C := DualNumber ℚ
  let e : C := DualNumber.eps
  let I : Ideal C := Ideal.span {e}
  have he2 : e * e = 0 := DualNumber.eps_mul_eps
  have hI : I ^ 2 = ⊥ := by
    change (Ideal.span {e}) ^ 2 = ⊥
    rw [Ideal.span_singleton_pow, pow_two, he2]
    simp
  obtain ⟨ψ₀, hψ₀u, hψ₀v, hψ₀k⟩ := exists_targetNode_hom (C := C) 0 0 (zero_mul _)
  obtain ⟨ψ₁, hψ₁u, hψ₁v, hψ₁k⟩ := exists_targetNode_hom (C := C) e 0 (mul_zero _)
  have hcomp : ψ₀.comp f = ψ₁.comp f := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change ψ₀ (f (algebraMap ℚ (nodeRing ℚ) a)) =
        ψ₁ (f (algebraMap ℚ (nodeRing ℚ) a))
      rw [hk a, hψ₀k, hψ₁k]
    · intro i
      fin_cases i
      · change ψ₀ (f (x ℚ)) = ψ₁ (f (x ℚ))
        rw [hx, map_pow, map_pow, hψ₀u, hψ₁u]
        simp only [pow_two, he2, zero_mul]
      · change ψ₀ (f (y ℚ)) = ψ₁ (f (y ℚ))
        rw [hy, map_pow, map_pow, hψ₀v, hψ₁v]
  let : Algebra (nodeRing ℚ) (targetNodeRing ℚ) := f.toAlgebra
  let : Algebra (nodeRing ℚ) C := (ψ₀.comp f).toAlgebra
  let φ₀ : targetNodeRing ℚ →ₐ[nodeRing ℚ] C := AlgHom.mk' ψ₀ (by
    intro a b
    simp only [Algebra.smul_def, map_mul]
    change ψ₀ (f a) * ψ₀ b = (ψ₀.comp f) a * ψ₀ b
    rfl)
  let φ₁ : targetNodeRing ℚ →ₐ[nodeRing ℚ] C := AlgHom.mk' ψ₁ (by
    intro a b
    simp only [Algebra.smul_def, map_mul]
    change ψ₁ (f a) * ψ₁ b = (ψ₀.comp f) a * ψ₁ b
    rw [← RingHom.comp_apply, hcomp])
  have hquotRing : (Ideal.Quotient.mk I).comp ψ₀ =
      (Ideal.Quotient.mk I).comp ψ₁ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change (Ideal.Quotient.mk I) (ψ₀ (algebraMap ℚ (targetNodeRing ℚ) a)) =
        (Ideal.Quotient.mk I) (ψ₁ (algebraMap ℚ (targetNodeRing ℚ) a))
      rw [hψ₀k, hψ₁k]
    · intro i
      cases i with
      | false =>
        change (Ideal.Quotient.mk I) (ψ₀ (u ℚ)) =
          (Ideal.Quotient.mk I) (ψ₁ (u ℚ))
        rw [hψ₀u, hψ₁u, Ideal.Quotient.eq]
        simpa only [zero_sub] using I.neg_mem
          (Ideal.subset_span (by simp [e]) : e ∈ I)
      | true =>
        change (Ideal.Quotient.mk I) (ψ₀ (v ℚ)) =
          (Ideal.Quotient.mk I) (ψ₁ (v ℚ))
        rw [hψ₀v, hψ₁v]
  have hquot : (Ideal.Quotient.mkₐ (nodeRing ℚ) I).comp φ₀ =
      (Ideal.Quotient.mkₐ (nodeRing ℚ) I).comp φ₁ := by
    apply AlgHom.ext
    intro b
    change ((Ideal.Quotient.mk I).comp ψ₀) b =
      ((Ideal.Quotient.mk I).comp ψ₁) b
    exact congrArg (fun g : targetNodeRing ℚ →+* C ⧸ I => g b) hquotRing
  intro hfu
  have hinj := (Algebra.FormallyUnramified.iff_comp_injective
    (R := nodeRing ℚ) (A := targetNodeRing ℚ)).mp hfu
  have hφ : φ₀ = φ₁ := hinj I hI hquot
  have hu := congrArg (fun φ : targetNodeRing ℚ →ₐ[nodeRing ℚ] C => φ (u ℚ)) hφ
  have : (0 : C) = e := by
    change ψ₀ (u ℚ) = ψ₁ (u ℚ) at hu
    rwa [hψ₀u, hψ₁u] at hu
  have he_ne : e ≠ 0 := by
    change TrivSqZeroExt.inr (1 : ℚ) ≠ TrivSqZeroExt.inr 0
    intro h
    exact one_ne_zero (TrivSqZeroExt.inr_injective h)
  exact he_ne this.symm

end Stacks.Discriminant.NodeExample

end
