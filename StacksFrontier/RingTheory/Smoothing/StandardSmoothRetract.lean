module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothPresentation
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension

/-!
# Smooth algebras are retracts of standard smooth algebras

A smooth `R`-algebra `A` need not be standard smooth: it is only standard smooth locally on
`Spec(A)`. This file shows that the defect disappears after enlarging `A`: there is a smooth
`A`-algebra `B` which is *standard smooth* over `R` and which admits an `R`-algebra retraction
`B → A`.

## Main results

* `Stacks.Smoothing.exists_smooth_isStandardSmooth_retraction`: a smooth `R`-algebra `A` admits a
  smooth `A`-algebra `B` with an `A`-algebra retraction `B → A` such that `B` is standard smooth
  over `R`, Stacks 07CH.

## Implementation notes

One piece of general theory is proved along the way.

* `Algebra.Presentation.addGenerators` adjoins to a presentation
  `A = R[x_1, …, x_n]/(f_1, …, f_c)` a family of *redundant* generators `w_k ∈ A`, together with
  the relations `z_k - w̃_k` expressing them in terms of the old ones. The resulting presentation
  has the same algebra but a larger Jacobian matrix, and this is what makes the Jacobian a unit
  in the construction below.

The proof of 07CH itself departs from the source. Stacks 07CG supplies a smooth `A`-algebra `C`
with a retraction which is a relative global complete intersection over `R`, so that it has a
presentation `C = R[x_1, …, x_n]/(f_1, …, f_c)` whose conormal module is free on the classes of
the relations (Lemma 00SV (3)). Smoothness of `R → C` splits the naive cotangent complex, which in
that basis is the matrix identity `∑_i (∂f_j/∂x_i) c_{iℓ} = δ_{jℓ}` of the source. The source then
puts `B' = C[y_1, …, y_c]`, shows that `R[z_1, …, z_n] → B'`, `z_i ↦ x_i - ∑_j c_{ij} y_j`, is
étale after inverting an element of `1 + (y_1, …, y_c)` — through unramifiedness, the fibrewise
criterion for flatness and the structure theorem 00U9 for étale maps — and concludes.

Here the étale detour is replaced by a direct determinant computation. Adjoining to the
presentation of `B' = C[y_1, …, y_c]` over `R` the `n` redundant generators
`x_i - ∑_j c_{ij} y_j` gives a presentation of `B'` by `n + c + n` variables and `n + c`
relations, and pairing the `n` new relations with the variables `x_i` and the `c` old relations
with the variables `y_j` makes it presubmersive. Modulo `(y_1, …, y_c)` its Jacobi matrix is
`[[-1, (∂f_j/∂x_i)], [(c_{iℓ}), 0]]`, whose determinant is `(-1)^n det (∑_i (∂f_j/∂x_i) c_{iℓ})`
`= (-1)^n` by the splitting identity. So the Jacobian `g` of the presentation is a unit in
`C = B'/(y_1, …, y_c)`, the localization `B = B'_g` is standard smooth over `R`, and the
retraction `B' → C`, `y_j ↦ 0`, extends to `B → C`.

## References

* [Stacks 07CH](https://stacks.math.columbia.edu/tag/07CH), Lemma 16.3.4
* [Stacks 07CG](https://stacks.math.columbia.edu/tag/07CG), Lemma 16.3.3
-/

@[expose] public section

universe u v

open MvPolynomial

namespace Algebra.Presentation

section AddGenerators

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ ρ : Type*}

/-- The auxiliary surjection `R[z_k, x_i] → R[x_i]` sending the new variable `z_k` to the
polynomial `w k` in the old variables. -/
private noncomputable def addGenAux (w : ρ → MvPolynomial ι R) :
    MvPolynomial (ρ ⊕ ι) R →ₐ[R] MvPolynomial ι R :=
  aeval (Sum.elim w X)

private lemma addGenAux_X_inl (w : ρ → MvPolynomial ι R) (k : ρ) :
    addGenAux w (X (Sum.inl k)) = w k := by simp [addGenAux]

private lemma addGenAux_X_inr (w : ρ → MvPolynomial ι R) (i : ι) :
    addGenAux w (X (Sum.inr i)) = X i := by simp [addGenAux]

private lemma addGenAux_rename (w : ρ → MvPolynomial ι R) (p : MvPolynomial ι R) :
    addGenAux w (rename Sum.inr p) = p := by
  rw [addGenAux, aeval_rename]
  simp

private lemma addGenAux_surjective (w : ρ → MvPolynomial ι R) :
    Function.Surjective (addGenAux w) :=
  fun p ↦ ⟨rename Sum.inr p, addGenAux_rename w p⟩

variable (P : Presentation R S ι σ) (w : ρ → MvPolynomial ι R)

/-- The relations of `Algebra.Presentation.addGenerators`: the old ones, renamed, preceded by the
relations `z_k - w_k` which express the new generators through the old variables. -/
noncomputable def addGeneratorsRelation : ρ ⊕ σ → MvPolynomial (ρ ⊕ ι) R :=
  Sum.elim (fun k ↦ X (Sum.inl k) - rename Sum.inr (w k))
    (fun j ↦ rename Sum.inr (P.relation j))

/-- The relation of `Algebra.Presentation.addGeneratorsRelation` indexed by a new generator
`z_k` is `z_k - w_k`. -/
@[simp] lemma addGeneratorsRelation_inl (k : ρ) :
    P.addGeneratorsRelation w (Sum.inl k) = X (Sum.inl k) - rename Sum.inr (w k) := rfl

/-- The relation of `Algebra.Presentation.addGeneratorsRelation` indexed by an old relation
is that relation, renamed into the enlarged set of variables. -/
@[simp] lemma addGeneratorsRelation_inr (j : σ) :
    P.addGeneratorsRelation w (Sum.inr j) = rename Sum.inr (P.relation j) := rfl

private lemma sub_rename_addGenAux_mem (p : MvPolynomial (ρ ⊕ ι) R) :
    p - rename Sum.inr (addGenAux w p) ∈
      Ideal.span (Set.range fun k : ρ ↦
        (X (Sum.inl k) - rename Sum.inr (w k) : MvPolynomial (ρ ⊕ ι) R)) := by
  set J := Ideal.span (Set.range fun k : ρ ↦
    (X (Sum.inl k) - rename Sum.inr (w k) : MvPolynomial (ρ ⊕ ι) R)) with hJ
  induction p using MvPolynomial.induction_on with
  | C a => simp [addGenAux]
  | add p q hp hq =>
      simpa only [map_add, add_sub_add_comm] using Ideal.add_mem J hp hq
  | mul_X p s hp =>
      have hX : (X s : MvPolynomial (ρ ⊕ ι) R) - rename Sum.inr (addGenAux w (X s)) ∈ J := by
        cases s with
        | inl k =>
          rw [addGenAux_X_inl]
          exact Ideal.subset_span ⟨k, rfl⟩
        | inr i => simp [addGenAux_X_inr]
      have h := Ideal.add_mem J (Ideal.mul_mem_right (X s) J hp)
        (Ideal.mul_mem_left J (rename Sum.inr (addGenAux w p)) hX)
      convert h using 1
      rw [map_mul, map_mul]
      ring

private lemma ker_addGenAux :
    RingHom.ker (addGenAux w (ι := ι) (R := R)).toRingHom =
      Ideal.span (Set.range fun k : ρ ↦
        (X (Sum.inl k) - rename Sum.inr (w k) : MvPolynomial (ρ ⊕ ι) R)) := by
  refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
  · have h0 : addGenAux w p = 0 := hp
    have h := sub_rename_addGenAux_mem w p
    rwa [h0, map_zero, sub_zero] at h
  · rintro _ ⟨k, rfl⟩
    simp [RingHom.mem_ker, addGenAux_X_inl, addGenAux_rename]

private lemma aeval_addGeneratorsVal :
    (aeval (Sum.elim (fun k ↦ aeval P.val (w k)) P.val) :
        MvPolynomial (ρ ⊕ ι) R →ₐ[R] S) = (aeval P.val).comp (addGenAux w) := by
  apply MvPolynomial.algHom_ext
  intro s
  cases s with
  | inl k => simp [addGenAux_X_inl]
  | inr i => simp [addGenAux_X_inr]

/-- Adjoining redundant generators to a presentation. Given a presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` and polynomials `w_k` in the `x_i`, this is the presentation of
`S` by the variables `z_k, x_i` and the relations `z_k - w_k, f_j`: the `z_k` are new names for
the elements `w_k(x)` of `S`. -/
noncomputable def addGenerators : Presentation R S (ρ ⊕ ι) (ρ ⊕ σ) where
  __ := Generators.ofSurjective (Sum.elim (fun k ↦ aeval P.val (w k)) P.val) <| by
    rw [aeval_addGeneratorsVal]
    exact P.aeval_val_surjective.comp (addGenAux_surjective w)
  relation := P.addGeneratorsRelation w
  span_range_relation_eq_ker := by
    have hval : (Generators.ofSurjective
        (Sum.elim (fun k ↦ aeval P.val (w k)) P.val) (ι := ρ ⊕ ι)
        (by rw [aeval_addGeneratorsVal]
            exact P.aeval_val_surjective.comp (addGenAux_surjective w))).val =
        Sum.elim (fun k ↦ aeval P.val (w k)) P.val := rfl
    have hmap : Ideal.map (addGenAux w (ι := ι) (R := R)).toRingHom
        (Ideal.span (Set.range fun j ↦
          (rename Sum.inr (P.relation j) : MvPolynomial (ρ ⊕ ι) R))) =
        Ideal.span (Set.range P.relation) := by
      rw [Ideal.map_span]
      congr 1
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun j ↦ addGenAux_rename w (P.relation j))
    have hcomap := Ideal.comap_map_of_surjective
      (addGenAux w (ι := ι) (R := R)).toRingHom (addGenAux_surjective w)
      (Ideal.span (Set.range fun j ↦
        (rename Sum.inr (P.relation j) : MvPolynomial (ρ ⊕ ι) R)))
    rw [hmap, ← RingHom.ker_eq_comap_bot, ker_addGenAux w] at hcomap
    have hmem : ∀ y : MvPolynomial ι R,
        aeval P.val y = 0 ↔ y ∈ Ideal.span (Set.range P.relation) := by
      intro y
      rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    have hker : (Generators.ofSurjective
        (Sum.elim (fun k ↦ aeval P.val (w k)) P.val) (ι := ρ ⊕ ι)
        (by rw [aeval_addGeneratorsVal]
            exact P.aeval_val_surjective.comp (addGenAux_surjective w))).ker =
        Ideal.comap (addGenAux w (ι := ι) (R := R)).toRingHom
          (Ideal.span (Set.range P.relation)) := by
      rw [Generators.ker_eq_ker_aeval_val, hval]
      ext x
      have hx : aeval (Sum.elim (fun k ↦ aeval P.val (w k)) P.val) x =
          aeval P.val (addGenAux w x) := by
        rw [aeval_addGeneratorsVal]; rfl
      simp only [RingHom.mem_ker, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx]
      exact hmem _
    rw [hker, hcomap, addGeneratorsRelation, Set.Sum.elim_range, Ideal.span_union, sup_comm]

/-- The relations of `Algebra.Presentation.addGenerators` are
`Algebra.Presentation.addGeneratorsRelation`. -/
@[simp] lemma addGenerators_relation :
    (P.addGenerators w).relation = P.addGeneratorsRelation w := rfl

/-- In `Algebra.Presentation.addGenerators`, the new generator `z_k` is sent to `w_k(x)` and
the old generator `x_i` to its image under the original presentation. -/
@[simp] lemma addGenerators_val :
    (P.addGenerators w).val = Sum.elim (fun k ↦ aeval P.val (w k)) P.val := rfl

end AddGenerators

end Algebra.Presentation

namespace Stacks.Smoothing

open Algebra

section Construction

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] {n c : ℕ}

/-- The presentation of the polynomial algebra `C[y_1, …, y_c]` over `C` with no relations. -/
private noncomputable def polyPresentation (C : Type*) [CommRing C] (c : ℕ) :
    Presentation C (MvPolynomial (Fin c) C) (Fin c) Empty where
  __ := Generators.mvPolynomial C (Fin c)
  relation := Empty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact (Generators.ker_mvPolynomial (R := C) (ι := Fin c)).symm

variable (P : Presentation R C (Fin n) (Fin c))

/-- The presentation `C[y_1, …, y_c] = R[y_1, …, y_c, x_1, …, x_n]/(f_1, …, f_c)` of the
polynomial algebra over `C` as an `R`-algebra, obtained from a presentation
`C = R[x_1, …, x_n]/(f_1, …, f_c)`. -/
private noncomputable def polyBasePresentation :
    Presentation R (MvPolynomial (Fin c) C) ((Fin c) ⊕ (Fin n)) (Fin c) where
  __ := (Generators.mvPolynomial C (Fin c)).comp P.toGenerators
  relation j := rename Sum.inr (P.relation j)
  span_range_relation_eq_ker := by
    have h := (polyPresentation C c).span_range_relation_eq_ker_comp P
    rw [Set.Sum.elim_range, Set.range_eq_empty, Set.empty_union] at h
    exact h

@[simp] private lemma polyBasePresentation_relation (j : Fin c) :
    (polyBasePresentation P).relation j = rename Sum.inr (P.relation j) := rfl

@[simp] private lemma polyBasePresentation_val_inl (l : Fin c) :
    (polyBasePresentation P).val (Sum.inl l) = MvPolynomial.X l := rfl

@[simp] private lemma polyBasePresentation_val_inr (i : Fin n) :
    (polyBasePresentation P).val (Sum.inr i) = algebraMap C (MvPolynomial (Fin c) C) (P.val i) :=
  rfl

variable (γ : Fin n → Fin c → MvPolynomial (Fin n) R)

/-- The redundant generator `x_i - ∑_l c_{il} y_l` of `C[y_1, …, y_c]`, as a polynomial in the
variables of `Algebra.Presentation.polyBasePresentation`. -/
private noncomputable def retractW (i : Fin n) : MvPolynomial ((Fin c) ⊕ (Fin n)) R :=
  MvPolynomial.X (Sum.inr i) - ∑ l, rename Sum.inr (γ i l) * MvPolynomial.X (Sum.inl l)

/-- The presentation of `C[y_1, …, y_c]` over `R` by the variables `z_i, y_l, x_i` and the
relations `z_i - x_i + ∑_l c_{il} y_l` and `f_j`, together with the pairing of the relations with
the variables `x_i` and `y_j` which makes it presubmersive. -/
private noncomputable def retractPresentation :
    PreSubmersivePresentation R (MvPolynomial (Fin c) C)
      ((Fin n) ⊕ ((Fin c) ⊕ (Fin n))) ((Fin n) ⊕ (Fin c)) where
  __ := (polyBasePresentation P).addGenerators (retractW γ)
  map := Sum.elim (fun i ↦ Sum.inr (Sum.inr i)) (fun j ↦ Sum.inr (Sum.inl j))
  map_inj := by
    rintro (i | j) (i' | j') h <;> simp_all

@[simp] private lemma retractPresentation_relation_inl (i : Fin n) :
    (retractPresentation P γ).relation (Sum.inl i) =
      MvPolynomial.X (Sum.inl i) - rename Sum.inr (retractW γ i) := rfl

@[simp] private lemma retractPresentation_relation_inr (j : Fin c) :
    (retractPresentation P γ).relation (Sum.inr j) =
      rename Sum.inr (rename Sum.inr (P.relation j)) := rfl

/-- The `C`-algebra map `C[y_1, …, y_c] → C` setting all `y_l` to zero. -/
private noncomputable def killY (C : Type*) [CommRing C] (c : ℕ) :
    MvPolynomial (Fin c) C →ₐ[C] C :=
  MvPolynomial.aeval (fun _ ↦ 0)

@[simp] private lemma killY_algebraMap (x : C) :
    killY C c (algebraMap C (MvPolynomial (Fin c) C) x) = x := by
  simp [killY]

@[simp] private lemma killY_X (l : Fin c) : killY C c (MvPolynomial.X l) = 0 := by
  simp [killY]

@[simp] private lemma retractPresentation_val_inl (i : Fin n) :
    (retractPresentation P γ).val (Sum.inl i) =
      MvPolynomial.aeval (polyBasePresentation P).val (retractW γ i) := rfl

@[simp] private lemma retractPresentation_val_inr_inl (l : Fin c) :
    (retractPresentation P γ).val (Sum.inr (Sum.inl l)) = MvPolynomial.X l := rfl

@[simp] private lemma retractPresentation_val_inr_inr (i : Fin n) :
    (retractPresentation P γ).val (Sum.inr (Sum.inr i)) =
      algebraMap C (MvPolynomial (Fin c) C) (P.val i) := rfl

/-- `killY` composed with the evaluation of `Algebra.Presentation.polyBasePresentation`. -/
private lemma killY_comp_aeval_polyBase :
    ((killY C c).restrictScalars R).comp (MvPolynomial.aeval (polyBasePresentation P).val) =
      MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val) := by
  apply MvPolynomial.algHom_ext
  rintro (l | i) <;> simp [killY]

/-- `killY` composed with the evaluation of `Algebra.Presentation.retractPresentation`. -/
private lemma killY_comp_aeval_retract :
    ((killY C c).restrictScalars R).comp
        (MvPolynomial.aeval (retractPresentation P γ).val) =
      MvPolynomial.aeval
        (Sum.elim P.val (Sum.elim (fun _ ↦ (0 : C)) P.val)) := by
  apply MvPolynomial.algHom_ext
  rintro (i | l | i)
  · have h := DFunLike.congr_fun (killY_comp_aeval_polyBase P) (retractW γ i)
    simp only [AlgHom.coe_comp, Function.comp_apply] at h
    have h2 : MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val) (retractW γ i) = P.val i := by
      simp [retractW, MvPolynomial.aeval_rename]
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X,
      retractPresentation_val_inl, Sum.elim_inl, h, h2]
  · simp
  · simp


/-- The composite of the evaluation of `retractPresentation` with `killY`: it sends the variable
`z_i` and `x_i` to `x_i` and the variable `y_l` to zero. -/
private noncomputable def retractKill :
    MvPolynomial ((Fin n) ⊕ ((Fin c) ⊕ (Fin n))) R →ₐ[R] C :=
  MvPolynomial.aeval (Sum.elim P.val (Sum.elim (fun _ ↦ (0 : C)) P.val))

private lemma retractKill_rename (p : MvPolynomial ((Fin c) ⊕ (Fin n)) R) :
    retractKill P (rename Sum.inr p) =
      MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val) p := by
  rw [retractKill, MvPolynomial.aeval_rename, Sum.elim_comp_inr]

private lemma retractKill_rename_rename (p : MvPolynomial (Fin n) R) :
    retractKill P (rename Sum.inr (rename Sum.inr p)) = MvPolynomial.aeval P.val p := by
  rw [retractKill_rename, MvPolynomial.aeval_rename, Sum.elim_comp_inr]

/-- The derivative of the new relation with respect to an `x`-variable, after setting the
`y`-variables to zero. -/
private lemma aeval_pderiv_retractW_inr (i i' : Fin n) :
    MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val)
        (pderiv (Sum.inr i) (retractW γ i')) = if i' = i then 1 else 0 := by
  classical
  have h1 : ∀ l : Fin c, MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val)
      (pderiv (Sum.inr i) (rename Sum.inr (γ i' l) *
        (MvPolynomial.X (Sum.inl l) : MvPolynomial ((Fin c) ⊕ (Fin n)) R))) = 0 := by
    intro l
    rw [pderiv_mul, MvPolynomial.pderiv_rename Sum.inr_injective,
      pderiv_X_of_ne (by simp : (Sum.inl l : (Fin c) ⊕ (Fin n)) ≠ Sum.inr i)]
    simp
  have h2 : MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val)
      (pderiv (Sum.inr i) (MvPolynomial.X (Sum.inr i') :
        MvPolynomial ((Fin c) ⊕ (Fin n)) R)) = if i' = i then 1 else 0 := by
    by_cases h : i' = i
    · subst h; simp
    · rw [pderiv_X_of_ne (by simpa using h)]; simp [h]
  rw [retractW, map_sub, map_sum, map_sub, map_sum]
  simp only [h1, h2, Finset.sum_const_zero, sub_zero]

/-- The derivative of the new relation with respect to a `y`-variable, after setting the
`y`-variables to zero. -/
private lemma aeval_pderiv_retractW_inl (j : Fin c) (i' : Fin n) :
    MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val)
        (pderiv (Sum.inl j) (retractW γ i')) = -MvPolynomial.aeval P.val (γ i' j) := by
  classical
  have h0 : pderiv (Sum.inl j) (retractW γ i') =
      -∑ l, pderiv (Sum.inl j) (rename Sum.inr (γ i' l) *
        (MvPolynomial.X (Sum.inl l) : MvPolynomial ((Fin c) ⊕ (Fin n)) R)) := by
    rw [retractW, map_sub, map_sum,
      pderiv_X_of_ne (by simp : (Sum.inr i' : (Fin c) ⊕ (Fin n)) ≠ Sum.inl j), zero_sub]
  have h1 : ∀ l : Fin c, MvPolynomial.aeval (Sum.elim (fun _ ↦ (0 : C)) P.val)
      (pderiv (Sum.inl j) (rename Sum.inr (γ i' l) *
        (MvPolynomial.X (Sum.inl l) : MvPolynomial ((Fin c) ⊕ (Fin n)) R))) =
      if l = j then MvPolynomial.aeval P.val (γ i' l) else 0 := by
    intro l
    rw [pderiv_mul, pderiv_rename_eq_zero_of_not_mem_range _ _ (by simp) (γ i' l)]
    by_cases h : l = j
    · subst h
      simp [MvPolynomial.aeval_rename]
    · rw [pderiv_X_of_ne (by simpa using h)]
      simp [h]
  rw [h0, map_neg, map_sum]
  simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The Jacobi matrix of the presentation, evaluated at `y = 0`: the block matrix
`[[-1, (∂f_j/∂x_i)], [(c_{jl}), 0]]`. -/
private lemma map_jacobiMatrix (N : Matrix (Fin c) (Fin n) C)
    (hN : ∀ (i : Fin n) (l : Fin c), MvPolynomial.aeval P.val (γ i l) = N l i) :
    (retractPresentation P γ).jacobiMatrix.map (retractKill P) =
      Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) C)
        (Matrix.of fun (i : Fin n) (j : Fin c) ↦
          MvPolynomial.aeval P.val (pderiv i (P.relation j))) N 0 := by
  classical
  have hmapinl : ∀ i : Fin n,
      (retractPresentation P γ).map (Sum.inl i) = Sum.inr (Sum.inr i) := fun _ ↦ rfl
  have hmapinr : ∀ j : Fin c,
      (retractPresentation P γ).map (Sum.inr j) = Sum.inr (Sum.inl j) := fun _ ↦ rfl
  ext s t
  rw [Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  match s, t with
  | Sum.inl i, Sum.inl i' =>
      rw [hmapinl, retractPresentation_relation_inl, map_sub,
        pderiv_X_of_ne (by simp), zero_sub,
        MvPolynomial.pderiv_rename Sum.inr_injective, map_neg, retractKill_rename,
        aeval_pderiv_retractW_inr, Matrix.fromBlocks_apply₁₁]
      simp [Matrix.one_apply, eq_comm]
  | Sum.inl i, Sum.inr j =>
      rw [hmapinl, retractPresentation_relation_inr,
        MvPolynomial.pderiv_rename Sum.inr_injective,
        MvPolynomial.pderiv_rename Sum.inr_injective,
        retractKill_rename_rename, Matrix.fromBlocks_apply₁₂]
      rfl
  | Sum.inr j, Sum.inl i' =>
      rw [hmapinr, retractPresentation_relation_inl, map_sub,
        pderiv_X_of_ne (by simp), zero_sub,
        MvPolynomial.pderiv_rename Sum.inr_injective, map_neg, retractKill_rename,
        aeval_pderiv_retractW_inl, neg_neg, Matrix.fromBlocks_apply₂₁, hN]
  | Sum.inr j, Sum.inr j' =>
      rw [hmapinr, retractPresentation_relation_inr,
        MvPolynomial.pderiv_rename Sum.inr_injective,
        pderiv_rename_eq_zero_of_not_mem_range _ _ (by simp) (P.relation j')]
      simp

/-- The determinant of the block matrix `[[-1, M], [N, 0]]` when `N * M = 1`. -/
private lemma det_fromBlocks_neg_one {m k : ℕ} (M : Matrix (Fin m) (Fin k) C)
    (N : Matrix (Fin k) (Fin m) C) (h : N * M = 1) :
    (Matrix.fromBlocks (-1 : Matrix (Fin m) (Fin m) C) M N 0).det = (-1) ^ m := by
  have hprod : Matrix.fromBlocks (-1 : Matrix (Fin m) (Fin m) C) M N 0 *
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) C) M 0 1 =
      Matrix.fromBlocks (-1 : Matrix (Fin m) (Fin m) C) 0 N 1 := by
    rw [Matrix.fromBlocks_multiply]
    congr 1 <;> simp [h]
  have h2 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at h2
  simpa [Matrix.det_neg] using h2

end Construction


section Main

open Algebra

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] {n c : ℕ}

/-- The matrix of the naive cotangent complex of a presentation in the basis of the conormal
module given by the relations is the Jacobi matrix `(∂f_j/∂x_i)`. -/
private lemma toMatrix_cotangentComplex
    (P : Presentation R C (Fin n) (Fin c))
    (bC : Module.Basis (Fin c) C P.toExtension.Cotangent)
    (hbC : ∀ j, bC j = Algebra.Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)
    (i : Fin n) (j : Fin c) :
    LinearMap.toMatrix bC P.cotangentSpaceBasis P.toExtension.cotangentComplex i j =
      MvPolynomial.aeval P.val (pderiv i (P.relation j)) := by
  rw [LinearMap.toMatrix_apply, hbC, Algebra.Extension.cotangentComplex_mk,
    P.cotangentSpaceBasis_repr_one_tmul]

/-- The Jacobian of `retractPresentation` becomes `(-1) ^ n` after setting the `y`-variables to
zero. -/
private lemma killY_jacobian (P : Presentation R C (Fin n) (Fin c))
    (γ : Fin n → Fin c → MvPolynomial (Fin n) R) (N : Matrix (Fin c) (Fin n) C)
    (hN : ∀ (i : Fin n) (l : Fin c), MvPolynomial.aeval P.val (γ i l) = N l i)
    (hNM : N * (Matrix.of fun (i : Fin n) (j : Fin c) ↦
      MvPolynomial.aeval P.val (pderiv i (P.relation j))) = 1) :
    killY C c (retractPresentation P γ).jacobian = (-1 : C) ^ n := by
  classical
  have h : killY C c (MvPolynomial.aeval (retractPresentation P γ).val
      (retractPresentation P γ).jacobiMatrix.det) =
      retractKill P (retractPresentation P γ).jacobiMatrix.det :=
    DFunLike.congr_fun (killY_comp_aeval_retract P γ) _
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.Generators.algebraMap_apply, h, AlgHom.map_det, AlgHom.mapMatrix_apply,
    map_jacobiMatrix P γ N hN, det_fromBlocks_neg_one _ N hNM]

/-- **Stacks 07CH.** Let `R → A` be a smooth ring map. Then there is a smooth `A`-algebra `B`
which is standard smooth over `R` and such that `A → B` has an `A`-algebra retraction. -/
@[stacks 07CH]
theorem exists_smooth_isStandardSmooth_retraction (R : Type u) (A : Type v) [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] :
    ∃ (B : Type v) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra R B)
      (_ : IsScalarTower R A B),
      Algebra.Smooth A B ∧ Algebra.IsStandardSmooth R B ∧
        ∃ r : B →+* A, r.comp (algebraMap A B) = RingHom.id A := by
  classical
  have : Algebra.Syntomic R A := Algebra.Smooth.syntomic R A
  obtain ⟨C, hCring, hRC, hAC, hTower, hSmoothAC, -, ρ, hρ, hRGCI⟩ :=
    Stacks.Smoothing.exists_smooth_retract_isRelativeGlobalCompleteIntersection R A
  let : CommRing C := hCring
  let : Algebra R C := hRC
  let : Algebra A C := hAC
  let : IsScalarTower R A C := hTower
  let : Algebra.Smooth A C := hSmoothAC
  let : Algebra.IsRelativeGlobalCompleteIntersection R C := hRGCI
  have hSmoothRC : Algebra.Smooth R C := Algebra.Smooth.comp R A C
  obtain ⟨n, c, P, hP⟩ := hRGCI.out
  let : P.IsRelativeGlobalCompleteIntersection := hP
  obtain ⟨bC, hbC⟩ := Algebra.Presentation.exists_basis_cotangent_relation P
  have : Algebra.FormallySmooth R C := hSmoothRC.formallySmooth
  have : Algebra.FormallySmooth R P.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial (Fin n) R))
  obtain ⟨lin, hlin⟩ :=
    (Algebra.Extension.formallySmooth_iff_split_injection P.toExtension).mp ‹_›
  -- the Jacobi matrix of `P` and the matrix of the splitting
  set Nmat : Matrix (Fin c) (Fin n) C := LinearMap.toMatrix P.cotangentSpaceBasis bC lin with hNdef
  have hNM : Nmat * (Matrix.of fun (i : Fin n) (j : Fin c) ↦
      MvPolynomial.aeval P.val (pderiv i (P.relation j))) = 1 := by
    have hM : (Matrix.of fun (i : Fin n) (j : Fin c) ↦
        MvPolynomial.aeval P.val (pderiv i (P.relation j))) =
        LinearMap.toMatrix bC P.cotangentSpaceBasis P.toExtension.cotangentComplex := by
      ext i j
      exact (toMatrix_cotangentComplex P bC hbC i j).symm
    rw [hM, hNdef, ← LinearMap.toMatrix_comp _ P.cotangentSpaceBasis, hlin,
      LinearMap.toMatrix_id]
  -- lifts of the entries of the splitting matrix to polynomials
  choose γ hγ using fun (i : Fin n) (l : Fin c) ↦ P.aeval_val_surjective (Nmat l i)
  set jac : MvPolynomial (Fin c) C := (retractPresentation P γ).jacobian
  have hkill : killY C c jac = (-1 : C) ^ n := killY_jacobian P γ Nmat hγ hNM
  -- the localization
  let B := Localization.Away jac
  -- `B` is standard smooth over `R`
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin c) C) B jac) :=
    IsLocalization.map_units B (⟨jac, Submonoid.mem_powers jac⟩ : Submonoid.powers jac)
  have hjacUnit : IsUnit ((Algebra.PreSubmersivePresentation.localizationAway B jac).comp
      (retractPresentation P γ)).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact hunit.mul hunit
  have hStd : Algebra.IsStandardSmooth R B :=
    (Algebra.SubmersivePresentation.mk _ hjacUnit).isStandardSmooth
  -- `B` is smooth over `A`
  have : Algebra.Smooth C (MvPolynomial (Fin c) C) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth (MvPolynomial (Fin c) C) B := Algebra.Smooth.of_isLocalization_Away jac
  have : Algebra.Smooth C B := Algebra.Smooth.comp C (MvPolynomial (Fin c) C) B
  have hSmoothAB : Algebra.Smooth A B := Algebra.Smooth.comp A C B
  -- the retraction
  let τ : MvPolynomial (Fin c) C →+* A := ρ.comp (killY C c).toRingHom
  have hτ : IsUnit (τ jac) := by
    show IsUnit (ρ (killY C c jac))
    rw [hkill, map_pow, map_neg, map_one]
    exact isUnit_one.neg.pow n
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, hSmoothAB, hStd,
    IsLocalization.Away.lift jac hτ, ?_⟩
  ext a
  show IsLocalization.Away.lift jac hτ (algebraMap A B a) = a
  have h1 : (algebraMap A B a) = algebraMap (MvPolynomial (Fin c) C) B
      (algebraMap C (MvPolynomial (Fin c) C) (algebraMap A C a)) := by
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin c) C) B,
      IsScalarTower.algebraMap_apply A C (MvPolynomial (Fin c) C)]
  rw [h1, IsLocalization.Away.lift_eq]
  show ρ (killY C c (algebraMap C (MvPolynomial (Fin c) C) (algebraMap A C a))) = a
  rw [killY_algebraMap]
  exact DFunLike.congr_fun hρ a

end Main

end Stacks.Smoothing
