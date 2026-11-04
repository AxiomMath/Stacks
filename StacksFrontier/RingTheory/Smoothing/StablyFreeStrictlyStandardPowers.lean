module

public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
public import StacksFrontier.RingTheory.Smoothing.StandardnessConditions
public import StacksFrontier.RingTheory.Smoothing.ElkikSingularIdeal
public import StacksFrontier.RingTheory.Smoothing.ConormalLocalization
public import StacksFrontier.RingTheory.Smoothing.PresentationAddVariables

/-!
# Stably free differentials give strictly standard powers

Let `R → A` be a ring map of finite presentation and let `a ∈ A`. If `A_a` is smooth over `R`
and `Ω_{A_a/R}` is stably free, then `a ^ e` is strictly standard in `A` over `R` for all
sufficiently large `e`. This is the implication (2) ⇒ (5) for large powers, part (e) of
Stacks 16.3.7.

The proof is the one of the source. Fix a presentation `A = R[x_1, …, x_n]/I`. Smoothness of
`A_a` makes the conormal sequence
`0 → (I/I²)_a → ⊕ A_a dx_i → Ω_{A_a/R} → 0`
split exact, so `(I/I²)_a` — the image of the Jacobian matrix of the relations — is a direct
summand of `A_a ^ n` with complement `Ω_{A_a/R}`. Adjoining `r` variables `y_1, …, y_r` and
the relations `y_1, …, y_r` adds a free summand `A_a ^ r` to the conormal module, and `r` can
be chosen, by stable freeness of `Ω_{A_a/R}`, so that the result is free, say of rank `c`.
Clearing denominators in a basis produces `c` elements `w_1, …, w_c` of the new relation
ideal `J`; putting them in front of the generators of `J` gives a presentation in which
condition 16.2.3.4 holds for a power of `a` — because the classes of `w_1, …, w_c` generate
`(J/J²)_a`, which is where the injectivity of the localized conormal map is used — and in
which the Jacobian map of the first `c` relations is a split injection after inverting `a`,
so that a power of `a` lies in the ideal of its maximal minors. Stacks 07ET turns that into
condition 16.2.3.3 for a further power, and both conditions are stable under multiplying the
element by anything, which gives all large powers.

## Main results

* `Stacks.Smoothing.isStrictlyStandard_pow_of_mem_maximalMinorsIdeal`: the reduction of
  strict standardness of the powers of `a` to one presentation, one `c` and one power.
* `Stacks.Smoothing.exists_eventually_isStrictlyStandard_pow`: **Stacks 16.3.7 (e)**.

## Implementation notes

The localization `A_a` is `Localization.Away a` and the module of differentials is Mathlib's
`KaehlerDifferential`, as in the other implications of Stacks 16.3.7 in
`StacksFrontier.RingTheory.Smoothing.StandardnessConditions`. The presentation with `r` extra
variables is `Stacks.Smoothing.addVarsPresentation`, and the facts used about the conormal
module of a presentation after inverting `a` are in
`StacksFrontier.RingTheory.Smoothing.ConormalLocalization`.

If `a` is nilpotent the localization is the zero ring and no rank argument is available; that
case is separated off, and there `a ^ e` is eventually `0`, which is strictly standard with
`c = 0`.

## References

* [Stacks Project, Tag 07EZ](https://stacks.math.columbia.edu/tag/07EZ)
* [Stacks Project, Tag 07ET](https://stacks.math.columbia.edu/tag/07ET)
* [Stacks Project, Tag 07DQ](https://stacks.math.columbia.edu/tag/07DQ)
-/

@[expose] public section

namespace Stacks.Smoothing

open MvPolynomial
open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- Splitting a vector of length `p + q` into its first `p` and its last `q` entries. -/
noncomputable def finAppendEquiv (T : Type*) [CommRing T] (p q : ℕ) :
    ((Fin p → T) × (Fin q → T)) ≃ₗ[T] (Fin (p + q) → T) where
  toFun uv := Fin.append uv.1 uv.2
  map_add' uv uv' := by
    funext i
    rcases fin_eq_castAdd_or_natAdd i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [Fin.append_left, Fin.append_right]
  map_smul' t uv := by
    funext i
    rcases fin_eq_castAdd_or_natAdd i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [Fin.append_left, Fin.append_right]
  invFun u := (fun i => u (Fin.castAdd q i), fun i => u (Fin.natAdd p i))
  left_inv uv := by
    apply Prod.ext <;> funext i <;> simp [Fin.append_left, Fin.append_right]
  right_inv u := by
    funext i
    rcases fin_eq_castAdd_or_natAdd i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [Fin.append_left, Fin.append_right]

/-- `finAppendEquiv` sends a pair of vectors to their concatenation `Fin.append`. -/
@[simp] theorem finAppendEquiv_apply {T : Type*} [CommRing T] {p q : ℕ}
    (uv : (Fin p → T) × (Fin q → T)) : finAppendEquiv T p q uv = Fin.append uv.1 uv.2 := rfl

private theorem standardCond2_of_forall_exists_lift (P : Presentation R A) (x : A) (c : ℕ)
    (hcm : c ≤ P.m)
    (h : ∀ j : Fin (P.m - c), ∃ p : MvPolynomial (Fin P.n) R, P.IsLift x p ∧
      p * P.f ⟨c + j.1, by have := j.2; omega⟩ ∈ P.firstRelIdeal c hcm + P.relIdeal ^ 2) :
    P.StandardCond2 x c hcm := by
  intro j ã hã
  obtain ⟨p, hp, hmem⟩ := h j
  have hdiff : ã - p ∈ P.relIdeal := by
    rw [mem_relIdeal_iff_lift_eq_zero, Presentation.lift_sub, show P.lift p = x from hp,
      show P.lift ã = x from hã, sub_self]
  have hgmem : P.f ⟨c + j.1, by have := j.2; omega⟩ ∈ P.relIdeal := Ideal.subset_span ⟨_, rfl⟩
  have h1 : (ã - p) * P.f ⟨c + j.1, by have := j.2; omega⟩ ∈ P.relIdeal ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hdiff hgmem
  have hsum : ã * P.f ⟨c + j.1, by have := j.2; omega⟩ =
      (ã - p) * P.f ⟨c + j.1, by have := j.2; omega⟩ +
        p * P.f ⟨c + j.1, by have := j.2; omega⟩ := by
    ring
  rw [hsum]
  exact Ideal.add_mem _ (Submodule.mem_sup_right h1) hmem

private theorem standardCond2_mul (P : Presentation R A) (x y : A) (c : ℕ) (hcm : c ≤ P.m)
    (h : P.StandardCond2 x c hcm) : P.StandardCond2 (x * y) c hcm := by
  refine standardCond2_of_forall_exists_lift P (x * y) c hcm fun j => ?_
  obtain ⟨p, hp⟩ := P.exists_isLift x
  obtain ⟨q, hq⟩ := P.exists_isLift y
  refine ⟨q * p, ?_, ?_⟩
  · show P.lift (q * p) = x * y
    rw [Presentation.lift_mul, show P.lift q = y from hq, show P.lift p = x from hp, mul_comm]
  · rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (h j p hp)

section Reduction

/-- **The reduction of Stacks 16.3.7 (e) to a single presentation.** If some power of `a`
lies in the ideal of maximal minors of the Jacobian matrix of the first `c` relations of a
presentation, and the same power satisfies condition 16.2.3.4 there, then every sufficiently
large power of `a` is strictly standard. -/
theorem isStrictlyStandard_pow_of_mem_maximalMinorsIdeal (a : A) (P : Presentation R A)
    (c N : ℕ) (hcn : c ≤ P.n) (hcm : c ≤ P.m)
    (hmin : a ^ N ∈ maximalMinorsIdeal (jacobianMatrix P c hcm))
    (hcond : P.StandardCond2 (a ^ N) c hcm) (e : ℕ) (he : c * N + N ≤ e) :
    IsStrictlyStandard (R := R) (a ^ e) := by
  classical
  obtain ⟨B, hB⟩ := exists_matrix_of_mem_minorIdeal _ _ hmin
  have hdiag : ((a ^ N) • (1 : Matrix (Fin c) (Fin c) A)) =
      Matrix.diagonal (fun _ : Fin c => a ^ N) := by
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  have hψ : (Matrix.toLin' B).comp (Matrix.toLin' (jacobianMatrix P c hcm)) =
      LinearMap.lsmul A (Fin c → A) (a ^ N) := by
    rw [← Matrix.toLin'_mul, hB, hdiag]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.diagonal_apply, LinearMap.lsmul_apply,
      dotProduct]
  obtain ⟨aI, haI⟩ :=
    exists_pow_eq_sum_jacobianMinor_of_comp_eq_lsmul P (a ^ N) c hcm (Matrix.toLin' B) hψ
  refine ⟨P, c, hcn, hcm, ⟨⟨fun s => a ^ (e - c * N) * aI s, ?_⟩, ?_⟩⟩
  · have hsplit : a ^ e = a ^ (e - c * N) * (a ^ N) ^ c := by
      rw [← pow_mul, ← pow_add, mul_comm N c]
      congr 1
      omega
    rw [hsplit, haI, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  · rw [← pow_mul_pow_sub a (show N ≤ e by nlinarith)]
    exact standardCond2_mul P _ _ c hcm hcond

end Reduction

section AddVarsJacobian

variable (P : Presentation R A) (r : ℕ) {c : ℕ}
  (w : Fin c → MvPolynomial (Fin (P.n + r)) R) (hw : ∀ κ, addVarsHom P r (w κ) = 0)

private theorem addVars_f_castAdd (κ : Fin c) :
    (addVarsPresentation P r w hw).f (Fin.castAdd (P.m + r) κ) = w κ := by
  show Fin.append w (addVarsRels P r) (Fin.castAdd (P.m + r) κ) = w κ
  exact Fin.append_left _ _ κ

private theorem addVars_f_natAdd (jj : Fin (P.m + r)) :
    (addVarsPresentation P r w hw).f (Fin.natAdd c jj) = addVarsRels P r jj := by
  show Fin.append w (addVarsRels P r) (Fin.natAdd c jj) = addVarsRels P r jj
  exact Fin.append_right _ _ jj

private theorem addVars_castLE (hcm : c ≤ (addVarsPresentation P r w hw).m) (κ : Fin c) :
    Fin.castLE hcm κ = Fin.castAdd (P.m + r) κ := Fin.ext rfl

private theorem addVars_jacobianMatrix (hcm : c ≤ (addVarsPresentation P r w hw).m)
    (z : Fin (P.n + r)) (κ : Fin c) :
    jacobianMatrix (addVarsPresentation P r w hw) c hcm z κ =
      addVarsHom P r (pderiv z (w κ)) := by
  show (addVarsPresentation P r w hw).lift
    (pderiv z ((addVarsPresentation P r w hw).f (Fin.castLE hcm κ))) = _
  rw [addVars_castLE, addVars_f_castAdd, addVarsPresentation_lift]

private theorem addVars_jacobianMatrixFull_castAdd (z : Fin (P.n + r)) (κ : Fin c) :
    jacobianMatrixFull (addVarsPresentation P r w hw) z (Fin.castAdd (P.m + r) κ) =
      addVarsHom P r (pderiv z (w κ)) := by
  show (addVarsPresentation P r w hw).lift
    (pderiv z ((addVarsPresentation P r w hw).f (Fin.castAdd (P.m + r) κ))) = _
  rw [addVars_f_castAdd, addVarsPresentation_lift]

private theorem addVars_jacobianMatrixFull_natAdd (z : Fin (P.n + r)) (jj : Fin (P.m + r)) :
    jacobianMatrixFull (addVarsPresentation P r w hw) z (Fin.natAdd c jj) =
      addVarsHom P r (pderiv z (addVarsRels P r jj)) := by
  show (addVarsPresentation P r w hw).lift
    (pderiv z ((addVarsPresentation P r w hw).f (Fin.natAdd c jj))) = _
  rw [addVars_f_natAdd, addVarsPresentation_lift]

private theorem addVars_firstRelIdeal (hcm : c ≤ (addVarsPresentation P r w hw).m) :
    (addVarsPresentation P r w hw).firstRelIdeal c hcm = Ideal.span (Set.range w) := by
  show Ideal.span (Set.range fun κ : Fin c =>
    (addVarsPresentation P r w hw).f (Fin.castLE hcm κ)) = _
  refine congrArg Ideal.span (congrArg Set.range (funext fun κ => ?_))
  rw [addVars_castLE, addVars_f_castAdd]

end AddVarsJacobian

section Construction

/-- **The construction of Stacks 16.3.7 (e).** If `T = A_a` is formally smooth over `R` and
`T ⊗ Ω[A⁄R]` is stably free, then some presentation of `A` and some `c` satisfy both halves of
strict standardness for a power of `a`. -/
private theorem exists_presentation_of_isStablyFree [Algebra.FinitePresentation R A] (a : A)
    (T : Type v) [CommRing T] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    [IsLocalization (Submonoid.powers a) T] [Algebra.FormallySmooth R T] [Nontrivial T]
    [Module.Finite T (T ⊗[A] Ω[A⁄R])] [Module.IsStablyFree T (T ⊗[A] Ω[A⁄R])] :
    ∃ (P : Presentation R A) (c N : ℕ) (_ : c ≤ P.n) (hcm : c ≤ P.m),
      a ^ N ∈ maximalMinorsIdeal (jacobianMatrix P c hcm) ∧ P.StandardCond2 (a ^ N) c hcm := by
  classical
  obtain ⟨P₀⟩ := nonempty_presentation R A
  have := finite_cotangent_baseChange T (P := P₀)
  obtain ⟨k, l, δ, hkl⟩ := exists_prod_fin_linearEquiv T (T ⊗[A] Ω[A⁄R])
  obtain ⟨eS, hrange⟩ := exists_split_jacobian T (P := P₀) a
  have htoLin : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) T) (x : Fin q → T) (i : Fin p),
      Matrix.toLin' M x i = ∑ j, M i j * x j := by
    intro p q M x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  have htoLinCols : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) T) (x : Fin q → T),
      Matrix.toLin' M x = ∑ j, x j • fun z => M z j := by
    intro p q M x
    funext z
    rw [htoLin]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have htoLinSingle : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) T) (j : Fin q),
      Matrix.toLin' M (Pi.single j 1) = fun i => M i j := by
    intro p q M j
    funext i
    rw [htoLin]
    simp [Pi.single_apply]
  -- The splitting of the conormal map of `P₀`, and the free complement.
  let C := T ⊗[A] (toAlgebraPresentation P₀).toGenerators.toExtension.Cotangent
  let W := T ⊗[A] Ω[A⁄R]
  let f : C →ₗ[T] (Fin P₀.n → T) := eS.symm.toLinearMap ∘ₗ LinearMap.inl T C W
  let lf : (Fin P₀.n → T) →ₗ[T] C := LinearMap.fst T C W ∘ₗ eS.toLinearMap
  have hlf : ∀ x, lf (f x) = x := fun x => by simp [lf, f]
  let Ξ : (Fin (P₀.n + k) → T) ≃ₗ[T] C × (Fin l → T) :=
    (finAppendEquiv T P₀.n k).symm.trans
      ((eS.prodCongr (LinearEquiv.refl T (Fin k → T))).trans
        ((LinearEquiv.prodAssoc T C W (Fin k → T)).trans
          ((LinearEquiv.refl T C).prodCongr δ)))
  let Θ : (Fin (P₀.n + k) → T) →ₗ[T] (Fin (P₀.n + l) → T) :=
    (finAppendEquiv T P₀.n l).toLinearMap ∘ₗ (f.prodMap LinearMap.id) ∘ₗ Ξ.toLinearMap
  let Λ : (Fin (P₀.n + l) → T) →ₗ[T] (Fin (P₀.n + k) → T) :=
    Ξ.symm.toLinearMap ∘ₗ (lf.prodMap LinearMap.id) ∘ₗ
      (finAppendEquiv T P₀.n l).symm.toLinearMap
  have hΘ : ∀ x, Θ x = Fin.append (f (Ξ x).1) (Ξ x).2 := fun x => rfl
  have hΛΘ : ∀ x, Λ (Θ x) = x := by
    intro x
    have e1 : (finAppendEquiv T P₀.n l).symm ((finAppendEquiv T P₀.n l)
        ((f.prodMap LinearMap.id) (Ξ x))) = (f.prodMap LinearMap.id) (Ξ x) :=
      (finAppendEquiv T P₀.n l).symm_apply_apply _
    show Ξ.symm ((lf.prodMap LinearMap.id) ((finAppendEquiv T P₀.n l).symm
      ((finAppendEquiv T P₀.n l) ((f.prodMap LinearMap.id) (Ξ x))))) = x
    rw [e1]
    show Ξ.symm (lf (f (Ξ x).1), (Ξ x).2) = x
    rw [hlf]
    exact Ξ.symm_apply_apply x
  have hmemΘ : ∀ (x : C) (y : Fin l → T), Fin.append (f x) y ∈ LinearMap.range Θ := by
    intro x y
    refine ⟨Ξ.symm (x, y), ?_⟩
    rw [hΘ, LinearEquiv.apply_symm_apply]
  have hΘsum : ∀ x, Θ x = ∑ κ : Fin (P₀.n + k), x κ • Θ (Pi.single κ 1) := by
    intro x
    have hxx : ∑ κ : Fin (P₀.n + k), x κ • (Pi.single κ 1 : Fin (P₀.n + k) → T) = x := by
      have h := (Pi.basisFun T (Fin (P₀.n + k))).sum_repr x
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using h
    conv_lhs => rw [← hxx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun κ _ => map_smul _ _ _
  -- Coordinates of the columns of `Θ`, cleared of denominators.
  have hu : ∀ κ : Fin (P₀.n + k), ∃ ut : Fin P₀.m → T,
      Matrix.toLin' ((jacobianMatrixFull P₀).map (algebraMap A T)) ut =
        f (Ξ (Pi.single κ 1)).1 := by
    intro κ
    have hmem : f (Ξ (Pi.single κ 1)).1 ∈
        LinearMap.range (Matrix.toLin' ((jacobianMatrixFull P₀).map (algebraMap A T))) := by
      rw [hrange]
      exact ⟨(Ξ (Pi.single κ 1)).1, rfl⟩
    exact hmem
  choose ut hut using hu
  obtain ⟨bden, hbden⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers a)
    (Finset.univ : Finset ((Fin (P₀.n + k) × Fin P₀.m) ⊕ (Fin (P₀.n + k) × Fin l)))
    (Sum.elim (fun p => ut p.1 p.2) fun p => (Ξ (Pi.single p.1 1)).2 p.2)
  obtain ⟨N₁, hN₁⟩ := (Submonoid.mem_powers_iff (bden : A) a).1 bden.2
  have huint : ∀ (κ : Fin (P₀.n + k)) (j : Fin P₀.m),
      ∃ z : A, algebraMap A T z = (bden : A) • ut κ j := by
    intro κ j
    obtain ⟨z, hz⟩ := hbden (Sum.inl (κ, j)) (Finset.mem_univ _)
    exact ⟨z, hz⟩
  choose u hu' using huint
  have hvint : ∀ (κ : Fin (P₀.n + k)) (i : Fin l),
      ∃ z : A, algebraMap A T z = (bden : A) • (Ξ (Pi.single κ 1)).2 i := by
    intro κ i
    obtain ⟨z, hz⟩ := hbden (Sum.inr (κ, i)) (Finset.mem_univ _)
    exact ⟨z, hz⟩
  choose v hv' using hvint
  choose up hup using fun (κ : Fin (P₀.n + k)) (j : Fin P₀.m) => P₀.exists_isLift (u κ j)
  choose vp hvp using fun (κ : Fin (P₀.n + k)) (i : Fin l) => P₀.exists_isLift (v κ i)
  -- The presentation with `l` extra variables and the `w`'s in front.
  obtain ⟨wf, hwf⟩ : ∃ wf : Fin (P₀.n + k) → MvPolynomial (Fin (P₀.n + l)) R,
      ∀ κ, wf κ = addVarsCombination P₀ l (up κ) (vp κ) :=
    ⟨fun κ => addVarsCombination P₀ l (up κ) (vp κ), fun _ => rfl⟩
  have hwrel : ∀ κ, addVarsHom P₀ l (wf κ) = 0 := by
    intro κ
    rw [hwf κ]
    exact addVarsHom_addVarsCombination P₀ l (up κ) (vp κ)
  let P : Presentation R A := addVarsPresentation P₀ l wf hwrel
  have hcn : P₀.n + k ≤ P.n := by
    show P₀.n + k ≤ P₀.n + l
    omega
  have hcm : P₀.n + k ≤ P.m := by
    show P₀.n + k ≤ P₀.n + k + (P₀.m + l)
    omega
  have hJacL : ∀ (κ : Fin (P₀.n + k)) (i : Fin P₀.n),
      jacobianMatrix P (P₀.n + k) hcm (Fin.castAdd l i) κ =
        ∑ j : Fin P₀.m, u κ j * jacobianMatrixFull P₀ i j := by
    intro κ i
    show jacobianMatrix (addVarsPresentation P₀ l wf hwrel) (P₀.n + k) hcm
      (Fin.castAdd l i) κ = _
    rw [addVars_jacobianMatrix, hwf κ, addVarsHom_pderiv_castAdd_addVarsCombination]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show P₀.lift (up κ j) = u κ j from hup κ j]
      rfl
  have hJacR : ∀ (κ : Fin (P₀.n + k)) (i : Fin l),
      jacobianMatrix P (P₀.n + k) hcm (Fin.natAdd P₀.n i) κ = v κ i := by
    intro κ i
    show jacobianMatrix (addVarsPresentation P₀ l wf hwrel) (P₀.n + k) hcm
      (Fin.natAdd P₀.n i) κ = _
    rw [addVars_jacobianMatrix, hwf κ, addVarsHom_pderiv_natAdd_addVarsCombination]
    exact hvp κ i
  have hFull1 : ∀ (z : Fin (P₀.n + l)) (κ : Fin (P₀.n + k)),
      jacobianMatrixFull P z (Fin.castAdd (P₀.m + l) κ) =
        jacobianMatrix P (P₀.n + k) hcm z κ := by
    intro z κ
    show jacobianMatrixFull (addVarsPresentation P₀ l wf hwrel) z
      (Fin.castAdd (P₀.m + l) κ) =
      jacobianMatrix (addVarsPresentation P₀ l wf hwrel) (P₀.n + k) hcm z κ
    rw [addVars_jacobianMatrixFull_castAdd, addVars_jacobianMatrix]
  have hFull2 : ∀ (z : Fin (P₀.n + l)) (jj : Fin (P₀.m + l)),
      jacobianMatrixFull P z (Fin.natAdd (P₀.n + k) jj) =
        addVarsHom P₀ l (pderiv z (addVarsRels P₀ l jj)) := by
    intro z jj
    show jacobianMatrixFull (addVarsPresentation P₀ l wf hwrel) z
      (Fin.natAdd (P₀.n + k) jj) = _
    rw [addVars_jacobianMatrixFull_natAdd]
  have hfirst : P.firstRelIdeal (P₀.n + k) hcm = Ideal.span (Set.range wf) :=
    addVars_firstRelIdeal P₀ l wf hwrel hcm
  -- A power of `a` lies in the ideal of maximal minors of the Jacobian.
  let MT : Matrix (Fin (P₀.n + l)) (Fin (P₀.n + k)) T :=
    fun z κ => algebraMap A T (jacobianMatrix P (P₀.n + k) hcm z κ)
  have hbb : algebraMap A T (a ^ N₁) = algebraMap A T (bden : A) := by rw [hN₁]
  have hcolT : ∀ κ : Fin (P₀.n + k),
      (fun z => MT z κ) = (algebraMap A T (a ^ N₁)) • Θ (Pi.single κ 1) := by
    intro κ
    funext z
    rcases fin_eq_castAdd_or_natAdd (n := P₀.n) (r := l) z with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · show algebraMap A T (jacobianMatrix P (P₀.n + k) hcm (Fin.castAdd l i) κ) = _
      rw [hJacL, hΘ, Pi.smul_apply, Fin.append_left, ← hut κ, htoLin, map_sum, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hu' κ j, Algebra.smul_def, hbb, Matrix.map_apply]
      ring
    · show algebraMap A T (jacobianMatrix P (P₀.n + k) hcm (Fin.natAdd P₀.n i) κ) = _
      rw [hJacR, hΘ, Pi.smul_apply, Fin.append_right, hv' κ i, Algebra.smul_def, hbb,
        smul_eq_mul]
  have hJacT : ∀ x, Matrix.toLin' MT x = (algebraMap A T (a ^ N₁)) • Θ x := by
    intro x
    rw [htoLinCols, hΘsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun κ _ => by
      rw [hcolT κ, smul_smul, smul_smul, mul_comm]
  have htunit : IsUnit (algebraMap A T (a ^ N₁)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit a).pow N₁
  have hΛT : (LinearMap.toMatrix' Λ) * MT =
      (algebraMap A T (a ^ N₁)) • (1 : Matrix (Fin (P₀.n + k)) (Fin (P₀.n + k)) T) := by
    have h1 : Λ ∘ₗ Matrix.toLin' MT =
        LinearMap.lsmul T (Fin (P₀.n + k) → T) (algebraMap A T (a ^ N₁)) := by
      refine LinearMap.ext fun x => ?_
      show Λ (Matrix.toLin' MT x) = _
      rw [hJacT, map_smul, hΛΘ]
      rfl
    rw [← LinearMap.toMatrix'_toLin' MT, ← LinearMap.toMatrix'_comp, h1]
    ext i j
    simp [LinearMap.toMatrix'_apply, LinearMap.lsmul_apply, Pi.single_apply, Matrix.one_apply]
  have hminT : (algebraMap A T (a ^ N₁)) ^ (P₀.n + k) ∈ maximalMinorsIdeal MT :=
    pow_mem_minorIdeal_of_matrix MT _ (LinearMap.toMatrix' Λ) hΛT
  have h1mem : (1 : T) ∈ Ideal.map (algebraMap A T)
      (maximalMinorsIdeal (jacobianMatrix P (P₀.n + k) hcm)) := by
    rw [← maximalMinorsIdeal_map]
    exact (Ideal.eq_top_iff_one _).1 (Ideal.eq_top_of_isUnit_mem _ hminT (htunit.pow _))
  obtain ⟨N₂, hN₂⟩ := exists_pow_mem_of_one_mem_map T a _ h1mem
  -- The conormal module of `P`, and the classes of its relations.
  let E' := (toAlgebraPresentation P).toGenerators.toExtension
  have hdmem : ∀ jj : Fin P.m, P.f jj ∈ E'.ker :=
    fun jj => (toAlgebraPresentation P).relation_mem_ker jj
  let dcl : Fin P.m → E'.Cotangent := fun jj =>
    Algebra.Extension.Cotangent.mk (P := E') ⟨P.f jj, hdmem jj⟩
  let Fall := relationClassesBaseChange T P
  have hFallsingle : ∀ jj : Fin P.m, Fall (Pi.single jj 1) = (1 : T) ⊗ₜ[A] dcl jj := by
    intro jj
    simp [Fall, relationClassesBaseChange, Fintype.linearCombination_apply, Pi.single_apply,
      dcl]
  let ι' : T ⊗[A] E'.Cotangent →ₗ[T] (Fin P.n → T) :=
    ((toAlgebraPresentation P).toGenerators.cotangentSpaceBasis.baseChange T).equivFun.toLinearMap
      ∘ₗ E'.cotangentComplex.baseChange T
  have hι'inj : Function.Injective ι' := by
    intro x y hxy
    refine injective_cotangentComplex_baseChange (R := R)
      (toAlgebraPresentation P).toGenerators (Submonoid.powers a) (T := T) ?_
    exact ((toAlgebraPresentation P).toGenerators.cotangentSpaceBasis.baseChange
      T).equivFun.injective hxy
  have hkeyapp : ∀ x, ι' (Fall x) =
      Matrix.toLin' ((jacobianMatrixFull P).map (algebraMap A T)) x := fun x =>
    LinearMap.congr_fun (cotangentSpaceBasis_comp_cotangentComplex_comp_relationClasses T) x
  -- Every column of the full Jacobian of `P` lies in the image of `Θ`.
  have hcol1 : ∀ κ : Fin (P₀.n + k),
      (fun z => algebraMap A T (jacobianMatrixFull P z (Fin.castAdd (P₀.m + l) κ))) =
        (algebraMap A T (a ^ N₁)) • Θ (Pi.single κ 1) := by
    intro κ
    rw [← hcolT κ]
    funext z
    exact congrArg (algebraMap A T) (hFull1 z κ)
  have hcol2 : ∀ j : Fin P₀.m,
      (fun z => algebraMap A T
        (jacobianMatrixFull P z (Fin.natAdd (P₀.n + k) (Fin.castAdd l j)))) ∈
        LinearMap.range Θ := by
    intro j
    obtain ⟨x, hx⟩ : ∃ x : C, f x =
        Matrix.toLin' ((jacobianMatrixFull P₀).map (algebraMap A T)) (Pi.single j 1) := by
      have hmem : Matrix.toLin' ((jacobianMatrixFull P₀).map (algebraMap A T))
          (Pi.single j 1) ∈ LinearMap.range (eS.symm.toLinearMap ∘ₗ LinearMap.inl T C W) := by
        rw [← hrange]
        exact ⟨Pi.single j 1, rfl⟩
      exact hmem
    have hcol : (fun z => algebraMap A T
        (jacobianMatrixFull P z (Fin.natAdd (P₀.n + k) (Fin.castAdd l j)))) =
        Fin.append (f x) 0 := by
      funext z
      rcases fin_eq_castAdd_or_natAdd (n := P₀.n) (r := l) z with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have h3 := congrArg (algebraMap A T) (hFull2 (Fin.castAdd l i) (Fin.castAdd l j))
        rw [addVarsRels_castAdd, pderiv_castAdd_rename, addVarsHom_rename] at h3
        rw [h3, Fin.append_left, hx, htoLinSingle]
        rfl
      · have h3 := congrArg (algebraMap A T) (hFull2 (Fin.natAdd P₀.n i) (Fin.castAdd l j))
        rw [addVarsRels_castAdd, pderiv_natAdd_rename, map_zero, map_zero] at h3
        rw [h3, Fin.append_right]
        rfl
    rw [hcol]
    exact hmemΘ x 0
  have hcol3 : ∀ i' : Fin l,
      (fun z => algebraMap A T
        (jacobianMatrixFull P z (Fin.natAdd (P₀.n + k) (Fin.natAdd P₀.m i')))) ∈
        LinearMap.range Θ := by
    intro i'
    have hcol : (fun z => algebraMap A T
        (jacobianMatrixFull P z (Fin.natAdd (P₀.n + k) (Fin.natAdd P₀.m i')))) =
        Fin.append (f 0) (Pi.single i' 1) := by
      funext z
      rw [map_zero]
      rcases fin_eq_castAdd_or_natAdd (n := P₀.n) (r := l) z with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have h3 := congrArg (algebraMap A T)
          (hFull2 (Fin.castAdd l i) (Fin.natAdd P₀.m i'))
        rw [addVarsRels_natAdd, pderiv_X_of_ne (natAdd_ne_castAdd i i'), map_zero,
          map_zero] at h3
        rw [h3, Fin.append_left]
        rfl
      · have h3 := congrArg (algebraMap A T)
          (hFull2 (Fin.natAdd P₀.n i) (Fin.natAdd P₀.m i'))
        rw [addVarsRels_natAdd] at h3
        rw [h3, Fin.append_right]
        rcases eq_or_ne i' i with rfl | hne
        · rw [pderiv_X_self, map_one, map_one]
          simp
        · have hne' : (Fin.natAdd P₀.n i' : Fin (P₀.n + l)) ≠ Fin.natAdd P₀.n i := by
            intro h
            have hv : P₀.n + (i' : ℕ) = P₀.n + (i : ℕ) := congrArg Fin.val h
            exact hne (Fin.ext (by omega))
          rw [pderiv_X_of_ne hne', map_zero, map_zero]
          simp [Ne.symm hne]
    rw [hcol]
    exact hmemΘ 0 (Pi.single i' 1)
  have hcolmem : ∀ jj : Fin P.m,
      (fun z => algebraMap A T (jacobianMatrixFull P z jj)) ∈ LinearMap.range Θ := by
    intro jj
    rcases fin_eq_castAdd_or_natAdd (n := P₀.n + k) (r := P₀.m + l) jj with
      ⟨κ, rfl⟩ | ⟨jj', rfl⟩
    · rw [hcol1 κ]
      exact Submodule.smul_mem _ _ ⟨Pi.single κ 1, rfl⟩
    · rcases fin_eq_castAdd_or_natAdd (n := P₀.m) (r := l) jj' with ⟨j, rfl⟩ | ⟨i', rfl⟩
      · exact hcol2 j
      · exact hcol3 i'
  have hrangeΦ : ∀ x, Matrix.toLin' ((jacobianMatrixFull P).map (algebraMap A T)) x ∈
      LinearMap.range Θ := by
    intro x
    rw [htoLinCols]
    exact Submodule.sum_mem _ fun jj _ => Submodule.smul_mem _ _ (hcolmem jj)
  -- The classes of the first `c` relations generate the localized conormal module.
  have hιV : Submodule.map ι' (Submodule.span T (Set.range fun κ : Fin (P₀.n + k) =>
      Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1))) = LinearMap.range Θ := by
    have hfun : (fun κ : Fin (P₀.n + k) =>
        ι' (Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1))) =
        fun κ => (algebraMap A T (a ^ N₁)) • Θ (Pi.single κ 1) := by
      funext κ
      have h4 : ι' (Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1)) =
          fun z => algebraMap A T (jacobianMatrixFull P z (Fin.castAdd (P₀.m + l) κ)) := by
        rw [hkeyapp]
        exact htoLinSingle _ _
      rw [h4, hcol1 κ]
    rw [Submodule.map_span, ← Set.range_comp]
    show Submodule.span T (Set.range (fun κ : Fin (P₀.n + k) =>
      ι' (Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1)))) = _
    rw [hfun]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨κ, rfl⟩
      exact Submodule.smul_mem _ _ ⟨Pi.single κ 1, rfl⟩
    · rintro _ ⟨x, rfl⟩
      rw [hΘsum]
      refine Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ ?_
      have hinv : (↑(htunit.unit⁻¹) : T) * algebraMap A T (a ^ N₁) = 1 :=
        htunit.unit.inv_mul
      have hΘκ : Θ (Pi.single κ 1) =
          (↑(htunit.unit⁻¹) : T) • ((algebraMap A T (a ^ N₁)) • Θ (Pi.single κ 1)) := by
        rw [smul_smul, hinv, one_smul]
      rw [hΘκ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ, rfl⟩)
  have hVtop : ∀ y : T ⊗[A] E'.Cotangent, y ∈ Submodule.span T
      (Set.range fun κ : Fin (P₀.n + k) =>
        Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1)) := by
    intro y
    have h1 : ι' y ∈ Submodule.map ι' (Submodule.span T
        (Set.range fun κ : Fin (P₀.n + k) =>
          Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1))) := by
      rw [hιV]
      obtain ⟨x, rfl⟩ := relationClassesBaseChange_surjective T (P := P) y
      rw [hkeyapp]
      exact hrangeΦ x
    obtain ⟨y', hy'V, hy'⟩ := h1
    rwa [hι'inj hy'] at hy'V
  -- Descending the generation statement to `A`.
  have hsmulT : ∀ (z : A) (x : E'.Cotangent),
      algebraMap A T z • ((1 : T) ⊗ₜ[A] x) = (1 : T) ⊗ₜ[A] (z • x) := by
    intro z x
    rw [algebraMap_smul, TensorProduct.smul_tmul' z (1 : T) x,
      TensorProduct.smul_tmul z (1 : T) x]
  have hstep : ∀ jj : Fin P.m, ∃ N : ℕ, a ^ N • dcl jj ∈ Submodule.span A
      (Set.range fun κ : Fin (P₀.n + k) => dcl (Fin.castAdd (P₀.m + l) κ)) := by
    intro jj
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun T).1
      (hVtop (Fall (Pi.single jj 1)))
    obtain ⟨bd, hbd⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers a)
      (Finset.univ : Finset (Fin (P₀.n + k))) cf
    obtain ⟨N₃, hN₃⟩ := (Submonoid.mem_powers_iff (bd : A) a).1 bd.2
    have hαint : ∀ κ, ∃ z : A, algebraMap A T z = (bd : A) • cf κ := by
      intro κ
      obtain ⟨z, hz⟩ := hbd κ (Finset.mem_univ _)
      exact ⟨z, hz⟩
    choose α hα using hαint
    have hT1 : (1 : T) ⊗ₜ[A] ((a ^ N₃) • dcl jj -
        ∑ κ, α κ • dcl (Fin.castAdd (P₀.m + l) κ)) = 0 := by
      rw [TensorProduct.tmul_sub, sub_eq_zero, ← hsmulT, TensorProduct.tmul_sum,
        ← hFallsingle jj, ← hcf, Finset.smul_sum]
      refine Finset.sum_congr rfl fun κ _ => ?_
      have h2 : (1 : T) ⊗ₜ[A] (α κ • dcl (Fin.castAdd (P₀.m + l) κ)) =
          algebraMap A T (α κ) • Fall (Pi.single (Fin.castAdd (P₀.m + l) κ) 1) := by
        rw [hFallsingle (Fin.castAdd (P₀.m + l) κ),
          hsmulT (α κ) (dcl (Fin.castAdd (P₀.m + l) κ))]
      rw [h2, hα κ, Algebra.smul_def, ← hN₃, smul_smul]
    have hloc : IsLocalizedModule (Submonoid.powers a)
        (TensorProduct.mk A T E'.Cotangent 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) T _).mpr
        (TensorProduct.isBaseChange A E'.Cotangent T)
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
      (TensorProduct.mk A T E'.Cotangent 1)).1 hT1
    obtain ⟨N₄, hN₄⟩ := (Submonoid.mem_powers_iff (s : A) a).1 s.2
    refine ⟨N₄ + N₃, ?_⟩
    have hs2 : ((s : A)) • ((a ^ N₃) • dcl jj -
        ∑ κ, α κ • dcl (Fin.castAdd (P₀.m + l) κ)) = 0 := hs
    rw [← hN₄, smul_sub, sub_eq_zero] at hs2
    rw [pow_add, mul_smul, hs2, Finset.smul_sum]
    exact Submodule.sum_mem _ fun κ _ => by
      rw [smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ, rfl⟩)
  choose Nf hNf using hstep
  have hNmax : ∀ jj : Fin P.m, a ^ (Finset.univ.sup Nf) • dcl jj ∈ Submodule.span A
      (Set.range fun κ : Fin (P₀.n + k) => dcl (Fin.castAdd (P₀.m + l) κ)) := by
    intro jj
    rw [← pow_sub_mul_pow a (Finset.le_sup (f := Nf) (Finset.mem_univ jj)), mul_smul]
    exact Submodule.smul_mem _ _ (hNf jj)
  -- From generation to condition 16.2.3.4.
  have halg : ∀ p : MvPolynomial (Fin P.n) R, algebraMap E'.Ring A p = P.lift p := by
    intro p
    have h1 : algebraMap E'.Ring A (generatorsToExtensionRingEquiv
        (toAlgebraPresentation P).toGenerators p) =
        algebraMap (toAlgebraPresentation P).toGenerators.Ring A p :=
      generatorsToExtensionRingEquiv_algebraMap _ p
    rw [generatorsToExtensionRingEquiv_apply] at h1
    rw [h1]
    show aeval (toAlgebraPresentation P).toGenerators.val p = P.lift p
    rw [aeval_toAlgebraPresentation]
  have hsmul_dcl : ∀ (p : MvPolynomial (Fin P.n) R) (jj : Fin P.m),
      (P.lift p) • dcl jj = Algebra.Extension.Cotangent.mk (P := E')
        ⟨p * P.f jj, Ideal.mul_mem_left _ _ (hdmem jj)⟩ := by
    intro p jj
    have h1 := cotangentMk_mul E' p ⟨P.f jj, hdmem jj⟩ (Ideal.mul_mem_left _ _ (hdmem jj))
    have h2 := IsScalarTower.algebraMap_smul (R := E'.Ring) (A := A) (M := E'.Cotangent) p
      (dcl jj)
    rw [← halg p, h2]
    exact h1.symm
  have hker : E'.ker = P.relIdeal := ker_toAlgebraPresentation P
  have hcond : ∀ jj : Fin P.m, ∃ p : MvPolynomial (Fin P.n) R,
      P.IsLift (a ^ (Finset.univ.sup Nf)) p ∧
      p * P.f jj ∈ P.firstRelIdeal (P₀.n + k) hcm + P.relIdeal ^ 2 := by
    intro jj
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 (hNmax jj)
    obtain ⟨q, hq⟩ := P.exists_isLift (a ^ (Finset.univ.sup Nf))
    choose bp hbp using fun κ : Fin (P₀.n + k) => P.exists_isLift (β κ)
    have hmemsum : (∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ)) ∈ E'.ker :=
      Ideal.sum_mem _ fun κ _ => Ideal.mul_mem_left _ _ (hdmem _)
    have hsum : ∑ κ : Fin (P₀.n + k), β κ • dcl (Fin.castAdd (P₀.m + l) κ) =
        Algebra.Extension.Cotangent.mk (P := E')
          ⟨∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ), hmemsum⟩ := by
      rw [show (⟨∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ),
          hmemsum⟩ : E'.ker) =
          ∑ κ : Fin (P₀.n + k), (⟨bp κ * P.f (Fin.castAdd (P₀.m + l) κ),
            Ideal.mul_mem_left _ _ (hdmem _)⟩ : E'.ker) from
        Subtype.ext (by simp), map_sum]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [show β κ = P.lift (bp κ) from (hbp κ).symm,
        hsmul_dcl (bp κ) (Fin.castAdd (P₀.m + l) κ)]
    have hlhs : (a ^ (Finset.univ.sup Nf)) • dcl jj =
        Algebra.Extension.Cotangent.mk (P := E')
          ⟨q * P.f jj, Ideal.mul_mem_left _ _ (hdmem jj)⟩ := by
      rw [show a ^ (Finset.univ.sup Nf) = P.lift q from hq.symm, hsmul_dcl q jj]
    have hsub0 := (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem
      (⟨∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ), hmemsum⟩ : E'.ker)
      (⟨q * P.f jj, Ideal.mul_mem_left _ _ (hdmem jj)⟩ : E'.ker)).1
      (by rw [← hsum, ← hlhs, hβ])
    have hsub : (∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ)) -
        q * P.f jj ∈ E'.ker ^ 2 := hsub0
    refine ⟨q, hq, ?_⟩
    have hsplit : q * P.f jj =
        (∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ)) -
          ((∑ κ : Fin (P₀.n + k), bp κ * P.f (Fin.castAdd (P₀.m + l) κ)) - q * P.f jj) := by
      ring
    rw [hsplit]
    refine Ideal.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · rw [hfirst]
      refine Ideal.sum_mem _ fun κ _ => Ideal.mul_mem_left _ _ ?_
      exact Ideal.subset_span ⟨κ, (addVars_f_castAdd P₀ l wf hwrel κ).symm⟩
    · rw [← hker]
      exact hsub
  refine ⟨P, P₀.n + k, max N₂ (Finset.univ.sup Nf), hcn, hcm, ?_, ?_⟩
  · rw [← pow_sub_mul_pow a (le_max_left N₂ (Finset.univ.sup Nf))]
    exact Ideal.mul_mem_left _ _ hN₂
  · rw [← pow_mul_pow_sub a (le_max_right N₂ (Finset.univ.sup Nf))]
    refine standardCond2_mul P _ _ (P₀.n + k) hcm ?_
    refine standardCond2_of_forall_exists_lift P (a ^ (Finset.univ.sup Nf)) (P₀.n + k) hcm ?_
    intro j
    exact hcond ⟨(P₀.n + k) + j.1, by have := j.2; omega⟩

end Construction

/-- **Stacks 16.3.7 (e).** Let `R → A` be of finite presentation and `a ∈ A`. If `A_a` is
smooth over `R` and `Ω_{A_a/R}` is stably free, then `a ^ e` is strictly standard in `A` over
`R` for every sufficiently large `e`. -/
@[stacks 07EZ "clause (e), the implication (2) ⇒ `a ^ e` is strictly standard in `A` over \
`R` for all `e ≥ e_0`: the conclusion is `∃ e₀, ∀ e, e₀ ≤ e → ...`, the source's all \
sufficiently large powers, and not merely that some power is strictly standard"]
theorem exists_eventually_isStrictlyStandard_pow (S : SixStandardnessConditions.{u, v})
    (hS : Algebra.Smooth S.R (Localization.Away S.a) ∧
      Module.IsStablyFree (Localization.Away S.a)
        (KaehlerDifferential S.R (Localization.Away S.a))) :
    ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → IsStrictlyStandard (R := S.R) (S.a ^ e) := by
  classical
  rcases subsingleton_or_nontrivial (Localization.Away S.a) with hsub | hnt
  · -- `a` is nilpotent, so `a ^ e` is eventually `0`, which is strictly standard with `c = 0`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, S.a ^ N = 0 := by
      have h10 : algebraMap S.A (Localization.Away S.a) 1 =
          algebraMap S.A (Localization.Away S.a) 0 := Subsingleton.elim _ _
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers S.a)
        (Localization.Away S.a)).1 h10
      obtain ⟨N, hNc⟩ := (Submonoid.mem_powers_iff (c : S.A) S.a).1 c.2
      refine ⟨N, ?_⟩
      rw [hNc]
      simpa using hc
    obtain ⟨P⟩ := nonempty_presentation S.R S.A
    refine ⟨N, fun e he => ?_⟩
    have hzero : S.a ^ e = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
      rw [pow_add, hN, zero_mul]
    rw [hzero]
    refine ⟨P, 0, Nat.zero_le _, Nat.zero_le _, ⟨⟨fun _ => 0, ?_⟩, ?_⟩⟩
    · simp
    · refine standardCond2_of_forall_exists_lift P 0 0 _ fun j => ⟨0, ?_, ?_⟩
      · exact map_zero _
      · simp
  · have hsm := hS.1
    have := hsm.formallySmooth
    have : IsLocalizedModule (Submonoid.powers S.a)
        (KaehlerDifferential.map S.R S.R S.A (Localization.Away S.a)) :=
      omega_localization_total S.R S.A (Submonoid.powers S.a) (Localization.Away S.a)
    let eOm : (Localization.Away S.a) ⊗[S.A] Ω[S.A⁄S.R] ≃ₗ[Localization.Away S.a]
        Ω[Localization.Away S.a⁄S.R] :=
      (IsLocalizedModule.isBaseChange (Submonoid.powers S.a) (Localization.Away S.a)
        (KaehlerDifferential.map S.R S.R S.A (Localization.Away S.a))).equiv
    have : Module.IsStablyFree (Localization.Away S.a)
        ((Localization.Away S.a) ⊗[S.A] Ω[S.A⁄S.R]) := hS.2.equiv eOm.symm
    have : Module.Finite (Localization.Away S.a)
        ((Localization.Away S.a) ⊗[S.A] Ω[S.A⁄S.R]) := Module.Finite.equiv eOm.symm
    obtain ⟨P, c, N, hcn, hcm, hmin, hcond⟩ :=
      exists_presentation_of_isStablyFree (R := S.R) S.a (Localization.Away S.a)
    exact ⟨c * N + N, fun e he =>
      isStrictlyStandard_pow_of_mem_maximalMinorsIdeal S.a P c N hcn hcm hmin hcond e he⟩


/-! ### Smoothness, local complete intersections and localization away from an element -/

/-- A smooth algebra map is a local complete intersection. -/
public lemma isLocalCompleteIntersection_algebraMap_of_algebraSmooth {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    RingHom.IsLocalCompleteIntersection (algebraMap R S) := by
  have h := RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection (algebraMap R S)
  rw [toAlgebra_algebraMap] at h
  exact (h.mp (Algebra.Smooth.syntomic R S)).2

/-- If `R → B` is a scalar tower over which `B_b` is smooth, and `C_b` is smooth over `B_b`, then
`C_b` is smooth over `R`. -/
public lemma smooth_localizationAway_awayMap_of_smooth {R B C : Type*} [CommRing R] [CommRing B]
    [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] (b : B)
    [Algebra.Smooth R (Localization.Away b)]
    (h : letI : Algebra (Localization.Away b) (Localization.Away (algebraMap B C b)) :=
        (Localization.awayMap (algebraMap B C) b).toAlgebra
      Algebra.Smooth (Localization.Away b) (Localization.Away (algebraMap B C b))) :
    Algebra.Smooth R (Localization.Away (algebraMap B C b)) := by
  let _ : Algebra (Localization.Away b) (Localization.Away (algebraMap B C b)) :=
    (Localization.awayMap (algebraMap B C) b).toAlgebra
  let _ : Algebra.Smooth (Localization.Away b) (Localization.Away (algebraMap B C b)) := h
  have : IsScalarTower R (Localization.Away b) (Localization.Away (algebraMap B C b)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply R C (Localization.Away (algebraMap B C b)),
      IsScalarTower.algebraMap_apply R B C,
      IsScalarTower.algebraMap_apply R B (Localization.Away b)]
    show _ = Localization.awayMap (algebraMap B C) b _
    simp [Localization.awayMap, IsLocalization.Away.map]
  exact Algebra.Smooth.comp R (Localization.Away b) _

end Stacks.Smoothing

end
