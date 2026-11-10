module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.Different.Formula.SquarePresentation
public import StacksFrontier.RingTheory.Different.Formula.LocalizedCompleteIntersectionBaseChange

/-!
# Elementary moves between localized square presentations

Let `S` be a ring. A localized square presentation of an `S`-algebra is an isomorphism with
`S[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. This file gives the elementary ways of passing from one
such presentation to another without changing the algebra.

* Changing the relations and the localization element without changing the variables: if
  `h'` is a unit and every `f'_i` vanishes in `S[x, 1/h]/(f)`, and symmetrically, then the two
  algebras are identified compatibly with the maps from `S[x]`.
* Multiplying the relations by a square matrix `M` whose determinant is a unit in the algebra:
  `S[x, 1/h]/(f) = S[x, 1/(h det M)]/(M f)`.
* Adding graph variables: `S[x, 1/h]/(f) = S[x, y, 1/h]/(f, h^a y - ψ(x))`.

## Main definitions

* `Stacks.TateMap.lciLift`: the map out of `S[x, 1/h]/(f)` induced by a map out of `S[x]` that
  inverts `h` and kills each `f_i`.
* `Stacks.TateMap.lciEquivOfUnit`: the identification of two localized complete intersections in
  the same variables that are quotients of each other.
* `Stacks.TateMap.lciMatrixEquiv`: the change of relations by a matrix.
* `Stacks.TateMap.graphRelations` and `Stacks.TateMap.lciGraphEquiv`: adding graph variables.
-/

@[expose] public section

open MvPolynomial

universe u

namespace Stacks.TateMap

open Stacks.Discriminant

variable {S : Type u} [CommRing S]

section Lift

variable {n : ℕ} {T : Type*} [CommRing T] [Algebra S T] {h : MvPolynomial (Fin n) S}
  {f : Fin n → MvPolynomial (Fin n) S}

/-- The `S`-algebra map out of `S[x_1, …, x_n, 1/h]/(f_1, …, f_n)` induced by an `S`-algebra map
out of `S[x_1, …, x_n]` which inverts `h` and kills every `f_i`. -/
noncomputable def lciLift (φ : MvPolynomial (Fin n) S →ₐ[S] T) (hu : IsUnit (φ h))
    (hz : ∀ i, φ (f i) = 0) : localizedCompleteIntersection S n h f →ₐ[S] T :=
  Ideal.Quotient.liftₐ _ (IsLocalization.Away.liftAlgHom h (f := φ) hu) (by
    intro a ha
    refine (Ideal.span_le (I := RingHom.ker _)).mpr ?_ ha
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, localizedRelations,
      IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
    exact hz i)

/-- `lciLift φ` sends the image of a polynomial `p` to `φ p`. -/
@[simp]
theorem lciLift_algebraMap (φ : MvPolynomial (Fin n) S →ₐ[S] T) (hu : IsUnit (φ h))
    (hz : ∀ i, φ (f i) = 0) (p : MvPolynomial (Fin n) S) :
    lciLift φ hu hz (algebraMap (MvPolynomial (Fin n) S) _ p) = φ p := by
  rw [algebraMap_localizedCompleteIntersection_apply]
  exact IsLocalization.Away.lift_eq h hu p

/-- The `S`-algebra map `S[x_1, …, x_n] → S[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
noncomputable abbrev lciMk (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S) :
    MvPolynomial (Fin n) S →ₐ[S] localizedCompleteIntersection S n h f :=
  IsScalarTower.toAlgHom S _ _

/-- `lciMk h f` is the algebra map `S[x_1, …, x_n] → S[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
theorem lciMk_apply (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
    (p : MvPolynomial (Fin n) S) :
    lciMk h f p = algebraMap (MvPolynomial (Fin n) S) _ p :=
  rfl

/-- The image of `h` in `S[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is a unit. -/
theorem isUnit_lciMk (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S) :
    IsUnit (lciMk h f h) := by
  change IsUnit (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) S) (Localization.Away h) h))
  exact (IsLocalization.Away.algebraMap_isUnit h).map _

/-- Each relation `f_i` vanishes in `S[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
theorem lciMk_relation (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
    (i : Fin n) : lciMk h f (f i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

/-- Two `S`-algebra maps out of `S[x_1, …, x_n, 1/h]/(f_1, …, f_n)` agree as soon as they agree
after composing with `lciMk`. -/
theorem lci_algHom_ext {T : Type*} [CommRing T] [Algebra S T]
    {φ ψ : localizedCompleteIntersection S n h f →ₐ[S] T}
    (H : ∀ i, φ (lciMk h f (X i)) = ψ (lciMk h f (X i))) : φ = ψ :=
  localizedCompleteIntersection_algHom_ext H

/-- `lciLift φ` sends `lciMk h f p` to `φ p`. -/
@[simp]
theorem lciLift_lciMk (φ : MvPolynomial (Fin n) S →ₐ[S] T) (hu : IsUnit (φ h))
    (hz : ∀ i, φ (f i) = 0) (p : MvPolynomial (Fin n) S) :
    lciLift φ hu hz (lciMk h f p) = φ p :=
  lciLift_algebraMap φ hu hz p

end Lift

section SameVariables

variable {n : ℕ} {h h' : MvPolynomial (Fin n) S} {f f' : Fin n → MvPolynomial (Fin n) S}

/-- Two localized complete intersections in the same variables, each a quotient of the other,
are identified compatibly with the maps from the polynomial ring: if `h'` is a unit and every
`f'_i` vanishes in `S[x, 1/h]/(f)`, and `h` is a unit and every `f_i` vanishes in
`S[x, 1/h']/(f')`, then `S[x, 1/h]/(f) ≅ S[x, 1/h']/(f')`. -/
noncomputable def lciEquivOfUnit (hu : IsUnit (lciMk h' f' h)) (hz : ∀ i, lciMk h' f' (f i) = 0)
    (hu' : IsUnit (lciMk h f h')) (hz' : ∀ i, lciMk h f (f' i) = 0) :
    localizedCompleteIntersection S n h f ≃ₐ[S] localizedCompleteIntersection S n h' f' :=
  AlgEquiv.ofAlgHom (lciLift (lciMk h' f') hu hz) (lciLift (lciMk h f) hu' hz')
    (lci_algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, lciLift_lciMk, lciLift_lciMk, AlgHom.id_apply])
    (lci_algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, lciLift_lciMk, lciLift_lciMk, AlgHom.id_apply])

/-- `lciEquivOfUnit` sends `lciMk h f p` to `lciMk h' f' p`. -/
@[simp]
theorem lciEquivOfUnit_lciMk (hu : IsUnit (lciMk h' f' h)) (hz : ∀ i, lciMk h' f' (f i) = 0)
    (hu' : IsUnit (lciMk h f h')) (hz' : ∀ i, lciMk h f (f' i) = 0)
    (p : MvPolynomial (Fin n) S) :
    lciEquivOfUnit hu hz hu' hz' (lciMk h f p) = lciMk h' f' p := by
  rw [lciEquivOfUnit, AlgEquiv.ofAlgHom_apply, lciLift_lciMk]

end SameVariables

section Matrix

variable {n : ℕ} {T : Type*} [CommRing T] [Algebra S T]

/-- If every `f_j` vanishes under `φ`, so does every entry of `M f`. -/
theorem map_mulVec_eq_zero (φ : MvPolynomial (Fin n) S →ₐ[S] T)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) S))
    {f : Fin n → MvPolynomial (Fin n) S} (hf : ∀ j, φ (f j) = 0) (i : Fin n) :
    φ ((M.mulVec f) i) = 0 := by
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hf]

/-- If every entry of `M f` vanishes under `φ` and `φ (det M)` is a unit, then every `f_i`
vanishes under `φ`. -/
theorem map_eq_zero_of_mulVec (φ : MvPolynomial (Fin n) S →ₐ[S] T)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) S))
    {f : Fin n → MvPolynomial (Fin n) S} (hd : IsUnit (φ M.det))
    (hf : ∀ j, φ ((M.mulVec f) j) = 0) (i : Fin n) : φ (f i) = 0 := by
  have key : M.det * f i = (M.adjugate.mulVec (M.mulVec f)) i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul]
  rw [← hd.mul_right_eq_zero, ← map_mul, key]
  exact map_mulVec_eq_zero φ _ hf i

/-- If `M` is a square matrix over `S[x_1, …, x_n]` whose
determinant is a unit in `S[x, 1/h]/(f)`, then `S[x, 1/h]/(f) ≅ S[x, 1/(h det M)]/(M f)`,
compatibly with the maps from the polynomial ring. -/
noncomputable def lciMatrixEquiv (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) S)) (hd : IsUnit (lciMk h f M.det)) :
    localizedCompleteIntersection S n h f ≃ₐ[S]
      localizedCompleteIntersection S n (h * M.det) (M.mulVec f) :=
  have hhd : IsUnit (lciMk (h * M.det) (M.mulVec f) h * lciMk (h * M.det) (M.mulVec f) M.det) :=
    (map_mul (lciMk (h * M.det) (M.mulVec f)) h M.det) ▸ isUnit_lciMk _ _
  lciEquivOfUnit (isUnit_of_mul_isUnit_left hhd)
    (map_eq_zero_of_mulVec _ M (isUnit_of_mul_isUnit_right hhd) (lciMk_relation _ _))
    ((map_mul (lciMk h f) h M.det).symm ▸ (isUnit_lciMk h f).mul hd)
    (map_mulVec_eq_zero _ M (lciMk_relation h f))

/-- `lciMatrixEquiv` sends the class of a polynomial `p` to the class of `p`. -/
@[simp]
theorem lciMatrixEquiv_lciMk (h : MvPolynomial (Fin n) S)
    (f : Fin n → MvPolynomial (Fin n) S) (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) S))
    (hd : IsUnit (lciMk h f M.det)) (p : MvPolynomial (Fin n) S) :
    lciMatrixEquiv h f M hd (lciMk h f p) = lciMk _ _ p :=
  lciEquivOfUnit_lciMk _ _ _ _ p

end Matrix

section Graph

variable {n m N : ℕ} (e : Fin n ⊕ Fin m ≃ Fin N) (σ : Fin n ⊕ Fin m ≃ Fin N)
  (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
  (ψ : Fin m → MvPolynomial (Fin n) S) (a : ℕ)

/-- The inclusion of the old variables `x_1, …, x_n` among the variables indexed by `Fin N`. -/
noncomputable abbrev graphIncl : MvPolynomial (Fin n) S →ₐ[S] MvPolynomial (Fin N) S :=
  rename fun i ↦ e (.inl i)

/-- The relations `f_1, …, f_n, h^a y_1 - ψ_1(x), …, h^a y_m - ψ_m(x)` in the variables
`x_i = X (e (inl i))` and `y_j = X (e (inr j))`, the relation attached to `c : Fin n ⊕ Fin m`
sitting at index `σ c`. -/
noncomputable def graphRelations : Fin N → MvPolynomial (Fin N) S := fun k ↦
  Sum.elim (fun i ↦ graphIncl e (f i))
    (fun j ↦ graphIncl e h ^ a * X (e (.inr j)) - graphIncl e (ψ j)) (σ.symm k)

/-- The relation at index `σ (inl i)` is `f_i(x)`. -/
@[simp]
theorem graphRelations_inl (i : Fin n) :
    graphRelations e σ h f ψ a (σ (.inl i)) = graphIncl e (f i) := by
  simp [graphRelations]

/-- The relation at index `σ (inr j)` is `h^a y_j - ψ_j(x)`. -/
@[simp]
theorem graphRelations_inr (j : Fin m) :
    graphRelations e σ h f ψ a (σ (.inr j)) =
      graphIncl e h ^ a * X (e (.inr j)) - graphIncl e (ψ j) := by
  simp [graphRelations]

/-- In any localization of `S[x, y]/(f, h^a y - ψ(x))`, `h^a y_j = ψ_j(x)`. -/
private theorem lciMk_graphIncl_pow_mul_X (h' : MvPolynomial (Fin N) S) (j : Fin m) :
    lciMk h' (graphRelations e σ h f ψ a) (graphIncl e h) ^ a *
      lciMk h' (graphRelations e σ h f ψ a) (X (e (.inr j))) =
        lciMk h' (graphRelations e σ h f ψ a) (graphIncl e (ψ j)) := by
  rw [← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub, ← graphRelations_inr e σ h f ψ a j]
  exact lciMk_relation _ _ _

/-- The map `S[x, 1/h]/(f) → S[x, y, 1/h]/(f, h^a y - ψ(x))` on the old variables. -/
noncomputable def lciGraphHom :
    localizedCompleteIntersection S n h f →ₐ[S]
      localizedCompleteIntersection S N (graphIncl e h) (graphRelations e σ h f ψ a) :=
  lciLift ((lciMk _ _).comp (graphIncl e)) (by
      rw [AlgHom.comp_apply]
      exact isUnit_lciMk _ _)
    (fun i ↦ by
      rw [AlgHom.comp_apply, ← graphRelations_inl e σ h f ψ a i]
      exact lciMk_relation _ _ _)

/-- `lciGraphHom` sends the class of a polynomial `p` in the old variables to the class of
`graphIncl e p`. -/
@[simp]
theorem lciGraphHom_lciMk (p : MvPolynomial (Fin n) S) :
    lciGraphHom e σ h f ψ a (lciMk h f p) = lciMk _ _ (graphIncl e p) :=
  lciLift_lciMk _ _ _ p

/-- The images of the variables under the inverse of `lciGraphHom`: `x_i ↦ x_i` and
`y_j ↦ ψ_j(x) / h^a`. -/
noncomputable def graphInvImage (k : Fin N) : localizedCompleteIntersection S n h f :=
  Sum.elim (fun i ↦ lciMk h f (X i))
    (fun j ↦ lciMk h f (ψ j) * ((isUnit_lciMk h f).unit⁻¹ : (localizedCompleteIntersection S n h
      f)ˣ) ^ a) (e.symm k)

/-- Evaluating at `graphInvImage` after including the old variables is `lciMk h f`. -/
theorem aeval_graphInvImage_comp_graphIncl :
    (aeval (graphInvImage e h f ψ a)).comp (graphIncl e) = lciMk h f :=
  MvPolynomial.algHom_ext fun i ↦ by
    simp [graphInvImage, graphIncl]

/-- Evaluating `graphIncl e p` at `graphInvImage` gives `lciMk h f p`. -/
theorem aeval_graphInvImage_graphIncl (p : MvPolynomial (Fin n) S) :
    aeval (graphInvImage e h f ψ a) (graphIncl e p) = lciMk h f p :=
  congrArg (fun φ : MvPolynomial (Fin n) S →ₐ[S] _ ↦ φ p)
    (aeval_graphInvImage_comp_graphIncl e h f ψ a)

/-- The map `S[x, y, 1/h]/(f, h^a y - ψ(x)) → S[x, 1/h]/(f)` sending `y_j` to `ψ_j(x) / h^a`. -/
noncomputable def lciGraphInv :
    localizedCompleteIntersection S N (graphIncl e h) (graphRelations e σ h f ψ a) →ₐ[S]
      localizedCompleteIntersection S n h f :=
  lciLift (aeval (graphInvImage e h f ψ a))
    (by
      rw [aeval_graphInvImage_graphIncl]
      exact isUnit_lciMk h f)
    (by
      intro k
      obtain ⟨c, rfl⟩ := σ.surjective k
      rcases c with i | j
      · rw [graphRelations_inl, aeval_graphInvImage_graphIncl]
        exact lciMk_relation h f i
      · rw [graphRelations_inr, map_sub, map_mul, map_pow, aeval_graphInvImage_graphIncl,
          aeval_graphInvImage_graphIncl, aeval_X]
        simp only [graphInvImage, Equiv.symm_apply_apply, Sum.elim_inr]
        rw [mul_left_comm, ← mul_pow, IsUnit.mul_val_inv, one_pow, mul_one, sub_self])

/-- `lciGraphInv` sends the class of a polynomial `p` to its evaluation at `graphInvImage`. -/
@[simp]
theorem lciGraphInv_lciMk (p : MvPolynomial (Fin N) S) :
    lciGraphInv e σ h f ψ a (lciMk _ _ p) = aeval (graphInvImage e h f ψ a) p :=
  lciLift_lciMk _ _ _ p

/-- `S[x, 1/h]/(f) ≅ S[x, y, 1/h]/(f, h^a y - ψ(x))`, sending `x_i` to
`x_i`; the inverse sends `y_j` to `ψ_j(x) / h^a`. -/
noncomputable def lciGraphEquiv :
    localizedCompleteIntersection S n h f ≃ₐ[S]
      localizedCompleteIntersection S N (graphIncl e h) (graphRelations e σ h f ψ a) :=
  AlgEquiv.ofAlgHom (lciGraphHom e σ h f ψ a) (lciGraphInv e σ h f ψ a)
    (lci_algHom_ext fun k ↦ by
      obtain ⟨c, rfl⟩ := e.surjective k
      rw [AlgHom.comp_apply, lciGraphInv_lciMk, aeval_X, AlgHom.id_apply]
      rcases c with i | j
      · simp only [graphInvImage, Equiv.symm_apply_apply, Sum.elim_inl, lciGraphHom_lciMk,
          graphIncl, rename_X]
      · simp only [graphInvImage, Equiv.symm_apply_apply, Sum.elim_inr, map_mul, map_pow,
          lciGraphHom_lciMk]
        set H := lciMk (S := S) (graphIncl e h) (graphRelations e σ h f ψ a)
        have hrel : H (graphIncl e h) ^ a * H (X (e (.inr j))) = H (graphIncl e (ψ j)) := by
          rw [← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub, ← graphRelations_inr e σ h f ψ a j]
          exact lciMk_relation _ _ _
        have hinv : lciGraphHom e σ h f ψ a
            ((isUnit_lciMk h f).unit⁻¹ : (localizedCompleteIntersection S n h f)ˣ) *
              H (graphIncl e h) = 1 := by
          rw [← lciGraphHom_lciMk, ← map_mul, IsUnit.val_inv_mul, map_one]
        rw [← hrel, mul_comm, ← mul_assoc, ← mul_pow, hinv, one_pow, one_mul])
    (lci_algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, lciGraphHom_lciMk, lciGraphInv_lciMk,
        aeval_graphInvImage_graphIncl, AlgHom.id_apply])

/-- `lciGraphEquiv` sends the class of a polynomial `p` in the old variables to the class of
`graphIncl e p`. -/
@[simp]
theorem lciGraphEquiv_lciMk (p : MvPolynomial (Fin n) S) :
    lciGraphEquiv e σ h f ψ a (lciMk h f p) = lciMk _ _ (graphIncl e p) :=
  lciGraphHom_lciMk e σ h f ψ a p

/-- The inverse of `lciGraphEquiv` sends the class of a polynomial `p` to its evaluation at
`graphInvImage`. -/
@[simp]
theorem lciGraphEquiv_symm_lciMk (p : MvPolynomial (Fin N) S) :
    (lciGraphEquiv e σ h f ψ a).symm (lciMk _ _ p) = aeval (graphInvImage e h f ψ a) p :=
  lciGraphInv_lciMk e σ h f ψ a p

end Graph

section Away

variable {n : ℕ} (h p : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)

/-- Every element of the ideal `(f_1, …, f_n)` of `S[x_1, …, x_n]` vanishes in
`S[x, 1/h]/(f)`. -/
theorem lciMk_eq_zero_of_mem {q : MvPolynomial (Fin n) S} (hq : q ∈ Ideal.span (Set.range f)) :
    lciMk h f q = 0 :=
  (Ideal.span_le (I := RingHom.ker (lciMk h f))).mpr
    (by rintro _ ⟨i, rfl⟩; exact lciMk_relation h f i) hq

/-- A polynomial vanishing in `S[x, 1/h]/(f)` lies in `(f_1, …, f_n)` after multiplication by a
power of `h`. -/
private theorem exists_pow_mul_mem_of_lciMk_eq_zero_aux {q : MvPolynomial (Fin n) S}
    (hq : lciMk h f q = 0) : ∃ N : ℕ, h ^ N * q ∈ Ideal.span (Set.range f) := by
  have hmem : algebraMap (MvPolynomial (Fin n) S) (Localization.Away h) q ∈
      (Ideal.span (Set.range f)).map (algebraMap _ _) := by
    rw [← span_range_localizedRelations]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  obtain ⟨⟨⟨x, hx⟩, ⟨-, M, rfl⟩⟩, hxq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h) _).mp hmem
  rw [← map_mul] at hxq
  obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq h hxq
  refine ⟨N + M, ?_⟩
  have : h ^ N * (q * h ^ M) ∈ Ideal.span (Set.range f) := hN ▸ Ideal.mul_mem_left _ _ hx
  rw [pow_add]
  convert this using 1
  ring

/-- The map `S[x, 1/h]/(f) → S[x, 1/(h p)]/(f)`. -/
noncomputable def lciAwayHom :
    localizedCompleteIntersection S n h f →ₐ[S] localizedCompleteIntersection S n (h * p) f :=
  lciLift (lciMk (h * p) f)
    (isUnit_of_mul_isUnit_left ((map_mul (lciMk (h * p) f) h p) ▸ isUnit_lciMk (h * p) f))
    (lciMk_relation _ _)

/-- `lciAwayHom` sends `lciMk h f q` to `lciMk (h * p) f q`. -/
@[simp]
theorem lciAwayHom_lciMk (q : MvPolynomial (Fin n) S) :
    lciAwayHom h p f (lciMk h f q) = lciMk (h * p) f q :=
  lciLift_lciMk _ _ _ q

/-- `S[x, 1/(h p)]/(f)` is the localization of
`S[x, 1/h]/(f)` away from the image of `p`. -/
theorem isLocalization_lciAwayHom :
    letI := (lciAwayHom h p f).toRingHom.toAlgebra
    IsLocalization.Away (lciMk h f p) (localizedCompleteIntersection S n (h * p) f) := by
  let := (lciAwayHom h p f).toRingHom.toAlgebra
  have hφmk : ∀ q, algebraMap (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection S n (h * p) f) (lciMk h f q) = lciMk (h * p) f q :=
    lciAwayHom_lciMk h p f
  have hhp : IsUnit (lciMk (h * p) f h * lciMk (h * p) f p) :=
    (map_mul (lciMk (h * p) f) h p) ▸ isUnit_lciMk (h * p) f
  have hu := isUnit_lciMk h f
  set U : localizedCompleteIntersection S n h f :=
    ((hu.unit⁻¹ : (localizedCompleteIntersection S n h f)ˣ) : localizedCompleteIntersection S n h f)
    with hU
  have hUH : algebraMap (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection S n (h * p) f) U * lciMk (h * p) f h = 1 := by
    rw [← hφmk, ← map_mul, hU, IsUnit.val_inv_mul, map_one]
  refine IsLocalization.Away.mk _ ?_ (fun z ↦ ?_) (fun a b hab ↦ ?_)
  · rw [hφmk]
    exact isUnit_of_mul_isUnit_right hhp
  · obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨k, a, hw⟩ := IsLocalization.Away.surj (h * p) w
    have hz : Ideal.Quotient.mk _ w * (lciMk (h * p) f h ^ k * lciMk (h * p) f p ^ k) =
        lciMk (h * p) f a := by
      have := congrArg (Ideal.Quotient.mk
        (Ideal.span (Set.range (localizedRelations S n (h * p) f)))) hw
      rw [map_mul, map_pow] at this
      rw [← mul_pow, ← map_mul]
      exact this
    have hUk : algebraMap (localizedCompleteIntersection S n h f)
        (localizedCompleteIntersection S n (h * p) f) U ^ k * lciMk (h * p) f h ^ k = 1 := by
      rw [← mul_pow, hUH, one_pow]
    refine ⟨k, lciMk h f a * U ^ k, ?_⟩
    rw [map_mul, map_pow, hφmk, hφmk]
    linear_combination (algebraMap (localizedCompleteIntersection S n h f)
        (localizedCompleteIntersection S n (h * p) f) U ^ k) * hz -
      (Ideal.Quotient.mk _ w * lciMk (h * p) f p ^ k) * hUk
  · obtain ⟨w, hw0⟩ := Ideal.Quotient.mk_surjective (a - b)
    obtain ⟨k, q, hw⟩ := IsLocalization.Away.surj h w
    have hc : (a - b) * lciMk h f h ^ k = lciMk h f q := by
      rw [← hw0]
      have := congrArg (Ideal.Quotient.mk
        (Ideal.span (Set.range (localizedRelations S n h f)))) hw
      rw [map_mul, map_pow] at this
      exact this
    have hq : lciMk (h * p) f q = 0 := by
      rw [← hφmk, ← hc, map_mul, map_sub, hab, sub_self, zero_mul]
    obtain ⟨N, hmem'⟩ := exists_pow_mul_mem_of_lciMk_eq_zero_aux (h * p) f hq
    have h0 := lciMk_eq_zero_of_mem h f hmem'
    rw [map_mul, map_pow, map_mul, mul_pow, ← hc] at h0
    refine ⟨N, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    have hhk : IsUnit (lciMk h f h ^ N * lciMk h f h ^ k) := (hu.pow _).mul (hu.pow _)
    refine (hhk.mul_right_eq_zero).mp ?_
    linear_combination h0

end Away

section Kernel

variable {n : ℕ} (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)

/-- A polynomial vanishing in `S[x, 1/h]/(f)` lies in `(f_1, …, f_n)` after multiplication by a
power of `h`. -/
theorem exists_pow_mul_mem_of_lciMk_eq_zero {q : MvPolynomial (Fin n) S} (hq : lciMk h f q = 0) :
    ∃ N : ℕ, h ^ N * q ∈ Ideal.span (Set.range f) :=
  exists_pow_mul_mem_of_lciMk_eq_zero_aux h f hq

/-- The kernel of `S[x_1, …, x_n] → S[x_1, …, x_n]/(f_1, …, f_n)`, written with the trivial
localization element. -/
theorem lciMk_one_eq_zero_iff {f : Fin n → MvPolynomial (Fin n) S} {q : MvPolynomial (Fin n) S} :
    lciMk 1 f q = 0 ↔ q ∈ Ideal.span (Set.range f) := by
  refine ⟨fun hq ↦ ?_, lciMk_eq_zero_of_mem 1 f⟩
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_of_lciMk_eq_zero 1 f hq
  simpa using hN

/-- With trivial localization element, `lciMk 1 r` is surjective. -/
theorem lciMk_one_surjective (r : Fin n → MvPolynomial (Fin n) S) :
    Function.Surjective (lciMk (1 : MvPolynomial (Fin n) S) r) := by
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨k, a, hw⟩ := IsLocalization.Away.surj (1 : MvPolynomial (Fin n) S) w
  rw [map_one, one_pow, mul_one] at hw
  exact ⟨a, by rw [lciMk_apply, algebraMap_localizedCompleteIntersection_apply, hw]⟩

/-- `S[x_1, …, x_n]/(f_1, …, f_n)` written as a quotient of the polynomial ring is the
localized complete intersection with trivial localization element. -/
noncomputable def lciOneEquiv (f : Fin n → MvPolynomial (Fin n) S) :
    (MvPolynomial (Fin n) S ⧸ Ideal.span (Set.range f)) ≃ₐ[S]
      localizedCompleteIntersection S n 1 f :=
  (Ideal.quotientEquivAlgOfEq S (by ext q; exact lciMk_one_eq_zero_iff.symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lciMk_one_surjective f))

/-- `lciOneEquiv` sends the class of `q` in `S[x]/(f)` to `lciMk 1 f q`. -/
@[simp]
theorem lciOneEquiv_mk (f : Fin n → MvPolynomial (Fin n) S) (q : MvPolynomial (Fin n) S) :
    lciOneEquiv f (Ideal.Quotient.mk _ q) = lciMk 1 f q :=
  rfl

end Kernel

section Conormal

variable {N : ℕ}

/-- Let `r` and `r'` be two families of `N` polynomials in `N` variables over `S` with
`S[x]/(r)` quasi-finite over `S`, and let `r = M r'` and `r' = M' r`. Then `det M` is a unit in
`S[x]/(r)`. -/
theorem isUnit_det_of_mulVec_eq (r r' : Fin N → MvPolynomial (Fin N) S)
    [Algebra.QuasiFinite S (MvPolynomial (Fin N) S ⧸ Ideal.span (Set.range r))]
    (M M' : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) S))
    (hM : r = M.mulVec r') (hM' : r' = M'.mulVec r) :
    IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range r)) M.det) := by
  classical
  set Q := MvPolynomial (Fin N) S ⧸ Ideal.span (Set.range r)
  let P : Algebra.Presentation S Q (Fin N) (Fin N) := Algebra.Presentation.naive (v := r)
  have : P.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection_of_card_eq rfl
  obtain ⟨b, hb⟩ := P.exists_basis_cotangent_relation
  have hr : r = (M * M').mulVec r := by
    rw [← Matrix.mulVec_mulVec, ← hM', ← hM]
  have key : ∀ k l, Ideal.Quotient.mk (Ideal.span (Set.range r)) ((M * M' - 1) k l) = 0 := by
    intro k
    have hsum : ∑ l, (M * M' - 1) k l * r l = 0 := by
      have := congrFun hr k
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← this, sub_self]
    let c : Fin N → P.toExtension.Ring := fun l ↦ (M * M' - 1) k l
    have hzero : (∑ l, c l • (⟨r l, P.relation_mem_ker l⟩ : P.toExtension.ker)) = 0 :=
      Subtype.ext (by
        rw [AddSubmonoidClass.coe_finsetSum]
        simp only [c, ZeroMemClass.coe_zero]
        exact hsum)
    have hcot := congrArg (Algebra.Extension.Cotangent.mk (P := P.toExtension)) hzero
    rw [map_sum, map_zero] at hcot
    have hcot' : ∑ l, (Ideal.Quotient.mk (Ideal.span (Set.range r)) ((M * M' - 1) k l)) • b l =
        0 := by
      rw [← hcot]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_smul, hb l]
      exact algebraMap_smul Q (c l) _
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hcot'
  have hone : (Ideal.Quotient.mk (Ideal.span (Set.range r))).mapMatrix (M * M') = 1 := by
    ext k l
    have := key k l
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet := congrArg Matrix.det hone
  rw [map_mul, Matrix.det_mul, Matrix.det_one] at hdet
  rw [RingHom.map_det]
  exact IsUnit.of_mul_eq_one _ hdet

end Conormal

section Global

variable {n : ℕ} (H : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)

/-- The relations `f_1, …, f_n, H t - 1` of the global presentation of `S[x, 1/H]/(f)`, in the
variables `x_1, …, x_n, t`. -/
noncomputable abbrev globalRelations : Fin (n + 1) → MvPolynomial (Fin (n + 1)) S :=
  graphRelations finSumFinEquiv finSumFinEquiv H f (fun _ ↦ 1) 1

/-- The image of `H` in `S[x, t]/(f, H t - 1)` is a unit. -/
theorem isUnit_lciMk_one_graphIncl :
    IsUnit (lciMk 1 (globalRelations H f) (graphIncl finSumFinEquiv H)) := by
  have hrel := lciMk_graphIncl_pow_mul_X finSumFinEquiv finSumFinEquiv H f (fun _ ↦ 1) 1 1
    (0 : Fin 1)
  rw [pow_one, map_one, map_one] at hrel
  exact IsUnit.of_mul_eq_one _ hrel

/-- `S[x, 1/H]/(f) ≅ S[x, t]/(f, H t - 1)`, sending `x_i` to
`x_i`. -/
noncomputable def lciGlobalEquiv :
    localizedCompleteIntersection S n H f ≃ₐ[S]
      localizedCompleteIntersection S (n + 1) 1 (globalRelations H f) :=
  (lciGraphEquiv finSumFinEquiv finSumFinEquiv H f (fun _ ↦ 1) 1).trans
    (lciEquivOfUnit (isUnit_lciMk_one_graphIncl H f) (lciMk_relation _ _)
      (by rw [map_one]; exact isUnit_one) (lciMk_relation _ _))

/-- `lciGlobalEquiv` sends the class of a polynomial `p` in `x` to the class of
`graphIncl finSumFinEquiv p`. -/
@[simp]
theorem lciGlobalEquiv_lciMk (p : MvPolynomial (Fin n) S) :
    lciGlobalEquiv H f (lciMk H f p) = lciMk 1 _ (graphIncl finSumFinEquiv p) := by
  rw [lciGlobalEquiv, AlgEquiv.trans_apply, lciGraphEquiv_lciMk, lciEquivOfUnit_lciMk]

end Global

section Decomposition

variable {B : Type*} [CommRing B] [Algebra S B] {n m : ℕ} {r : Fin n → MvPolynomial (Fin n) S}
  {s : Fin m → MvPolynomial (Fin m) S}

/-- The variables `x_1, …, x_n, y_1, …, y_m` in the order `x, y`. -/
abbrev decompLeft (n m : ℕ) : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv

/-- The variables `x_1, …, x_n, y_1, …, y_m`, the `y` listed first. -/
abbrev decompRight (n m : ℕ) : Fin m ⊕ Fin n ≃ Fin (n + m) :=
  (Equiv.sumComm (Fin m) (Fin n)).trans finSumFinEquiv

/-- Under `decompRight`, the variable `x_i` sits where it does under `decompLeft`. -/
theorem decompRight_inr (i : Fin n) : decompRight n m (.inr i) = decompLeft n m (.inl i) := rfl

/-- Under `decompRight`, the variable `y_j` sits where it does under `decompLeft`. -/
theorem decompRight_inl (j : Fin m) : decompRight n m (.inl j) = decompLeft n m (.inr j) := rfl

variable (e₁ : localizedCompleteIntersection S n 1 r ≃ₐ[S] B)
  (e₂ : localizedCompleteIntersection S m 1 s ≃ₐ[S] B)

/-- A polynomial `ψ_j(x)` representing the image of `y_j` in the first presentation. -/
noncomputable def decompψ (j : Fin m) : MvPolynomial (Fin n) S :=
  Function.surjInv (lciMk_one_surjective r) (e₁.symm (e₂ (lciMk 1 s (X j))))

/-- A polynomial `φ_i(y)` representing the image of `x_i` in the second presentation. -/
noncomputable def decompφ (i : Fin n) : MvPolynomial (Fin m) S :=
  Function.surjInv (lciMk_one_surjective s) (e₂.symm (e₁ (lciMk 1 r (X i))))

/-- The class of `decompψ e₁ e₂ j` in the first presentation is the image of `y_j`. -/
theorem lciMk_decompψ (j : Fin m) :
    lciMk 1 r (decompψ e₁ e₂ j) = e₁.symm (e₂ (lciMk 1 s (X j))) :=
  Function.surjInv_eq _ _

/-- The class of `decompφ e₁ e₂ i` in the second presentation is the image of `x_i`. -/
theorem lciMk_decompφ (i : Fin n) :
    lciMk 1 s (decompφ e₁ e₂ i) = e₂.symm (e₁ (lciMk 1 r (X i))) :=
  Function.surjInv_eq _ _

/-- The relations `r(x), y - ψ(x)` in the variables `x, y`. -/
noncomputable abbrev decompRelLeft : Fin (n + m) → MvPolynomial (Fin (n + m)) S :=
  graphRelations (decompLeft n m) (decompLeft n m) 1 r (decompψ e₁ e₂) 0

/-- The relations `x - φ(y), s(y)` in the variables `x, y`. -/
noncomputable abbrev decompRelRight : Fin (n + m) → MvPolynomial (Fin (n + m)) S :=
  graphRelations (decompRight n m) (decompRight n m) 1 s (decompφ e₁ e₂) 0

/-- The two graph presentations, with the trivial localization element written as `1`. -/
noncomputable def decompLeftEquiv :
    localizedCompleteIntersection S n 1 r ≃ₐ[S]
      localizedCompleteIntersection S (n + m) 1 (decompRelLeft e₁ e₂) :=
  (lciGraphEquiv (decompLeft n m) (decompLeft n m) 1 r (decompψ e₁ e₂) 0).trans
    (localizedCompleteIntersectionCongr (map_one _) rfl)

/-- The second graph presentation, with the trivial localization element written as `1`. -/
noncomputable def decompRightEquiv :
    localizedCompleteIntersection S m 1 s ≃ₐ[S]
      localizedCompleteIntersection S (n + m) 1 (decompRelRight e₁ e₂) :=
  (lciGraphEquiv (decompRight n m) (decompRight n m) 1 s (decompφ e₁ e₂) 0).trans
    (localizedCompleteIntersectionCongr (map_one _) rfl)

/-- The identification of the two graph presentations through `B`. -/
noncomputable def decompEquiv :
    localizedCompleteIntersection S (n + m) 1 (decompRelLeft e₁ e₂) ≃ₐ[S]
      localizedCompleteIntersection S (n + m) 1 (decompRelRight e₁ e₂) :=
  (decompLeftEquiv e₁ e₂).symm.trans (e₁.trans (e₂.symm.trans (decompRightEquiv e₁ e₂)))

/-- `localizedCompleteIntersectionCongr` sends `lciMk h f p` to `lciMk h' f p`. -/
theorem congr_lciMk {N : ℕ} {h h' : MvPolynomial (Fin N) S} {f : Fin N → MvPolynomial (Fin N) S}
    (hh : h = h') (p : MvPolynomial (Fin N) S) :
    localizedCompleteIntersectionCongr hh rfl (lciMk h f p) = lciMk h' f p :=
  localizedCompleteIntersectionCongr_algebraMap hh rfl p

/-- The inverse of `localizedCompleteIntersectionCongr` sends `lciMk h' f p` to `lciMk h f p`. -/
theorem congr_symm_lciMk {N : ℕ} {h h' : MvPolynomial (Fin N) S}
    {f : Fin N → MvPolynomial (Fin N) S} (hh : h = h') (p : MvPolynomial (Fin N) S) :
    (localizedCompleteIntersectionCongr hh rfl).symm (lciMk h' f p) = lciMk h f p := by
  rw [AlgEquiv.symm_apply_eq, congr_lciMk]

/-- The identification of the two graph presentations is the identity on the polynomial ring. -/
theorem decompEquiv_lciMk (p : MvPolynomial (Fin (n + m)) S) :
    decompEquiv e₁ e₂ (lciMk 1 _ p) = lciMk 1 _ p := by
  suffices H : (decompEquiv e₁ e₂).toAlgHom.comp (lciMk _ _) = lciMk _ _ from
    congrArg (fun φ : MvPolynomial (Fin (n + m)) S →ₐ[S] _ ↦ φ p) H
  refine MvPolynomial.algHom_ext fun k ↦ ?_
  obtain ⟨c, rfl⟩ := (decompLeft n m).surjective k
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, decompEquiv]
  simp only [AlgEquiv.trans_apply, decompLeftEquiv, decompRightEquiv, AlgEquiv.symm_trans_apply,
    congr_symm_lciMk, lciGraphEquiv_symm_lciMk, aeval_X]
  rcases c with i | j
  · simp only [graphInvImage, Equiv.symm_apply_apply, Sum.elim_inl]
    rw [← lciMk_decompφ, lciGraphEquiv_lciMk, congr_lciMk, ← decompRight_inr]
    have hrel := lciMk_graphIncl_pow_mul_X (decompRight n m) (decompRight n m) 1 s
      (decompφ e₁ e₂) 0 1 i
    rw [pow_zero, one_mul] at hrel
    exact hrel.symm
  · simp only [graphInvImage, Equiv.symm_apply_apply, Sum.elim_inr, pow_zero, mul_one]
    rw [lciMk_decompψ, AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply, lciGraphEquiv_lciMk,
      congr_lciMk, graphIncl, rename_X, decompRight_inl]

/-- The inverse of the identification of the two graph presentations is the identity on the
polynomial ring. -/
theorem decompEquiv_symm_lciMk (p : MvPolynomial (Fin (n + m)) S) :
    (decompEquiv e₁ e₂).symm (lciMk 1 _ p) = lciMk 1 _ p := by
  rw [AlgEquiv.symm_apply_eq, decompEquiv_lciMk]

/-- The two graph presentations `(r(x), y - ψ(x))` and `(x - φ(y), s(y))` generate the same
ideal of `S[x, y]`. -/
theorem span_decompRelLeft_eq :
    Ideal.span (Set.range (decompRelLeft e₁ e₂)) =
      Ideal.span (Set.range (decompRelRight e₁ e₂)) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine lciMk_one_eq_zero_iff.mp ?_
    rw [← decompEquiv_lciMk, lciMk_relation, map_zero]
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine lciMk_one_eq_zero_iff.mp ?_
    rw [← decompEquiv_symm_lciMk, lciMk_relation, map_zero]

/-- Given two presentations
`B ≅ S[x]/(r)` and `B ≅ S[y]/(s)` of a quasi-finite `S`-algebra, the graph presentations
`(r(x), y - ψ(x))` and `(x - φ(y), s(y))` of `B` in the variables `x, y` differ by square matrices
`M`, `M'`, and `det M` is a unit in `B`. -/
theorem exists_matrix_decomp [Algebra.QuasiFinite S B] :
    ∃ M M' : Matrix (Fin (n + m)) (Fin (n + m)) (MvPolynomial (Fin (n + m)) S),
      decompRelLeft e₁ e₂ = M.mulVec (decompRelRight e₁ e₂) ∧
      decompRelRight e₁ e₂ = M'.mulVec (decompRelLeft e₁ e₂) ∧
      IsUnit (lciMk 1 (decompRelLeft e₁ e₂) M.det) := by
  have hspan := span_decompRelLeft_eq e₁ e₂
  have h1 : ∀ k, ∃ c : Fin (n + m) → MvPolynomial (Fin (n + m)) S,
      ∑ l, c l * decompRelRight e₁ e₂ l = decompRelLeft e₁ e₂ k := fun k ↦
    Ideal.mem_span_range_iff_exists_fun.mp (hspan ▸ Ideal.subset_span ⟨k, rfl⟩)
  have h2 : ∀ k, ∃ c : Fin (n + m) → MvPolynomial (Fin (n + m)) S,
      ∑ l, c l * decompRelLeft e₁ e₂ l = decompRelRight e₁ e₂ k := fun k ↦
    Ideal.mem_span_range_iff_exists_fun.mp (hspan.symm ▸ Ideal.subset_span ⟨k, rfl⟩)
  choose c hc using h1
  choose c' hc' using h2
  have hM : decompRelLeft e₁ e₂ = (Matrix.of c).mulVec (decompRelRight e₁ e₂) := by
    funext k
    simp [Matrix.mulVec, dotProduct, hc]
  have hM' : decompRelRight e₁ e₂ = (Matrix.of c').mulVec (decompRelLeft e₁ e₂) := by
    funext k
    simp [Matrix.mulVec, dotProduct, hc']
  have eB : (MvPolynomial (Fin (n + m)) S ⧸ Ideal.span (Set.range (decompRelLeft e₁ e₂))) ≃ₐ[S] B :=
    (lciOneEquiv _).trans ((decompLeftEquiv e₁ e₂).symm.trans e₁)
  have : Algebra.QuasiFinite S
      (MvPolynomial (Fin (n + m)) S ⧸ Ideal.span (Set.range (decompRelLeft e₁ e₂))) :=
    (Algebra.QuasiFinite.iff_of_algEquiv eB).mpr inferInstance
  refine ⟨Matrix.of c, Matrix.of c', hM, hM', ?_⟩
  have := (isUnit_det_of_mulVec_eq _ _ _ _ hM hM').map (lciOneEquiv (decompRelLeft e₁ e₂))
  rwa [lciOneEquiv_mk] at this

end Decomposition

end Stacks.TateMap
