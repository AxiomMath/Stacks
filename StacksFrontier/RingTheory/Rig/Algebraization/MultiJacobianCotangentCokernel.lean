module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Algebraization.JacobianCriterion
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedPresentation

/-!
# The degree-zero cohomology of a square multi-Jacobian algebra is `I`-power torsion

Let `A` be a Noetherian ring, `I = (a₁, …, a_t)` an ideal, and
`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ - a₁^c, …, z_tΔ - a_t^c, f₁, …, f_r)` the multi-generator
Jacobian algebra of Stacks 0GAV attached to a **square** system `f₁, …, f_r` of polynomials in
`r` variables, with `Δ = det(∂fⱼ/∂xᵢ)_{i, j ≤ r}`.  Then `C` is presented by `t + r` variables
and `t + r` relations, and the Jacobian determinant of the full system is `Δ^{t+1}`
(`Rig.det_pderiv_multiJacobianRelations`).  Cramer's rule therefore annihilates the *cokernel*
of the differential of the naive cotangent complex by `Δ^{t+1}`, and since `a_k^c = z_kΔ` in
`C` a power of `I` annihilates it.

The statement proved here is that annihilation, after base change along any map `C^∧ → B`:

`Rig.pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian` — every element of
`I^{1 + t((t+1)c - 1)}` carries all of `⨁ᵢ B dxᵢ` into the image of
`B ⊗_{C^∧} (J/J²) → ⨁ᵢ B dxᵢ`, that is, it annihilates
`H⁰(NL^∧_{C^∧/A} ⊗_{C^∧} B)`.

That is exactly the hypothesis `hcomparison` of
`Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison`, in the strong form which does not
look at the relation `hv` at all: the whole of `H⁰(NL^∧_{C^∧/A} ⊗_{C^∧} B)` is killed, not
merely the kernel of the comparison to `H⁰(NL^∧_{B/A})`.

## Why the square case is the whole of the comparison for Stacks 0ALS

The last step of the proof of Stacks 0GAW compares `H⁰(NL^∧_{C^∧/A}) ⊗ B[1/b]` with
`H⁰(NL^∧_{B/A}) ⊗ B[1/b]`, both "free `B[1/b]` modules of rank `r - m`".  For the rig-étale
case of Stacks 0ALS the Jacobian chart of `B` is square — `m = r`, by Stacks 0AJU part (6) —
so that rank is `0`: *both* localized modules vanish.  Only the first of the two needs to be
seen to vanish, because the kernel of a map out of a module whose localization is zero is
`b`-power torsion for trivial reasons, and here even more is true: the exponent is produced
over `A` directly, so no localization and no comparison of ranks is needed.  The present file
is that observation, carried out on the nose for the algebra `C` which
`Rig.exists_multiJacobian_surjection_of_jacobianChart_principal` builds.

## Main results

* `Rig.det_smul_mem_range_of_matrix` — Cramer's rule for a cokernel: if `N` elements of the
  source of `d : D →ₗ[R] (Fin N → R)` have images the columns of a square matrix `M`, then
  `det M` carries all of `Fin N → R` into the image of `d`.
* `Rig.pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian` — the annihilation above.

## References

* [Stacks Project, Tag 0GAV](https://stacks.math.columbia.edu/tag/0GAV)
* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

/-! ## Cramer's rule for a cokernel -/

section Cramer

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

/-- **Cramer's rule for a cokernel.**  Let `d : D → ⨁_{i < N} R` be a linear map and let
`u₁, …, u_N` be elements of `D` whose images under `d` are the columns of a square matrix `M`.
Then `det M` carries every tuple into the image of `d`: the adjugate identity
`M · adj(M) = det(M) · 1` writes `det(M) · v` as the combination of the columns with
coefficients `adj(M) · v`, and that combination is `d` of the corresponding combination of the
`uⱼ`. -/
public theorem det_smul_mem_range_of_matrix {N : ℕ} (d : D →ₗ[R] (Fin N → R)) (u : Fin N → D)
    (M : Matrix (Fin N) (Fin N) R) (hM : ∀ j i, d (u j) i = M i j) (v : Fin N → R) :
    M.det • v ∈ LinearMap.range d := by
  classical
  refine ⟨∑ j, M.adjugate.mulVec v j • u j, ?_⟩
  have h1 : d (∑ j, M.adjugate.mulVec v j • u j) = M.mulVec (M.adjugate.mulVec v) := by
    rw [map_sum]
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hM j i, mul_comm]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

end Cramer

/-! ## The differential of `NL^∧_{C^∧/A} ⊗_{C^∧} B` on a relation of `C` -/

section InnerBaseChange

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {D : Type u} [CommRing D] [Algebra A D] [Algebra.FiniteType A D] {n : ℕ}
  (G : Algebra.Generators A D (Fin n)) (B : AdicFiniteTypeAlgebra.{u, u} A I)
  [Algebra (adicCompletionObj I (B := D)).carrier B.carrier]
  [IsScalarTower A (adicCompletionObj I (B := D)).carrier B.carrier]

omit [IsScalarTower A (adicCompletionObj I (B := D)).carrier B.carrier] in
/-- The degree-`0` differential of `NL^∧_{D^∧/A} ⊗_{D^∧} B` of Stacks 0ALM, evaluated on
`1 ⊗ dg` for a relation `g` of the finite type presentation `G` of `D`: the tuple of the images
in `B` of the partial derivatives `∂g/∂xᵢ`.  This is
`Rig.differential_conormalComparison` (Stacks 0GAF) read after base change. -/
public theorem innerBaseChangeDifferential_one_tmul_conormalComparison
    (g : G.toExtension.ker) :
    (presentationCompletion I G).innerBaseChangeDifferential (C := B) (completedComplex I G)
        ((1 : B.carrier) ⊗ₜ[(adicCompletionObj I (B := D)).carrier]
          conormalComparison I G (Algebra.Extension.Cotangent.mk g)) =
      fun i : Fin n ↦ algebraMap (adicCompletionObj I (B := D)).carrier B.carrier
        (algebraMap D (adicCompletionObj I (B := D)).carrier
          (algebraMap G.Ring D (MvPolynomial.pderiv i g.val))) := by
  rw [CompletedPolynomialPresentation.innerBaseChangeDifferential,
    LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply]
  funext i
  rw [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
  refine congrArg _ ?_
  have h3 : (completedComplex I G).differential
      (conormalComparison I G (Algebra.Extension.Cotangent.mk g)) i =
      algebraMap D (adicCompletionObj I (B := D)).carrier
        (presentationDifferential G (Algebra.Extension.Cotangent.mk g) i) :=
    congrFun (differential_conormalComparison I G (Algebra.Extension.Cotangent.mk g)) i
  rw [h3]
  exact congrArg _ (presentationDifferential_mk G g i)

end InnerBaseChange

/-! ## The annihilation -/

section MultiJacobian

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r t : ℕ}

/-- **A power of `I` annihilates `H⁰(NL^∧_{C^∧/A} ⊗_{C^∧} B)` for a square multi-Jacobian
algebra.**  Let `I = (a₁, …, a_t)` be an ideal of a Noetherian ring `A`, let `f₁, …, f_r` be
polynomials in the *same number* `r` of variables, and let
`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ - a₁^c, …, z_tΔ - a_t^c, f₁, …, f_r)` be the multi-generator
Jacobian algebra of Stacks 0GAV, with `Δ = det(∂fⱼ/∂xᵢ)`.  Let `B` be any object of the
category of Stacks 0AL4 over `(A, I)` receiving a map from `C^∧`.  Then every element of
`I^{1 + t((t+1)c - 1)}` carries every tuple `v ∈ ⨁ᵢ B dxᵢ` into the image of the degree-`0`
differential of `NL^∧_{C^∧/A} ⊗_{C^∧} B`.

The presentation of `C` is square: `t + r` variables `z₁, …, z_t, x₁, …, x_r` against `t + r`
relations, and the determinant of its Jacobian is `Δ^{t+1}`
(`Rig.det_pderiv_multiJacobianRelations`).  Cramer's rule
(`Rig.det_smul_mem_range_of_matrix`) therefore puts `Δ^{t+1}` into the annihilator of the
cokernel, and `a_k^c = z_kΔ` in `C` makes `a_k^{(t+1)c}` a multiple of `Δ^{t+1}`; the
pigeonhole bound `Rig.span_range_pow_le_of_forall_pow_mem` turns the `t` separate exponents
into the single one on `I`.

This is the hypothesis `hcomparison` of
`Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison`, in the form which ignores the
relation hypothesis: the whole degree-`0` cohomology is annihilated, not merely the kernel of
the comparison to `H⁰(NL^∧_{B/A})`. -/
public theorem pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian
    (hm : r ≤ r) (f : Fin r → MvPolynomial (Fin r) A) (agen : Fin t → A) (c : ℕ)
    {I : Ideal A} (hI : I = Ideal.span (Set.range agen))
    (B : AdicFiniteTypeAlgebra.{u, u} A I)
    [Algebra (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier B.carrier]
    [IsScalarTower A (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier
      B.carrier]
    (y : A) (hy : y ∈ I ^ (1 + t * ((t + 1) * c - 1)))
    (v : Fin (multiJacobianCompletedPresentation I hm f agen c).variableCount → B.carrier) :
    algebraMap A B.carrier y • v ∈ LinearMap.range
      ((multiJacobianCompletedPresentation I hm f agen c).innerBaseChangeDifferential
        (C := B)
        (completedNaiveCotangentComplex
          (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c))
          (multiJacobianCompletedPresentation I hm f agen c))) := by
  classical
  have hsq : t + r ≤ t + r := le_rfl
  have hcast : ∀ i : Fin (t + r), Fin.castLE hsq i = i := fun i ↦ Fin.ext rfl
  -- the relations of `C`, and the fact that they lie in the kernel of the presentation
  have hkerG : Ideal.span (Set.range (multiJacobianRelations hm f agen c)) =
      (multiJacobianGenerators hm f agen c).toExtension.ker :=
    (Algebra.Generators.ker_naive _ _).symm
  have hmemker : ∀ j, multiJacobianRelations hm f agen c j ∈
      (multiJacobianGenerators hm f agen c).toExtension.ker :=
    fun j ↦ hkerG.le (Ideal.subset_span ⟨j, rfl⟩)
  -- the ring map `A[z, x] → C → C^∧ → B`
  set ρ : MvPolynomial (Fin (t + r)) A →+* B.carrier :=
    ((algebraMap (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier
        B.carrier).comp
      ((algebraMap (MultiJacobianAlgebra hm f agen c)
          (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier).comp
        (algebraMap (MvPolynomial (Fin (t + r)) A)
          (MultiJacobianAlgebra hm f agen c)))) with hρdef
  have hρapply : ∀ x : MvPolynomial (Fin (t + r)) A,
      ρ x = algebraMap (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier
        B.carrier
        (algebraMap (MultiJacobianAlgebra hm f agen c)
          (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier
          (algebraMap (MvPolynomial (Fin (t + r)) A)
            (MultiJacobianAlgebra hm f agen c) x)) := fun x ↦ rfl
  -- `ρ` restricted to constants is the structure map of `B`
  have hρC : ∀ a : A, ρ (MvPolynomial.C a) = algebraMap A B.carrier a := by
    intro a
    rw [hρapply, show (MvPolynomial.C a : MvPolynomial (Fin (t + r)) A) =
        algebraMap A (MvPolynomial (Fin (t + r)) A) a from
      (MvPolynomial.algebraMap_eq (R := A) (σ := Fin (t + r)) ▸ rfl),
      ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin (t + r)) A)
        (MultiJacobianAlgebra hm f agen c) a,
      ← IsScalarTower.algebraMap_apply A (MultiJacobianAlgebra hm f agen c)
        (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier a,
      ← IsScalarTower.algebraMap_apply A
        (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c)).carrier B.carrier a]
  -- `ρ` kills the relations
  have hρrel : ∀ j, ρ (multiJacobianRelations hm f agen c j) = 0 := by
    intro j
    rw [hρapply, show algebraMap (MvPolynomial (Fin (t + r)) A)
        (MultiJacobianAlgebra hm f agen c) (multiJacobianRelations hm f agen c j) = 0 from
      hmemker j, map_zero, map_zero]
  -- the matrix of the full Jacobian, read in `B`
  set M : Matrix (Fin (t + r)) (Fin (t + r)) B.carrier :=
    fun i j ↦ ρ (MvPolynomial.pderiv i (multiJacobianRelations hm f agen c j)) with hMdef
  have hMdet : M.det = ρ (rename (Fin.natAdd t) (jacobian hm f).det) ^ (t + 1) := by
    have h1 : M.det = ρ (Matrix.det fun i j : Fin (t + r) ↦
        MvPolynomial.pderiv i (multiJacobianRelations hm f agen c j)) :=
      (RingHom.map_det ρ _).symm
    have h2 : (Matrix.det fun i j : Fin (t + r) ↦
          MvPolynomial.pderiv i (multiJacobianRelations hm f agen c j)) =
        rename (Fin.natAdd t) (jacobian hm f).det ^ (t + 1) := by
      rw [show (fun i j : Fin (t + r) ↦
            MvPolynomial.pderiv i (multiJacobianRelations hm f agen c j)) =
          (fun i j : Fin (t + r) ↦ MvPolynomial.pderiv (Fin.castLE hsq i)
            (multiJacobianRelations hm f agen c j)) from by
        funext i j
        rw [hcast i]]
      exact det_pderiv_multiJacobianRelations hm hsq f agen c
    rw [h1, h2, map_pow]
  -- the columns of `M` are the images of the classes of the relations
  have hcol : ∀ j i : Fin (t + r),
      (multiJacobianCompletedPresentation I hm f agen c).innerBaseChangeDifferential
          (C := B)
          (completedNaiveCotangentComplex
            (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c))
            (multiJacobianCompletedPresentation I hm f agen c))
          ((1 : B.carrier) ⊗ₜ[(adicCompletionObj I
              (B := MultiJacobianAlgebra hm f agen c)).carrier]
            conormalComparison I (multiJacobianGenerators hm f agen c)
              (Algebra.Extension.Cotangent.mk
                ⟨multiJacobianRelations hm f agen c j, hmemker j⟩)) i = M i j := by
    intro j i
    exact (congrFun (innerBaseChangeDifferential_one_tmul_conormalComparison I
      (multiJacobianGenerators hm f agen c) B
      ⟨multiJacobianRelations hm f agen c j, hmemker j⟩) i).trans (hρapply _).symm
  -- Cramer's rule: `det M` carries everything into the image
  have hcramer : ∀ w : Fin (t + r) → B.carrier, M.det • w ∈ LinearMap.range
      ((multiJacobianCompletedPresentation I hm f agen c).innerBaseChangeDifferential
        (C := B)
        (completedNaiveCotangentComplex
          (adicCompletionObj I (B := MultiJacobianAlgebra hm f agen c))
          (multiJacobianCompletedPresentation I hm f agen c))) :=
    det_smul_mem_range_of_matrix _
      (fun j ↦ (1 : B.carrier) ⊗ₜ[(adicCompletionObj I
          (B := MultiJacobianAlgebra hm f agen c)).carrier]
        conormalComparison I (multiJacobianGenerators hm f agen c)
          (Algebra.Extension.Cotangent.mk
            ⟨multiJacobianRelations hm f agen c j, hmemker j⟩)) M hcol
  -- `a_k^c = z_k Δ` in `C`, hence in `B`
  have hzk : ∀ k : Fin t, algebraMap A B.carrier (agen k ^ c) =
      ρ (X (Fin.castAdd r k)) * ρ (rename (Fin.natAdd t) (jacobian hm f).det) := by
    intro k
    have h0 := hρrel (Fin.castAdd r k)
    rw [multiJacobianRelations_castAdd, map_sub, map_mul, hρC, sub_eq_zero] at h0
    exact h0.symm
  -- each `a_k^{(t+1)c}` is a multiple of `det M`, read in `A` itself
  have hpow : ∀ k : Fin t, agen k ^ ((t + 1) * c) ∈
      Ideal.comap (algebraMap A B.carrier) (Ideal.span {M.det}) := by
    intro k
    rw [Ideal.mem_comap, show agen k ^ ((t + 1) * c) = (agen k ^ c) ^ (t + 1) from by
      rw [mul_comm, pow_mul], map_pow, hzk k, mul_pow, hMdet]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  -- the pigeonhole bound turns the `t` exponents into one on `I`
  have hy' : y ∈ Ideal.span (Set.range agen) ^ (1 + t * ((t + 1) * c - 1)) := by
    rwa [← hI]
  have hymem : algebraMap A B.carrier y ∈ Ideal.span {M.det} :=
    Ideal.mem_comap.mp
      (span_range_pow_le_of_forall_pow_mem agen ((t + 1) * c) _ hpow hy')
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hymem
  rw [← hw, mul_smul]
  exact Submodule.smul_mem _ w (hcramer v)

end MultiJacobian

end Rig

end
