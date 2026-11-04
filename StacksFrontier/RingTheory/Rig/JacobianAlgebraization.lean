module

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria
public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Rig.Algebraization
public import StacksFrontier.RingTheory.Rig.DeformationPrincipal

/-!
# Inputs for the Jacobian criterion for algebraization

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B = A⟨x₁, …, x_r⟩/J` an object of the
category of `I`-adically complete `A`-algebras of finite type modulo `I`, presented so that
there are an element `b`, an integer `m ≤ r` and `f₁, …, f_m ∈ J` with `V(b) ⊆ V(IB)`, with the
Jacobian determinant `Δ = det(∂fⱼ/∂xᵢ)` of the first `m` variables dividing `b`, and with
`bJ ⊆ (f₁, …, f_m) + J²`.

Three independent inputs for the algebraization of such a `B` are collected here: that `B` is
rig-smooth, that the square system `f₁, …, f_r, z·Δ - a` obtained by adjoining a variable
inverting `Δ` has Jacobian determinant `Δ²` and hence a cotangent complex whose `Ext¹` is
annihilated by `a²`, and that in a Noetherian ring the `b`-power torsion is disjoint from a
high power of `(b)`.

## Main definitions

* `Rig.jacobianRelations` — the square system `f₁, …, f_r, z·Δ - a`.
* `Rig.JacobianAlgebra` — the finite type algebra `A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)`.

## Main results

* `Rig.isRigSmooth_of_jacobianChart` — a single Jacobian chart covering the complement of the
  ideal of definition makes `B` rig-smooth over `(A, I)`.
* `Rig.exists_pow_adicIdeal_le_span_of_le_radical` — `V(b) ⊆ V(IB)` gives `I^c B ⊆ bB`.
* `Rig.det_pderiv_jacobianRelations` — the Jacobian determinant of `f₁, …, f_r, z·Δ - a` with
  respect to `x₁, …, x_r, z` is `Δ²`.
* `Rig.sq_smul_ext_one_naiveCotangentComplex_jacobianRelations_eq_zero` — the image of `a²`
  annihilates `Ext¹_C(NL_{C/A}, N)` for `C = A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)`.
* `Rig.exists_disjoint_torsionIdeal_pow` — in a Noetherian ring the `b`-power torsion ideal is
  disjoint from a sufficiently high power of `(b)`.
* `Rig.det_mem_retractionIdeal_of_span` — Cramer's rule: the determinant of a square matrix
  describing a linear map on a generating family lies in the retraction ideal of that map.
* `Rig.det_pderiv_mem_retractionIdeal` — for a presentation by as many relations as variables
  the image of the Jacobian determinant lies in the retraction ideal of the differential.
* `Rig.smoothAwayFrom_of_le_radical_det` — such a presentation is smooth over the complement
  of `V(I)` as soon as `IB` lies in the radical of the Jacobian determinant.
* `Rig.smoothAwayFrom_jacobianAlgebra` and
  `Rig.isRigSmooth_adicCompletionObj_jacobianAlgebra` — for `I = (a)` the algebra
  `A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)` is smooth away from `V(I)` and its `I`-adic
  completion is rig-smooth over `(A, I)`.
* `Rig.exists_pow_smul_ext_one_eq_zero_of_isRigSmooth` and
  `Rig.exists_pow_smul_ext_one_eq_zero_adicCompletionObj_jacobianAlgebra` — rig-smoothness read
  on a given presentation as the annihilation of `Ext¹` by a power of an element of `I`, and
  that annihilation for the completion of the Jacobian algebra.

## Implementation notes

The last relation `z·Δ - a` has a constant term, so the last row of the Jacobian matrix of the
enlarged system vanishes off the diagonal and the determinant is computed by one cofactor
expansion.  The resulting factor `Δ` is the determinant of the renamed Jacobian matrix of
`f₁, …, f_r`.

The disjointness statement is the Artin-Rees lemma applied to the torsion ideal, which in a
Noetherian ring is annihilated by a single power of `b`.

## References

* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GAV](https://stacks.math.columbia.edu/tag/0GAV)
* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

section RigSmooth

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- A single Jacobian chart covering the complement of the ideal of definition makes `B`
rig-smooth: if `V(b) ⊆ V(IB)`, the Jacobian determinant of `f₁, …, f_m ∈ J` taken in `m` of the
variables divides the image of `b`, and `bJ ⊆ (f₁, …, f_m) + J²`, then `B` is rig-smooth over
`(A, I)`. -/
public theorem isRigSmooth_of_jacobianChart (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (m : ℕ) (hm : m ≤ P.variableCount)
    (b : P.completedPolynomialRing) (f : Fin m → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom
        (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
            (f j : P.completedPolynomialRing)) ∣
        P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    IsRigSmooth B := by
  refine (isRigSmooth_iff_hasJacobianCover B P).mpr ⟨1, fun _ ↦ b, ?_, fun _ ↦
    ⟨m, ⟨Fin.castLE hm, Fin.castLE_injective hm⟩, f, ?_, hrelations⟩⟩
  · simpa using hvanish
  · exact hjacobian

/-- If the vanishing locus of `b` in `Spec(B)` is contained in that of the ideal of definition,
then a power of the ideal of definition lies in `(b)`. -/
public theorem exists_pow_adicIdeal_le_span_of_le_radical
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (b : B.carrier)
    (hvanish : B.adicIdeal ≤ (Ideal.span {b}).radical) :
    ∃ c : ℕ, B.adicIdeal ^ c ≤ Ideal.span {b} :=
  Ideal.exists_pow_le_of_le_radical_of_fg hvanish
    ((Ideal.fg_of_isNoetherianRing I).map (algebraMap A B.carrier))

end RigSmooth

section Candidate

variable {A : Type u} [CommRing A] {r : ℕ}

private theorem pderiv_last_rename_castSucc (p : MvPolynomial (Fin r) A) :
    MvPolynomial.pderiv (Fin.last r) (rename Fin.castSucc p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k h => simp [h, Fin.castSucc_ne_last k]

/-- The square system `f₁, …, f_r, z·Δ - a` in the variables `x₁, …, x_r, z`, where
`Δ = det(∂fⱼ/∂xᵢ)` is the Jacobian determinant of `f₁, …, f_r`. -/
public def jacobianRelations (f : Fin r → MvPolynomial (Fin r) A) (a : A) :
    Fin (r + 1) → MvPolynomial (Fin (r + 1)) A :=
  Fin.snoc (fun j ↦ rename Fin.castSucc (f j))
    (X (Fin.last r) *
        rename Fin.castSucc (Matrix.det fun i j : Fin r ↦ MvPolynomial.pderiv i (f j)) -
      C a)

/-- The finite type `A`-algebra `A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)`, in which the Jacobian
determinant of `f₁, …, f_r` divides `a`. -/
public abbrev JacobianAlgebra (f : Fin r → MvPolynomial (Fin r) A) (a : A) : Type u :=
  MvPolynomial (Fin (r + 1)) A ⧸ Ideal.span (Set.range (jacobianRelations f a))

/-- The Jacobian determinant of the square system `f₁, …, f_r, z·Δ - a` with respect to the
variables `x₁, …, x_r, z` is the square of the Jacobian determinant `Δ` of `f₁, …, f_r`. -/
public theorem det_pderiv_jacobianRelations (f : Fin r → MvPolynomial (Fin r) A) (a : A) :
    (Matrix.det fun i j : Fin (r + 1) ↦ MvPolynomial.pderiv i (jacobianRelations f a j)) =
      rename Fin.castSucc (Matrix.det fun i j : Fin r ↦ MvPolynomial.pderiv i (f j)) ^ 2 := by
  classical
  set D : MvPolynomial (Fin r) A := Matrix.det fun i j : Fin r ↦ MvPolynomial.pderiv i (f j)
    with hD
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1)) A) :=
    Matrix.of fun i j ↦ MvPolynomial.pderiv i (jacobianRelations f a j) with hM
  have hrow : ∀ j : Fin r, M (Fin.last r) (Fin.castSucc j) = 0 := by
    intro j
    simp only [hM, Matrix.of_apply, jacobianRelations, Fin.snoc_castSucc]
    exact pderiv_last_rename_castSucc (f j)
  have hlast : M (Fin.last r) (Fin.last r) = rename Fin.castSucc D := by
    simp only [hM, Matrix.of_apply, jacobianRelations, Fin.snoc_last]
    rw [map_sub, pderiv_mul, pderiv_X_self, pderiv_C, pderiv_last_rename_castSucc D]
    simp [hD]
  have hsub : M.submatrix (Fin.last r).succAbove (Fin.last r).succAbove =
      (Matrix.of fun i j : Fin r ↦ MvPolynomial.pderiv i (f j)).map (rename Fin.castSucc) := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_last_apply, hM, Matrix.of_apply,
      Matrix.map_apply, jacobianRelations, Fin.snoc_castSucc]
    rw [MvPolynomial.pderiv_rename (Fin.castSucc_injective r) i (f j)]
  change M.det = _
  rw [Matrix.det_succ_row M (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · rw [hlast, hsub,
      show ((Matrix.of fun i j : Fin r ↦ MvPolynomial.pderiv i (f j)).map
            (rename (R := A) Fin.castSucc)).det = rename Fin.castSucc D from by
        rw [hD]
        exact (RingHom.map_det (MvPolynomial.rename (R := A) Fin.castSucc).toRingHom
          (Matrix.of fun i j : Fin r ↦ MvPolynomial.pderiv i (f j))).symm,
      show ((-1 : MvPolynomial (Fin (r + 1)) A)) ^
          ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 from by rw [← two_mul]; simp [pow_mul]]
    ring
  · intro j _ hj
    obtain ⟨j₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    rw [hrow j₀]
    ring
  · exact fun h ↦ absurd (Finset.mem_univ _) h

/-- In `A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)` the image of `a` is `z·Δ`. -/
private theorem algebraMap_jacobianAlgebra_eq (f : Fin r → MvPolynomial (Fin r) A) (a : A) :
    algebraMap A (JacobianAlgebra f a) a =
      Ideal.Quotient.mk (Ideal.span (Set.range (jacobianRelations f a))) (X (Fin.last r)) *
        Ideal.Quotient.mk (Ideal.span (Set.range (jacobianRelations f a)))
          (rename Fin.castSucc (Matrix.det fun i j : Fin r ↦ MvPolynomial.pderiv i (f j))) := by
  have hrel : Ideal.Quotient.mk (Ideal.span (Set.range (jacobianRelations f a)))
      (jacobianRelations f a (Fin.last r)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨Fin.last r, rfl⟩)
  rw [show jacobianRelations f a (Fin.last r) = X (Fin.last r) *
        rename Fin.castSucc (Matrix.det fun i j : Fin r ↦ MvPolynomial.pderiv i (f j)) - C a from
      by simp [jacobianRelations],
    map_sub, sub_eq_zero, map_mul] at hrel
  exact hrel.symm

/-- In `C = A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)` the image of `a²` annihilates
`Ext¹_C(NL_{C/A}, N)` for every `C`-module `N`: the Jacobian determinant of the square system
is `Δ²`, and `a = z·Δ` in `C`. -/
public theorem sq_smul_ext_one_naiveCotangentComplex_jacobianRelations_eq_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → MvPolynomial (Fin r) A) (a : A)
    (N : ModuleCat.{max u v} (JacobianAlgebra f a))
    (x : DerivedCategory.Ext (Rig.derivedNaiveCotangentComplex.{u, v} A (JacobianAlgebra f a))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (JacobianAlgebra f a)) 0).obj N) 1) :
    algebraMap A (JacobianAlgebra f a) (a ^ 2) • x = 0 := by
  have hcast : (fun i j : Fin (r + 1) ↦
      MvPolynomial.pderiv (Fin.castLE (le_refl (r + 1)) i) (jacobianRelations f a j)) =
      fun i j : Fin (r + 1) ↦ MvPolynomial.pderiv i (jacobianRelations f a j) := by
    funext i j
    congr 1
  have h0 := Rig.jacobianDet_smul_ext_one_naiveCotangentComplex_eq_zero.{u, v}
    A (r + 1) (r + 1) (jacobianRelations f a) (le_refl (r + 1)) N x
  rw [hcast, det_pderiv_jacobianRelations, map_pow] at h0
  rw [map_pow, algebraMap_jacobianAlgebra_eq, mul_pow, mul_smul, h0, smul_zero]

end Candidate

section Torsion

variable {B : Type u} [CommRing B] [IsNoetherianRing B]

/-- In a Noetherian ring a single power of `b` annihilates the whole `b`-power torsion
ideal. -/
public theorem exists_pow_mul_torsionIdeal_eq_zero (b : B) :
    ∃ m : ℕ, ∀ t ∈ torsionIdeal B b, b ^ m * t = 0 := by
  classical
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (torsionIdeal B b))
  choose e he using fun i : Fin n ↦
    (mem_torsionIdeal_iff B b (s i)).mp (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Finset.univ.sup e, fun t ht ↦ ?_⟩
  have hle : torsionIdeal B b ≤
      LinearMap.ker (LinearMap.mulLeft B (b ^ Finset.univ.sup e)) := by
    rw [← hs, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    have hei : e i ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ i)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
    calc b ^ Finset.univ.sup e * s i = b ^ (Finset.univ.sup e - e i) * (b ^ e i * s i) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega
      _ = 0 := by rw [he i, mul_zero]
  exact hle ht

/-- In a Noetherian ring the `b`-power torsion ideal is disjoint from a sufficiently high power
of `(b)`. -/
public theorem exists_disjoint_torsionIdeal_pow (b : B) :
    ∃ d : ℕ, Disjoint (torsionIdeal B b) (Ideal.span {b} ^ d) := by
  obtain ⟨m, hm⟩ := exists_pow_mul_torsionIdeal_eq_zero b
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {b}) (torsionIdeal B b)
  refine ⟨k + m, disjoint_iff.mpr (le_antisymm ?_ bot_le)⟩
  have h1 := hk (k + m) (Nat.le_add_right k m)
  rw [show Ideal.span {b} ^ (k + m) • (⊤ : Submodule B B) = Ideal.span {b} ^ (k + m) from by simp,
    show Ideal.span {b} ^ k • (⊤ : Submodule B B) = Ideal.span {b} ^ k from by simp,
    Nat.add_sub_cancel_left] at h1
  rw [inf_comm, h1]
  refine Submodule.smul_le.mpr fun c hc x hx ↦ ?_
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hc
  obtain ⟨u, rfl⟩ := hc
  simp only [Submodule.mem_bot, smul_eq_mul]
  rw [mul_comm u (b ^ m), mul_assoc, mul_comm u x, ← mul_assoc, hm x hx.2, zero_mul]

end Torsion

section SquarePresentation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B] {N : ℕ}

/-- Cramer's rule for a retraction: if a family `g₁, …, g_n` generates `D` and the linear
map `d : D → Rⁿ` sends `g_j` to the `j`-th column of a square matrix `M`, then `det M` admits a
retraction of `d`: the adjugate of `M` provides one. -/
public theorem det_mem_retractionIdeal_of_span
    {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]
    {n : ℕ} (d : D →ₗ[R] (Fin n → R)) (g : Fin n → D)
    (hspan : Submodule.span R (Set.range g) = ⊤)
    (M : Matrix (Fin n) (Fin n) R) (hd : ∀ j i, d (g j) i = M i j) :
    M.det ∈ retractionIdeal d := by
  classical
  refine ⟨(Pi.basisFun R (Fin n)).constr R (fun i ↦ ∑ j, M.adjugate j i • g j), ?_⟩
  refine LinearMap.ext_on hspan ?_
  rintro x ⟨k, rfl⟩
  have hdg : d (g k) = ∑ i, M i k • (Pi.basisFun R (Fin n)) i := by
    funext i
    rw [hd k i]
    simp [Pi.basisFun_apply, Finset.sum_apply, Pi.single_apply]
  simp only [LinearMap.comp_apply, hdg, map_sum, map_smul,
    Module.Basis.constr_basis, LinearMap.smul_apply, LinearMap.id_apply]
  calc ∑ i, M i k • ∑ j, M.adjugate j i • g j
      = ∑ i, ∑ j, (M.adjugate j i * M i k) • g j := by
        simp only [Finset.smul_sum, smul_smul]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm]
    _ = ∑ j, ∑ i, (M.adjugate j i * M i k) • g j := Finset.sum_comm
    _ = ∑ j, ((M.adjugate * M) j k) • g j :=
        Finset.sum_congr rfl fun j _ ↦ by rw [Matrix.mul_apply, Finset.sum_smul]
    _ = M.det • g k := by
        rw [Matrix.adjugate_mul, Finset.sum_eq_single k]
        · simp
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_univ k) h

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- For a presentation of `B` with as many relations `f₁, …, f_N` as variables, the image in `B`
of the Jacobian determinant `det(∂fⱼ/∂xᵢ)` lies in the retraction ideal of the differential of
the naive cotangent complex. -/
public theorem det_pderiv_mem_retractionIdeal (G : Algebra.Generators A B (Fin N))
    (rel : Fin N → G.Ring) (hrel : Ideal.span (Set.range rel) = G.toExtension.ker) :
    algebraMap G.Ring B (Matrix.det fun i j : Fin N ↦ MvPolynomial.pderiv i (rel j)) ∈
      retractionIdeal (presentationDifferential G) := by
  classical
  have hspan := Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
    (P := G.toExtension) rel hrel
  have hd : ∀ (j i : Fin N),
      presentationDifferential G (Algebra.Extension.Cotangent.mk
          ⟨rel j, hrel.le (Ideal.subset_span ⟨j, rfl⟩)⟩) i =
        algebraMap G.Ring B (MvPolynomial.pderiv i (rel j)) := by
    intro j i
    rw [presentationDifferential_mk]
  have hmain := det_mem_retractionIdeal_of_span (presentationDifferential G)
    (fun j ↦ Algebra.Extension.Cotangent.mk ⟨rel j, hrel.le (Ideal.subset_span ⟨j, rfl⟩)⟩)
    hspan (Matrix.of fun i j ↦ algebraMap G.Ring B (MvPolynomial.pderiv i (rel j)))
    (fun j i ↦ hd j i)
  rwa [show (Matrix.of fun i j : Fin N ↦
        algebraMap G.Ring B (MvPolynomial.pderiv i (rel j))).det =
      algebraMap G.Ring B
        (Matrix.det fun i j : Fin N ↦ MvPolynomial.pderiv i (rel j)) from
    (RingHom.map_det (algebraMap G.Ring B)
      (Matrix.of fun i j : Fin N ↦ MvPolynomial.pderiv i (rel j))).symm] at hmain

/-- A presentation of `B` with as many relations as variables presents `Spec(B) → Spec(A)` as
smooth over `Spec(A) ∖ V(I)` as soon as `IB` is contained in the radical of the image of the
Jacobian determinant of the relations. -/
public theorem smoothAwayFrom_of_le_radical_det {I : Ideal A}
    (G : Algebra.Generators A B (Fin N))
    (rel : Fin N → G.Ring) (hrel : Ideal.span (Set.range rel) = G.toExtension.ker)
    (hrad : I.map (algebraMap A B) ≤
      (Ideal.span {algebraMap G.Ring B
        (Matrix.det fun i j : Fin N ↦ MvPolynomial.pderiv i (rel j))}).radical) :
    SmoothAwayFrom A I B :=
  (smoothAwayFrom_iff_le_radical_retractionIdeal G).mpr (hrad.trans
    (Ideal.radical_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (det_pderiv_mem_retractionIdeal G rel hrel)))))

end SquarePresentation

section JacobianSmooth

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {r : ℕ}

/-- For a principal ideal `I = (a)` the algebra `C = A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)` is
smooth over `Spec(A) ∖ V(I)`: its Jacobian determinant is `Δ²` and `a = z·Δ` in `C`, so `a²`
lies in `(Δ²)`. -/
public theorem smoothAwayFrom_jacobianAlgebra (f : Fin r → MvPolynomial (Fin r) A)
    (a : A) (hI : I = Ideal.span {a}) :
    SmoothAwayFrom A I (JacobianAlgebra f a) := by
  classical
  set rel := jacobianRelations f a with hreldef
  set Isp : Ideal (MvPolynomial (Fin (r + 1)) A) := Ideal.span (Set.range rel) with hIsp
  refine smoothAwayFrom_of_le_radical_det
    (Algebra.Generators.naive (R := A) (I := Isp)) rel
    (Algebra.Generators.ker_naive _ _).symm ?_
  rw [hI, Ideal.map_span, Set.image_singleton]
  refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
  rw [det_pderiv_jacobianRelations f a]
  refine Ideal.mem_radical_iff.mpr ⟨2, ?_⟩
  rw [algebraMap_jacobianAlgebra_eq, mul_pow]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← map_pow (Ideal.Quotient.mk _)]
  exact Ideal.mem_span_singleton_self _

/-- For a principal ideal `I = (a)` the `I`-adic completion of
`A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)` is rig-smooth over `(A, I)`. -/
public theorem isRigSmooth_adicCompletionObj_jacobianAlgebra
    (f : Fin r → MvPolynomial (Fin r) A) (a : A) (hI : I = Ideal.span {a}) :
    IsRigSmooth (adicCompletionObj I (B := JacobianAlgebra f a)) :=
  isRigSmooth_adicCompletionObj_of_smoothAwayFrom I (smoothAwayFrom_jacobianAlgebra f a hI)

end JacobianSmooth

section ExtAnnihilation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- Rig-smoothness of `B` over `(A, I)`, read on a chosen completed polynomial presentation and
at an element `a ∈ I`: some power of the image of `a` annihilates `Ext¹` out of the completed
naive cotangent complex into every `B`-module. -/
public theorem exists_pow_smul_ext_one_eq_zero_of_isRigSmooth
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (hB : IsRigSmooth B) (a : A) (ha : a ∈ I) :
    ∃ c : ℕ, ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) ^ c • ξ = 0 := by
  obtain ⟨c, hc⟩ := (isRigSmooth_iff B P).mp hB
  refine ⟨c, fun N ξ ↦ ?_⟩
  rw [← map_pow]
  exact hc N ξ (a ^ c) (Ideal.pow_mem_pow ha c)

/-- For `I = (a)` and `C = A[x₁, …, x_r, z]/(f₁, …, f_r, z·Δ - a)`, a power of the image of `a`
annihilates `Ext¹` out of the completed naive cotangent complex of `C^∧` on every completed
polynomial presentation of `C^∧`. -/
public theorem exists_pow_smul_ext_one_eq_zero_adicCompletionObj_jacobianAlgebra {r : ℕ}
    (f : Fin r → MvPolynomial (Fin r) A) (a : A) (hI : I = Ideal.span {a})
    (P : CompletedPolynomialPresentation I (adicCompletionObj I (B := JacobianAlgebra f a))) :
    ∃ c : ℕ,
      ∀ (N : ModuleCat.{u} (adicCompletionObj I (B := JacobianAlgebra f a)).carrier)
        (ξ : DerivedCategory.Ext
          (DerivedCategory.Q.obj
            (completedNaiveCotangentComplex
              (adicCompletionObj I (B := JacobianAlgebra f a)) P).cochainComplex)
          ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (adicCompletionObj I (B := JacobianAlgebra f a)).carrier) 0).obj N) 1),
        (algebraMap A (adicCompletionObj I (B := JacobianAlgebra f a)).carrier a) ^ c • ξ = 0 :=
  exists_pow_smul_ext_one_eq_zero_of_isRigSmooth _ P
    (isRigSmooth_adicCompletionObj_jacobianAlgebra f a hI) a
    (by rw [hI]; exact Ideal.mem_span_singleton_self a)

end ExtAnnihilation

end Rig

end
