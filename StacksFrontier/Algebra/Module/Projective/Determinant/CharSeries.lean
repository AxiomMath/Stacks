module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Algebra.Module.Projective.Determinant.Endomorphism

/-!
# The characteristic series `det(1 - φ T ^ d)` of an endomorphism of a finite projective module

Let `Λ` be a commutative ring and `φ` an endomorphism of a finite projective `Λ`-module `M`. The
characteristic series `det(1 - φ T ^ d) ∈ Λ⟦T⟧` is the projective determinant
(`ProjectiveDeterminant.det`) of `1 - T ^ d • φ` after base change to `Λ⟦T⟧`. Unlike Mathlib's
`LinearMap.det`, which takes the junk value `1` on a module without a finite basis, this is the
true determinant on every finite projective module. On a finite free module it is
`LinearMap.det`.

## Main definitions

* `ProjectiveDeterminant.charSeries`: `det(1 - φ T ^ d)`.

## Main results

* `ProjectiveDeterminant.charSeries_retract`: the characteristic series is unchanged when `M` is
  replaced by a module `N` of which it is a retract `p ∘ i = id` and `φ` by `i ∘ φ ∘ p`.
* `ProjectiveDeterminant.charSeries_eq_det_matrix`: in a finite basis it is the determinant of
  the matrix `1 - T ^ d • A`.
* `ProjectiveDeterminant.charSeries_comp_comm`: `det(1 - (a ∘ b) T ^ d) = det(1 - (b ∘ a) T ^ d)`.
* `ProjectiveDeterminant.charSeries_of_exact`: multiplicativity along an endomorphism of a short
  exact sequence.
* `ProjectiveDeterminant.constantCoeff_charSeries`, `ProjectiveDeterminant.isUnit_charSeries`:
  for `d ≠ 0` it has constant coefficient `1`, so it is a unit of `Λ⟦T⟧`.
* `ProjectiveDeterminant.charSeries_baseChange`: compatibility with base change of rings.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open PowerSeries

namespace ProjectiveDeterminant

universe u v w x

variable {Λ : Type u} [CommRing Λ]
variable {M : Type v} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M]
variable {N : Type w} [AddCommGroup N] [Module Λ N] [Module.Finite Λ N] [Module.Projective Λ N]

/-- The characteristic series `det(1 - φ T ^ d) ∈ Λ⟦T⟧` of an endomorphism `φ` of a finite
projective `Λ`-module: the projective determinant of `1 - T ^ d • φ` over `Λ⟦T⟧`. -/
public def charSeries (φ : M →ₗ[Λ] M) (d : ℕ) : PowerSeries Λ :=
  det (1 - (X ^ d : PowerSeries Λ) • φ.baseChange (PowerSeries Λ))

/-- **Switching the factors of a composite.** For maps `a : M → N` and `b : N → M` between
finite projective modules, `det(1 - (b ∘ a) T ^ d) = det(1 - (a ∘ b) T ^ d)`. -/
public theorem charSeries_comp_comm (a : M →ₗ[Λ] N) (b : N →ₗ[Λ] M) (d : ℕ) :
    charSeries (b.comp a) d = charSeries (a.comp b) d := by
  have h := det_one_add_comp_comm (R := PowerSeries Λ)
    (-((X ^ d : PowerSeries Λ) • b.baseChange (PowerSeries Λ))) (a.baseChange (PowerSeries Λ))
  have h1 : LinearMap.id + (-((X ^ d : PowerSeries Λ) • b.baseChange (PowerSeries Λ))).comp
      (a.baseChange (PowerSeries Λ)) =
      1 - (X ^ d : PowerSeries Λ) • (b.comp a).baseChange (PowerSeries Λ) := by
    rw [LinearMap.baseChange_comp]
    ext x
    simp [sub_eq_add_neg]
  have h2 : LinearMap.id + (a.baseChange (PowerSeries Λ)).comp
      (-((X ^ d : PowerSeries Λ) • b.baseChange (PowerSeries Λ))) =
      1 - (X ^ d : PowerSeries Λ) • (a.comp b).baseChange (PowerSeries Λ) := by
    rw [LinearMap.baseChange_comp]
    ext x
    simp [sub_eq_add_neg]
  rwa [h1, h2] at h

/-- **Passing to a retract.** If `p ∘ i = id` then `det(1 - φ T ^ d)` on `M` is
`det(1 - (i ∘ φ ∘ p) T ^ d)` on `N`. -/
public theorem charSeries_retract (i : M →ₗ[Λ] N) (p : N →ₗ[Λ] M)
    (h : p.comp i = LinearMap.id) (φ : M →ₗ[Λ] M) (d : ℕ) :
    charSeries φ d = charSeries (i.comp (φ.comp p)) d := by
  have := charSeries_comp_comm i (φ.comp p) d
  rwa [LinearMap.comp_assoc, h, LinearMap.comp_id] at this

/-- In a basis of the base change, `1 - T ^ d • φ` has matrix `1 - T ^ d • A`. -/
private theorem toMatrix_one_sub_smul_baseChange {P ι : Type*} [AddCommGroup P] [Module Λ P]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι Λ P) (φ : P →ₗ[Λ] P) (d : ℕ) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis (PowerSeries Λ) b)
      (Algebra.TensorProduct.basis (PowerSeries Λ) b)
      (1 - (X ^ d : PowerSeries Λ) • φ.baseChange (PowerSeries Λ)) =
      1 - (X ^ d : PowerSeries Λ) • (LinearMap.toMatrix b b φ).map (C (R := Λ)) := by
  have hb := LinearMap.toMatrix_baseChange (PowerSeries Λ) φ b b
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, LinearMap.sub_apply, map_sub, Finsupp.sub_apply,
    Module.End.one_apply, LinearMap.smul_apply, map_smul, Finsupp.smul_apply,
    ← LinearMap.toMatrix_apply, hb]
  simp [Matrix.one_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm,
    Matrix.map_apply]

/-- In a finite basis, `det(1 - φ T ^ d)` is the determinant of the matrix `1 - T ^ d • A` over
`Λ⟦T⟧`, where `A` is the matrix of `φ`. -/
public theorem charSeries_eq_det_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Λ M) (φ : M →ₗ[Λ] M) (d : ℕ) :
    charSeries φ d =
      (1 - (X ^ d : PowerSeries Λ) • (LinearMap.toMatrix b b φ).map (C (R := Λ))).det := by
  nontriviality Λ
  classical
  let b' := Algebra.TensorProduct.basis (PowerSeries Λ) b
  let e := b'.reindex (Fintype.equivFin ι)
  rw [charSeries, det_eq_linearMap_det_of_basis e, ← LinearMap.det_toMatrix b']
  congr 1
  exact toMatrix_one_sub_smul_baseChange b φ d

/-- On a finite free module `det(1 - φ T ^ d)` is Mathlib's `LinearMap.det` of
`1 - T ^ d • φ`. -/
public theorem charSeries_eq_linearMap_det [Module.Free Λ M] (φ : M →ₗ[Λ] M) (d : ℕ) :
    charSeries φ d =
      LinearMap.det (1 - (X ^ d : PowerSeries Λ) • φ.baseChange (PowerSeries Λ)) := by
  classical
  let b := Module.Free.chooseBasis Λ M
  rw [charSeries_eq_det_matrix b, ← LinearMap.det_toMatrix (Algebra.TensorProduct.basis
    (PowerSeries Λ) b)]
  congr 1
  exact (toMatrix_one_sub_smul_baseChange b φ d).symm

/-- A finite projective module is a retract of a finite free module `Fin n → Λ`. -/
public theorem exists_retract_fin (Λ : Type u) [CommRing Λ] (M : Type v) [AddCommGroup M]
    [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M] :
    ∃ (n : ℕ) (i : M →ₗ[Λ] (Fin n → Λ)) (p : (Fin n → Λ) →ₗ[Λ] M),
      p.comp i = LinearMap.id := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  exact ⟨n, i, p, hpi⟩

/-- `det(1 - φ T ^ d)` is the determinant of a matrix `1 - T ^ d • A` over `Λ⟦T⟧`. -/
public theorem exists_charSeries_eq_det_matrix (φ : M →ₗ[Λ] M) (d : ℕ) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) Λ),
      charSeries φ d = (1 - (X ^ d : PowerSeries Λ) • A.map (C (R := Λ))).det := by
  obtain ⟨n, i, p, h⟩ := exists_retract_fin Λ M
  refine ⟨n, LinearMap.toMatrix (Pi.basisFun Λ (Fin n)) (Pi.basisFun Λ (Fin n))
    (i.comp (φ.comp p)), ?_⟩
  rw [charSeries_retract i p h φ d, charSeries_eq_det_matrix (Pi.basisFun Λ (Fin n))]

/-- A ring homomorphism out of `Λ⟦T⟧` killing `T ^ d` sends `det(1 - φ T ^ d)` to `1`. -/
public theorem map_charSeries_eq_one {S : Type*} [CommRing S] (g : PowerSeries Λ →+* S)
    (φ : M →ₗ[Λ] M) (d : ℕ) (hg : g ((X : PowerSeries Λ) ^ d) = 0) :
    g (charSeries φ d) = 1 := by
  obtain ⟨n, A, hA⟩ := exists_charSeries_eq_det_matrix φ d
  rw [hA, g.map_det]
  have : g.mapMatrix (1 - (X ^ d : PowerSeries Λ) • A.map (C (R := Λ))) = 1 := by
    ext i j
    simp [Matrix.one_apply, hg]
  rw [this, Matrix.det_one]

/-- For `d ≠ 0`, `det(1 - φ T ^ d)` has constant coefficient `1`. -/
public theorem constantCoeff_charSeries (φ : M →ₗ[Λ] M) {d : ℕ} (hd : d ≠ 0) :
    constantCoeff (charSeries φ d) = 1 :=
  map_charSeries_eq_one _ φ d (by simp [hd])

/-- `det(1 - φ T ^ d)` is congruent to `1` modulo `T ^ d`. -/
public theorem X_pow_dvd_charSeries_sub_one (φ : M →ₗ[Λ] M) (d : ℕ) :
    (X : PowerSeries Λ) ^ d ∣ charSeries φ d - 1 := by
  have h := map_charSeries_eq_one
    (Ideal.Quotient.mk (Ideal.span {(X : PowerSeries Λ) ^ d})) φ d
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, h, map_one,
    sub_self]

/-- For `d ≠ 0`, `det(1 - φ T ^ d)` is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_charSeries (φ : M →ₗ[Λ] M) {d : ℕ} (hd : d ≠ 0) :
    IsUnit (charSeries φ d) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_charSeries φ hd]
  exact isUnit_one

/-- The characteristic series of the zero endomorphism is `1`. -/
public theorem charSeries_zero (d : ℕ) : charSeries (0 : M →ₗ[Λ] M) d = 1 := by
  rw [charSeries, LinearMap.baseChange_zero, smul_zero, sub_zero]
  exact det_linearMap_id

/-- The characteristic series is invariant under conjugation by a linear equivalence. -/
public theorem charSeries_conj (e : M ≃ₗ[Λ] N) (φ : M →ₗ[Λ] M) (d : ℕ) :
    charSeries (e.conj φ) d = charSeries φ d := by
  have h := charSeries_comp_comm (φ.comp e.symm.toLinearMap) e.toLinearMap d
  have h1 : (e.toLinearMap).comp (φ.comp e.symm.toLinearMap) = e.conj φ := by
    ext x
    simp [LinearEquiv.conj_apply]
  have h2 : (φ.comp e.symm.toLinearMap).comp e.toLinearMap = φ := by
    ext x
    simp
  rwa [h1, h2] at h

/-- **Base change of rings.** For a `Λ`-algebra `Λ'`, the characteristic series of the base
change of `φ` is the image of the characteristic series of `φ` under `Λ⟦T⟧ → Λ'⟦T⟧`. -/
public theorem charSeries_baseChange (Λ' : Type x) [CommRing Λ'] [Algebra Λ Λ']
    (φ : M →ₗ[Λ] M) (d : ℕ) :
    charSeries (φ.baseChange Λ') d = PowerSeries.map (algebraMap Λ Λ') (charSeries φ d) := by
  classical
  obtain ⟨n, i, p, h⟩ := exists_retract_fin Λ M
  have h' : (p.baseChange Λ').comp (i.baseChange Λ') = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_id]
  let b := Pi.basisFun Λ (Fin n)
  let b' := Algebra.TensorProduct.basis Λ' b
  rw [charSeries_retract i p h φ d, charSeries_retract _ _ h' (φ.baseChange Λ') d,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, charSeries_eq_det_matrix b',
    charSeries_eq_det_matrix b, LinearMap.toMatrix_baseChange, RingHom.map_det]
  congr 1
  refine Matrix.ext fun j k => ?_
  by_cases hjk : j = k <;>
    simp [Matrix.map_apply, RingHom.mapMatrix_apply, hjk]

/-- The characteristic series of an endomorphism of the zero module is `1`. -/
public theorem charSeries_eq_one_of_subsingleton [Subsingleton M] (φ : M →ₗ[Λ] M) (d : ℕ) :
    charSeries φ d = 1 := by
  rw [show φ = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, charSeries_zero]

variable {A : Type v} [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] [Module.Projective Λ A]
variable {E : Type w} [AddCommGroup E] [Module Λ E] [Module.Finite Λ E] [Module.Projective Λ E]
variable {B : Type x} [AddCommGroup B] [Module Λ B] [Module.Finite Λ B] [Module.Projective Λ B]

/-- `1 - T ^ d • g` intertwines `u` with `1 - T ^ d • f` over `Λ⟦T⟧` when `g` intertwines them. -/
private theorem one_sub_smul_baseChange_comp {P Q : Type*} [AddCommGroup P] [Module Λ P]
    [AddCommGroup Q] [Module Λ Q] (u : P →ₗ[Λ] Q) (f : P →ₗ[Λ] P) (g : Q →ₗ[Λ] Q)
    (h : g.comp u = u.comp f) (d : ℕ) :
    (1 - (X ^ d : PowerSeries Λ) • g.baseChange (PowerSeries Λ)).comp (u.baseChange _) =
      (u.baseChange (PowerSeries Λ)).comp
        (1 - (X ^ d : PowerSeries Λ) • f.baseChange (PowerSeries Λ)) := by
  refine LinearMap.ext fun y => ?_
  have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange (PowerSeries Λ)) h) y
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply, map_sub, map_smul, h]

/-- **Multiplicativity along short exact sequences.** For an endomorphism `(α, ε, β)` of a short
exact sequence `0 → A → E → B → 0` of finite projective modules,
`det(1 - ε T ^ d) = det(1 - α T ^ d) * det(1 - β T ^ d)`. -/
public theorem charSeries_of_exact {i : A →ₗ[Λ] E} {q : E →ₗ[Λ] B} (hi : Function.Injective i)
    (hex : Function.Exact i q) (hq : Function.Surjective q)
    (α : A →ₗ[Λ] A) (ε : E →ₗ[Λ] E) (β : B →ₗ[Λ] B)
    (hα : ε.comp i = i.comp α) (hβ : q.comp ε = β.comp q) (d : ℕ) :
    charSeries ε d = charSeries α d * charSeries β d := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  have hqs : ∀ z, q (s z) = z := fun z => LinearMap.congr_fun hs z
  have hr : ∀ y : E, ∃ a : A, i a = y - s (q y) := fun y => (hex _).1 (by simp [hqs])
  choose rf hrf using hr
  let r : E →ₗ[Λ] A :=
    { toFun := rf
      map_add' := fun y y' => hi (by simp [hrf]; abel)
      map_smul' := fun c y => hi (by simp [hrf, smul_sub]) }
  have hri : r.comp i = LinearMap.id := by
    ext a
    apply hi
    change i (rf (i a)) = i a
    rw [hrf]
    simp [(hex (i a)).2 ⟨a, rfl⟩]
  have hi' : Function.Injective (i.baseChange (PowerSeries Λ)) := by
    intro y y' hyy
    have := congrArg (r.baseChange (PowerSeries Λ)) hyy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hri,
      LinearMap.baseChange_id] at this
  have hex' : Function.Exact (i.baseChange (PowerSeries Λ)) (q.baseChange (PowerSeries Λ)) := by
    rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    exact lTensor_exact (PowerSeries Λ) hex hq
  have hq' : Function.Surjective (q.baseChange (PowerSeries Λ)) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective (PowerSeries Λ) hq
  refine det_of_exact hi' hex' hq' _ _ _ ?_ ?_
  · exact one_sub_smul_baseChange_comp i α ε hα d
  · exact (one_sub_smul_baseChange_comp q ε β hβ.symm d).symm

end ProjectiveDeterminant
