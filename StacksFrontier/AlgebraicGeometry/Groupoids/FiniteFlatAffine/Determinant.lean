module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# Adjugates and norms of finite projective modules

An endomorphism `f` of a finite projective module has a scalar determinant
`ProjectiveDeterminant.det f`, and choosing a split `s ∘ₗ i = id` of the module off a finite
free module turns that determinant into the ordinary determinant of a matrix
(`ProjectiveDeterminant.det_stabilize`). Two consequences of that reduction are collected here:
the determinant is realized by an adjugate, and a ring map killing `r` sends the determinant of
`id + r • φ` to `1`.

Applied to the multiplication endomorphism of a finite projective algebra, the determinant is
the projective norm `Algebra.projectiveNorm`, and the adjugate shows that a retraction of the
algebra onto its base sends an element to a divisor of its norm.

## Main results

* `ProjectiveDeterminant.exists_comp_eq_det_smul_id`: existence of an adjugate.
* `ProjectiveDeterminant.map_det_id_add_smul_eq_one`: the determinant of `id + r • φ` becomes
  `1` under a ring map killing `r`.
* `ProjectiveDeterminant.map_dvd_det_lmul`: a retraction sends an element to a divisor of its
  norm.

## References

* [Stacks Project, Tag 0FJF](https://stacks.math.columbia.edu/tag/0FJF)
-/

@[expose] public section

namespace ProjectiveDeterminant

universe u v

/-- An endomorphism of a finite projective module has an adjugate: a second endomorphism whose
composite with it is multiplication by the determinant. -/
theorem exists_comp_eq_det_smul_id {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] M) :
    ∃ g : M →ₗ[R] M, f ∘ₗ g = det f • LinearMap.id := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    have : Subsingleton M := Module.subsingleton R M
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨n, q, i, _, _, hqi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  set F := LinearMap.id + i ∘ₗ ((f - LinearMap.id) ∘ₗ q) with hF
  set A := LinearMap.toMatrix' F with hA
  set adj := Matrix.toLin' A.adjugate with hadj
  have hFadj : F ∘ₗ adj = A.det • LinearMap.id := by
    apply LinearMap.toMatrix'.injective
    simpa [hA, hadj, LinearMap.toMatrix'_comp] using Matrix.mul_adjugate A
  have hqF : q ∘ₗ F = f ∘ₗ q := by
    rw [hF, LinearMap.comp_add, LinearMap.comp_id, ← LinearMap.comp_assoc, hqi,
      LinearMap.id_comp, LinearMap.sub_comp, LinearMap.id_comp]
    abel
  have hdet : A.det = det f := by
    rw [hA, hF, LinearMap.det_toMatrix']
    exact (det_stabilize q i hqi f).symm
  refine ⟨q ∘ₗ (adj ∘ₗ i), ?_⟩
  ext x
  show f (q (adj (i x))) = det f • x
  calc
    _ = q (F (adj (i x))) := LinearMap.congr_fun hqF.symm _
    _ = q (A.det • i x) := congrArg q (LinearMap.congr_fun hFadj (i x))
    _ = _ := by
      rw [map_smul, hdet]
      exact congrArg (det f • ·) (LinearMap.congr_fun hqi x)

/-- A ring map killing `r` sends the determinant of `id + r • φ` to `1`. -/
theorem map_det_id_add_smul_eq_one {R : Type u} [CommRing R] {T : Type v} [CommRing T]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (h : R →+* T) (r : R) (hr : h r = 0) (φ : M →ₗ[R] M) :
    h (det (LinearMap.id + r • φ)) = 1 := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    rw [Subsingleton.elim (det _) 1, map_one]
  obtain ⟨n, q, i, _, _, hqi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  rw [det_stabilize q i hqi]
  have heq : LinearMap.id + i ∘ₗ ((LinearMap.id + r • φ - LinearMap.id) ∘ₗ q) =
      LinearMap.id + r • (i ∘ₗ (φ ∘ₗ q)) := by
    simp only [add_sub_cancel_left, LinearMap.smul_comp, LinearMap.comp_smul]
  rw [heq, ← LinearMap.det_toMatrix', h.map_det]
  have hone : h.mapMatrix (LinearMap.toMatrix' (LinearMap.id + r • (i ∘ₗ (φ ∘ₗ q)))) = 1 := by
    ext j k
    simp [RingHom.mapMatrix_apply, hr, LinearMap.toMatrix'_apply, Matrix.one_apply]
  rw [hone, Matrix.det_one]

/-- A retraction of a finite projective algebra onto its base sends each element to a divisor
of its norm. -/
theorem map_dvd_det_lmul {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] (e : B →ₐ[R] R) (b : B) :
    e b ∣ det (Algebra.lmul R B b) := by
  obtain ⟨g, hg⟩ := exists_comp_eq_det_smul_id (Algebra.lmul R B b)
  exact ⟨e (g 1), by simpa using (congrArg (fun k : B →ₗ[R] B => e (k 1)) hg).symm⟩

end ProjectiveDeterminant

end
