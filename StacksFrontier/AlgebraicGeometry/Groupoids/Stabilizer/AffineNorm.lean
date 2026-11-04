module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantNorm
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineBasis

/-!
# The determinant trick for an affine groupoid scheme

Let `G` be a groupoid scheme whose object scheme is affine and whose source map is finite
locally free. Then the arrow ring is a finite projective module over the object ring along
the source map, and the norm — the determinant of multiplication — of a function pulled
back along the target map is an invariant function.

## Main results

* `AlgebraicGeometry.norm_targetMap_mem_invariantRing`: the arrow ring is finite projective
  over the object ring along the source map, and the norm, along the source map, of the
  pullback along the target map of any global function lies in
  `AlgebraicGeometry.invariantRing`.

## References

* [Stacks Project, Tag 03BH](https://stacks.math.columbia.edu/tag/03BH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms

/-- The arrow scheme of a groupoid scheme with affine objects and finite locally free source
is affine. -/
lemma arrows_isAffine {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsFiniteLocallyFree G.source.left] :
    IsAffine G.arrows.left := by
  let : IsAffineHom G.source.left := inferInstance
  exact isAffine_of_isAffineHom G.source.left

/-- The determinant of an endomorphism of a finite projective module, computed after
stabilizing along a split surjection from a finite free module. -/
private lemma det_stabilize {R M F : Type*}
    [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
    (s : F →ₗ[R] M) (i : M →ₗ[R] F) (hi : s.comp i = LinearMap.id)
    (f : M →ₗ[R] M) :
    ProjectiveDeterminant.det f =
      LinearMap.det (LinearMap.id + i.comp ((f - LinearMap.id).comp s)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rw [← ProjectiveDeterminant.det_eq_linearMap_det_of_basis (Module.finBasis R F),
    ProjectiveDeterminant.det_one_add_comp_comm]
  congr 1
  rw [LinearMap.comp_assoc, hi, LinearMap.comp_id]
  abel

/-- A finite projective module is a retract of a finite free module `Fin n → R`. -/
private lemma exists_split_fin (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (s : (Fin n → R) →ₗ[R] M) (i : M →ₗ[R] (Fin n → R)),
      s.comp i = LinearMap.id := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  obtain ⟨n, _, s, _, hs, _⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective s hs).mp inferInstance
  exact ⟨n, s, i, hi⟩

/-- The determinant of an endomorphism of a finite projective module commutes with base
change along any algebra map. -/
private lemma det_baseChange_of_projective {R M A : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    [CommRing A] [Algebra R A] (f : M →ₗ[R] M) :
    algebraMap R A (ProjectiveDeterminant.det f) =
      ProjectiveDeterminant.det (f.baseChange A) := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have : Nontrivial R := (algebraMap R A).domain_nontrivial
  obtain ⟨n, s, i, hi⟩ := exists_split_fin R M
  let F := Fin n → R
  let : Module.Free A (A ⊗[R] F) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis A (Module.finBasis R F))
  have hiA : (s.baseChange A).comp (i.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hi, LinearMap.baseChange_id]
  rw [det_stabilize s i hi f,
    det_stabilize (s.baseChange A) (i.baseChange A) hiA (f.baseChange A),
    ← LinearMap.det_baseChange]
  congr 1
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_id,
    LinearMap.baseChange_comp, LinearMap.baseChange_sub]

/-- The determinant of an endomorphism of a finite projective module is invariant under
conjugation by a linear equivalence. -/
private lemma det_conj_of_projective {R M N : Type*}
    [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) :
    ProjectiveDeterminant.det
        (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      ProjectiveDeterminant.det f := by
  classical
  obtain ⟨n, s, i, hi⟩ := exists_split_fin R M
  let sN := e.toLinearMap.comp s
  let iN := i.comp e.symm.toLinearMap
  have hiN : sN.comp iN = LinearMap.id := by
    ext x
    simp [sN, iN, ← LinearMap.comp_apply, hi]
  rw [det_stabilize sN iN hiN, det_stabilize s i hi]
  congr 1
  ext x
  simp [sN, iN, LinearMap.comp_apply]

/-- Alias of `AlgebraicGeometry.GroupoidScheme.finite_projective_appTop_of_isFiniteLocallyFree`. -/
private alias finite_projective_of_finiteLocallyFree :=
  GroupoidScheme.finite_projective_appTop_of_isFiniteLocallyFree

/-- Alias of `AlgebraicGeometry.GroupoidScheme.composables_isPushout`. -/
private alias composable_isPushout :=
  GroupoidScheme.composables_isPushout

/-- Alias of `AlgebraicGeometry.GroupoidScheme.composition_source_isPushout`. -/
private alias composition_source_isPushout :=
  GroupoidScheme.composition_source_isPushout

/-- The norm of a finite projective algebra commutes with base change along a pushout of
commutative rings. -/
private lemma norm_baseChange_of_projective {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra A C] [Algebra B C] [Algebra R C]
    [IsScalarTower R A C] [IsScalarTower R B C]
    [Algebra.IsPushout R A B C]
    [Module.Finite R B] [Module.Projective R B]
    [Module.Finite A C] [Module.Projective A C] (x : B) :
    algebraMap R A (ProjectiveDeterminant.det (Algebra.lmul R B x)) =
      ProjectiveDeterminant.det (Algebra.lmul A C (algebraMap B C x)) := by
  let e := Algebra.IsPushout.equiv R A B C
  let f := Algebra.lmul R B x
  have hmap :
      e.toLinearMap.comp
          ((Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ[R] x)).comp e.symm.toLinearMap) =
        Algebra.lmul A C (algebraMap B C x) := by
    ext y
    simp [e, Algebra.IsPushout.equiv_tmul]
  calc
    algebraMap R A (ProjectiveDeterminant.det f) =
        ProjectiveDeterminant.det (f.baseChange A) :=
      det_baseChange_of_projective f
    _ = ProjectiveDeterminant.det
          (Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ[R] x)) := by
      rw [Algebra.baseChange_lmul]
    _ = ProjectiveDeterminant.det (Algebra.lmul A C (algebraMap B C x)) := by
      rw [← hmap]
      exact (det_conj_of_projective e.toLinearEquiv _).symm

/-- Alias of `AlgebraicGeometry.GroupoidScheme.finite_projective_of_isPushout`. -/
private alias finite_projective_of_ring_pushout :=
  GroupoidScheme.finite_projective_of_isPushout

/-- Alias of `AlgebraicGeometry.GroupoidScheme.map_det_lmul_of_isPushout`. -/
private alias norm_baseChange_of_ring_pushout :=
  GroupoidScheme.map_det_lmul_of_isPushout

/-- For a groupoid scheme with affine object scheme and finite locally free source map, the
arrow ring is a finite projective module over the object ring along the source map, and the
norm along the source map of a function pulled back along the target map is an invariant
function. -/
@[stacks 03BH]
theorem norm_targetMap_mem_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsFiniteLocallyFree G.source.left]
    (f : Γ(G.objects.left, ⊤)) :
    letI := (sourceMap G).toAlgebra
    ∃ (hfinite : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤))
      (hprojective : Module.Projective Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤)),
      letI := hfinite
      letI := hprojective
      ProjectiveDeterminant.det
        (Algebra.lmul Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) (targetMap G f)) ∈
          invariantRing G := by
  let : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
  obtain ⟨hfinite, hprojective⟩ := finite_projective_of_finiteLocallyFree G.source.left
  refine ⟨hfinite, hprojective, ?_⟩
  let : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := hfinite
  let : Module.Projective Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := hprojective
  let p0 : Γ(G.arrows.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map (pullback.fst G.source G.target).left.op).hom
  let p1 : Γ(G.arrows.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map (pullback.snd G.source G.target).left.op).hom
  let c : Γ(G.arrows.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map G.comp.left.op).hom
  obtain ⟨hfiniteD, hprojectiveD⟩ := finite_projective_of_ring_pushout
    (sourceMap G) (targetMap G) p0 p1 (composable_isPushout G).flip hfinite hprojective
  have hdef := norm_baseChange_of_ring_pushout
    (sourceMap G) (targetMap G) p0 p1 (composable_isPushout G).flip
    hfinite hprojective hfiniteD hprojectiveD (targetMap G f)
  have hcomp := norm_baseChange_of_ring_pushout
    (sourceMap G) (sourceMap G) c p1 (composition_source_isPushout G).flip
    hfinite hprojective hfiniteD hprojectiveD (targetMap G f)
  show sourceMap G (ProjectiveDeterminant.det
      (Algebra.lmul Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) (targetMap G f))) =
    targetMap G (ProjectiveDeterminant.det
      (Algebra.lmul Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) (targetMap G f)))
  have hmap : c (targetMap G f) = p0 (targetMap G f) :=
    congrArg (fun h : Γ(G.objects.left, ⊤) →+*
      Γ((pullback G.source G.target).left, ⊤) => h f)
      (over_appTop_comp_eq G.comp G.target
        (pullback.fst G.source G.target) G.target G.target_comp)
  rw [hcomp, hdef, hmap]

end AlgebraicGeometry

end
