module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.Determinant
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineBasis

/-!
# The norm of a function pulled back along the target of an affine groupoid scheme

Let `G` be a groupoid scheme whose object scheme is affine and whose source map is finite
locally free. Then the arrow scheme is affine as well, and the arrow ring is a finite
projective module over the object ring through the source map. The norm along the source map
of a function pulled back along the target map is then an invariant function.

This is the determinant trick: the two pullbacks of the arrow ring to the ring of composable
arrows, along the second projection and along composition, are both base changes of the arrow
ring along the source map, and the function in question has the same image under both.

## Main results

* `AlgebraicGeometry.GroupoidScheme.finite_projective_appTop_of_isFiniteLocallyFree`: a finite
  locally free morphism to an affine scheme makes the source ring a finite projective module
  over the target ring.
* `AlgebraicGeometry.GroupoidScheme.det_lmul_targetMap_mem_invariantRing`: the determinant
  trick.

## Implementation notes

The coordinate rings are taken canonically to be the rings of global functions, rather than
being supplied through chosen affine presentations; pullback on global functions supplies the
source and target maps `AlgebraicGeometry.sourceMap` and `AlgebraicGeometry.targetMap`, and
their equalizer is `AlgebraicGeometry.invariantRing`. Only the source map is required to be
finite locally free; together with affineness of the object scheme this forces the arrow
scheme to be affine. The finite projective structures on the arrow ring are existentially
bound in the statement alongside the invariance of the norm, because the determinant cannot
be written down without them; its value does not depend on these proof-valued witnesses.

## References

* [Stacks Project, Tag 03BH](https://stacks.math.columbia.edu/tag/03BH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- For a finite locally free morphism to an affine scheme, the ring of global functions on the
source is a finite projective module over the ring of global functions on the target. -/
theorem finite_projective_appTop_of_isFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [IsFiniteLocallyFree f] :
    letI := f.appTop.hom.toAlgebra
    Module.Finite Γ(Y, ⊤) Γ(X, ⊤) ∧ Module.Projective Γ(Y, ⊤) Γ(X, ⊤) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨hfinite, hflat, hpresentation⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp inferInstance
  have : IsFinite f := hfinite
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := hpresentation
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := f.flat_appTop
  have : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    have : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := f.finitePresentation_appTop
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-- The square of global-function rings attached to the composable arrows of an affine groupoid
scheme with finite locally free source is a pushout of commutative rings. -/
theorem composables_isPushout {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsFiniteLocallyFree G.source.left] :
    IsPushout (CommRingCat.ofHom (sourceMap G)) (CommRingCat.ofHom (targetMap G))
      (CommRingCat.ofHom ((Scheme.Γ.map (pullback.fst G.source G.target).left.op).hom))
      (CommRingCat.ofHom ((Scheme.Γ.map (pullback.snd G.source G.target).left.op).hom)) := by
  have : IsAffine G.arrows.left := isAffine_of_isAffineHom G.source.left
  exact isPushout_appTop_of_isPullback
    ((IsPullback.of_hasPullback G.source G.target).map (Over.forget S))

/-- The square of global-function rings formed by the source map and the composition map of an
affine groupoid scheme with finite locally free source is a pushout of commutative rings. -/
theorem composition_source_isPushout {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsFiniteLocallyFree G.source.left] :
    IsPushout (CommRingCat.ofHom (sourceMap G)) (CommRingCat.ofHom (sourceMap G))
      (CommRingCat.ofHom ((Scheme.Γ.map G.comp.left.op).hom))
      (CommRingCat.ofHom ((Scheme.Γ.map (pullback.snd G.source G.target).left.op).hom)) := by
  have : IsAffine G.arrows.left := isAffine_of_isAffineHom G.source.left
  exact isPushout_appTop_of_isPullback
    ((GroupoidScheme.comp_source_isPullback G).map (Over.forget S))

/-- Finiteness and projectivity transported across a pushout square of commutative rings. -/
theorem finite_projective_of_isPushout {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (s : R →+* B) (t : R →+* A) (p : B →+* C) (q : A →+* C)
    (H : IsPushout (CommRingCat.ofHom t) (CommRingCat.ofHom s)
      (CommRingCat.ofHom q) (CommRingCat.ofHom p))
    (hfinite : letI := s.toAlgebra; Module.Finite R B)
    (hprojective : letI := s.toAlgebra; Module.Projective R B) :
    letI := q.toAlgebra
    Module.Finite A C ∧ Module.Projective A C := by
  let : Algebra R B := s.toAlgebra
  let : Algebra R A := t.toAlgebra
  let : Algebra B C := p.toAlgebra
  let : Algebra A C := q.toAlgebra
  let : Algebra R C := (q.comp t).toAlgebra
  have hcomm : q.comp t = p.comp s := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
      congrArg CommRingCat.Hom.hom H.w
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' hcomm
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsPushout R A B C := (CommRingCat.isPushout_iff_isPushout).mp H
  have : Module.Finite R B := hfinite
  have : Module.Projective R B := hprojective
  exact ⟨Module.Finite.equiv (Algebra.IsPushout.equiv R A B C).toLinearEquiv,
    Module.Projective.of_equiv' (Algebra.IsPushout.equiv R A B C).toLinearEquiv⟩

/-- The projective norm commutes with base change along a pushout square of commutative rings,
read as a square of ring homomorphisms. -/
theorem map_det_lmul_of_isPushout {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (s : R →+* B) (t : R →+* A) (p : B →+* C) (q : A →+* C)
    (H : IsPushout (CommRingCat.ofHom t) (CommRingCat.ofHom s)
      (CommRingCat.ofHom q) (CommRingCat.ofHom p))
    (hfinite : letI := s.toAlgebra; Module.Finite R B)
    (hprojective : letI := s.toAlgebra; Module.Projective R B)
    (hfiniteC : letI := q.toAlgebra; Module.Finite A C)
    (hprojectiveC : letI := q.toAlgebra; Module.Projective A C) (x : B) :
    letI := s.toAlgebra
    letI := q.toAlgebra
    letI := hfinite
    letI := hprojective
    letI := hfiniteC
    letI := hprojectiveC
    t (ProjectiveDeterminant.det (Algebra.lmul R B x)) =
      ProjectiveDeterminant.det (Algebra.lmul A C (p x)) := by
  let : Algebra R B := s.toAlgebra
  let : Algebra A C := q.toAlgebra
  have : Module.Finite R B := hfinite
  have : Module.Projective R B := hprojective
  have : Module.Finite A C := hfiniteC
  have : Module.Projective A C := hprojectiveC
  exact (Algebra.projectiveNorm_pushout (CommRingCat.ofHom s) (CommRingCat.ofHom t)
    (CommRingCat.ofHom p) (CommRingCat.ofHom q) H.flip x).symm

/-- **Stacks Project, Tag 03BH.** For a groupoid scheme with affine object scheme and finite
locally free source map, the norm along the source map of a function pulled back along the
target map is an invariant function. -/
@[stacks 03BH]
theorem det_lmul_targetMap_mem_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsFiniteLocallyFree G.source.left] (f : Γ(G.objects.left, ⊤)) :
    letI := (sourceMap G).toAlgebra
    ∃ (hfinite : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤))
      (hprojective : Module.Projective Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤)),
      letI := hfinite
      letI := hprojective
      ProjectiveDeterminant.det
          (Algebra.lmul Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) (targetMap G f)) ∈
        invariantRing G := by
  let : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
  obtain ⟨hfinite, hprojective⟩ :=
    finite_projective_appTop_of_isFiniteLocallyFree G.source.left
  refine ⟨hfinite, hprojective, ?_⟩
  let : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := hfinite
  let : Module.Projective Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := hprojective
  set p₀ : Γ(G.arrows.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map (pullback.fst G.source G.target).left.op).hom with hp₀
  set p₁ : Γ(G.arrows.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map (pullback.snd G.source G.target).left.op).hom with hp₁
  set c : Γ(G.arrows.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map G.comp.left.op).hom with hc
  obtain ⟨hfiniteD, hprojectiveD⟩ := finite_projective_of_isPushout
    (sourceMap G) (targetMap G) p₀ p₁ (composables_isPushout G).flip hfinite hprojective
  have hdef := map_det_lmul_of_isPushout (sourceMap G) (targetMap G) p₀ p₁
    (composables_isPushout G).flip hfinite hprojective hfiniteD hprojectiveD (targetMap G f)
  have hcomp := map_det_lmul_of_isPushout (sourceMap G) (sourceMap G) c p₁
    (composition_source_isPushout G).flip hfinite hprojective hfiniteD hprojectiveD
    (targetMap G f)
  change sourceMap G (ProjectiveDeterminant.det
      (Algebra.lmul Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) (targetMap G f))) =
    targetMap G (ProjectiveDeterminant.det
      (Algebra.lmul Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) (targetMap G f)))
  have hmap : c (targetMap G f) = p₀ (targetMap G f) :=
    congrArg
      (fun h : Γ(G.objects.left, ⊤) →+* Γ((pullback G.source G.target).left, ⊤) => h f)
      (over_appTop_comp_eq G.comp G.target (pullback.fst G.source G.target) G.target
        G.target_comp)
  rw [hcomp, hdef, hmap]

end AlgebraicGeometry.GroupoidScheme

end

end
