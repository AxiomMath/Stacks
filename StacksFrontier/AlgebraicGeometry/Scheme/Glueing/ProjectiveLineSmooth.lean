module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# The projective line is smooth over its base

The structure morphism of the projective line over a commutative ring `k` is smooth, and over a
field it has relative dimension one.

## Main results

* `AlgebraicGeometry.projectiveLineAffineStructureMorphism_smooth`: the structure morphism of
  either affine chart is smooth.
* `AlgebraicGeometry.projectiveLine_smooth`, registered as the instance
  `AlgebraicGeometry.projectiveLine_smooth_inst`: the structure morphism of the projective line
  is smooth.
* `AlgebraicGeometry.isIso_fromSpecResidueField_spec_field`: at the unique point of the spectrum
  of a field the canonical morphism from the spectrum of the residue field is an isomorphism.
* `AlgebraicGeometry.projectiveLine_relativeDimension`: the structure morphism of the projective
  line over a field has relative dimension one.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable (k : Type u) [CommRing k]

/-- The structure morphism `Spec k[X] ⟶ Spec k` of either affine chart of the projective line is
smooth. -/
theorem projectiveLineAffineStructureMorphism_smooth :
    Smooth (projectiveLineAffineStructureMorphism k) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  show RingHom.Smooth (algebraMap k (Polynomial k))
  rw [RingHom.smooth_algebraMap]
  have : Algebra.Smooth k (MvPolynomial PUnit.{1} k) :=
    { formallySmooth := inferInstance, finitePresentation := inferInstance }
  exact Algebra.Smooth.of_equiv (MvPolynomial.uniqueAlgEquiv.{u, 0} k PUnit)

/-- **The structure morphism of the projective line is smooth.** -/
theorem projectiveLine_smooth : Smooth (projectiveLine k ↘ Spec (.of k)) := by
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_openCover (projectiveLineGluingData k).openCover fun i ↦ ?_
  have h : (projectiveLineGluingData k).openCover.f i ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k := (projectiveLineStructureMorphism k).2 i
  rw [h]
  exact projectiveLineAffineStructureMorphism_smooth k

/-- The structure morphism of the projective line is smooth. -/
instance projectiveLine_smooth_inst : Smooth (projectiveLine k ↘ Spec (.of k)) :=
  projectiveLine_smooth k

end

section

variable (k : Type u) [Field k]

/-- At the point of the spectrum of a field, the canonical morphism from the spectrum of the
residue field is an isomorphism. -/
theorem isIso_fromSpecResidueField_spec_field (s : Spec (CommRingCat.of k)) :
    IsIso ((Spec (CommRingCat.of k)).fromSpecResidueField s) := by
  have hclosed : IsClosed (Set.range ((Spec (CommRingCat.of k)).fromSpecResidueField s)) := by
    rw [Scheme.range_fromSpecResidueField, (Set.singleton_nonempty s).eq_univ]
    exact isClosed_univ
  have : IsClosedImmersion ((Spec (CommRingCat.of k)).fromSpecResidueField s) :=
    IsClosedImmersion.of_isPreimmersion _ hclosed
  have : Surjective ((Spec (CommRingCat.of k)).fromSpecResidueField s) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint ((Spec (CommRingCat.of k)).residueField s),
      Subsingleton.elim _ z⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- **The projective line over a field has relative dimension one.** -/
theorem projectiveLine_relativeDimension :
    RelativeDimension (projectiveLine k ↘ Spec (.of k)) 1 := by
  intro s _
  have : IsIso ((Spec (CommRingCat.of k)).fromSpecResidueField s) :=
    isIso_fromSpecResidueField_spec_field k s
  have hiso : IsIso ((projectiveLine k ↘ Spec (.of k)).fiberι s) := by
    show IsIso (pullback.fst (projectiveLine k ↘ Spec (.of k))
      ((Spec (CommRingCat.of k)).fromSpecResidueField s))
    infer_instance
  have _ : IrreducibleSpace (projectiveLine k) := projectiveLine_irreducibleSpace k
  let e := Scheme.homeoOfIso (asIso ((projectiveLine k ↘ Spec (.of k)).fiberι s))
  refine ⟨TopologicalSpace.Equidimensional.of_homeomorph e
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace _), ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact topologicalKrullDim_projectiveLine k

end

end AlgebraicGeometry

end
