module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLinePoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSeparated
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The affine line inside the projective line over a ring

For a commutative ring `A`, the projective line `ℙ¹_A ⟶ Spec A` contains the affine line
`𝔸¹_A = Spec A[X]` as the open chart `j`, whose complement is the section at infinity
`i : Spec A ⟶ ℙ¹_A`, a closed immersion with `i ≫ g = 𝟙`; in the other chart `Spec A[Y]` the
affine line is the basic open `D(Y)`. The fibres of `g : ℙ¹_A ⟶ Spec A` have dimension at most
one. This is the geometry of the compactification `𝔸^d_K ⊂ ℙ¹ × 𝔸^{d-1}_K` used in the proof of
Stacks 0F0V, with `A = K[t₁, …, t_{d-1}]`.

## Main results

* `AlgebraicGeometry.projectiveLineYChart_mem_range_xChart_iff`: in the second chart, the first
  chart is `D(Y)`.
* `AlgebraicGeometry.projectiveLineInfinitySection`, with
  `AlgebraicGeometry.projectiveLineInfinitySection_comp_structureMorphism`,
  `AlgebraicGeometry.range_projectiveLineInfinitySection` and its closed-immersion instance.
* `AlgebraicGeometry.topologicalKrullDim_fiber_projectiveLine_le_one`.
* `AlgebraicGeometry.topologicalKrullDim_pullback_spec_C_le_one`: the base change of the affine
  line to a field has dimension at most one.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The affine line over a field has dimension one, after any base change to a field.** For a
ring map `φ : A ⟶ L` to a field, the base change of `Spec A[X] ⟶ Spec A` along `Spec φ` is
`Spec L[X]`, of dimension one. -/
public theorem topologicalKrullDim_pullback_spec_C_le_one {A : Type u} [CommRing A]
    {L : CommRingCat.{u}} (hL : IsField L) (φ : CommRingCat.of A ⟶ L) :
    topologicalKrullDim (pullback (Spec.map (CommRingCat.ofHom (C : A →+* A[X]))) (Spec.map φ) :
      Scheme.{u}) ≤
      1 := by
  let : Field L := hL.toField
  let : Algebra A L := φ.hom.toAlgebra
  rw [show φ = CommRingCat.ofHom (algebraMap A L) from rfl,
    show CommRingCat.ofHom (C : A →+* A[X]) = CommRingCat.ofHom (algebraMap A A[X]) from rfl]
  let e' : A[X] ⊗[A] L ≃ₐ[A] L[X] :=
    (Algebra.TensorProduct.comm A A[X] L).trans ((polyEquivTensor A L).symm.restrictScalars A)
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (pullbackSpecIso A A[X] L)).isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum (A[X] ⊗[A] L)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv e'.toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

section ProjectiveLine

variable (A : Type u) [CommRing A]

/-- **In the second chart of the projective line, the first chart is `D(Y)`.** -/
public theorem projectiveLineYChart_mem_range_xChart_iff (p : Spec (.of A[X])) :
    projectiveLineYChart A p ∈ Set.range (projectiveLineXChart A) ↔
      (X : A[X]) ∉ p.asIdeal := by
  rw [← mem_range_projectiveLinePuncturedChart_iff A p]
  have h := isPullback_projectiveLineCharts' A
  have hfst : Set.range (projectiveLinePuncturedChart A) =
      Set.range (pullback.fst (projectiveLineYChart A) (projectiveLineXChart A)) := by
    rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      show Set.range ⇑h.isoPullback.hom = Set.univ from
        (Scheme.homeoOfIso h.isoPullback).surjective.range_eq, Set.image_univ]
  rw [hfst, Scheme.Pullback.range_fst]
  rfl

/-- The section at infinity `Spec A ⟶ ℙ¹_A`: the origin of the second chart, `Y = 0`. -/
public def projectiveLineInfinitySection : Spec (.of A) ⟶ projectiveLine A :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) ≫ projectiveLineYChart A

/-- The section at infinity is a section of the structure morphism. -/
@[reassoc]
public theorem projectiveLineInfinitySection_comp_structureMorphism :
    projectiveLineInfinitySection A ≫ (projectiveLine A ↘ Spec (.of A)) = 𝟙 _ := by
  rw [projectiveLineInfinitySection, Category.assoc, projectiveLineYChart_comp_structureMorphism,
    projectiveLineAffineStructureMorphism, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of A)
  ext a
  simp

/-- **The section at infinity is the complement of the first chart.** -/
public theorem range_projectiveLineInfinitySection :
    Set.range (projectiveLineInfinitySection A) = (Set.range (projectiveLineXChart A))ᶜ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [projectiveLineInfinitySection, Scheme.Hom.comp_apply, Set.mem_compl_iff,
      projectiveLineYChart_mem_range_xChart_iff, not_not]
    change Polynomial.X ∈ Ideal.comap (Polynomial.evalRingHom (0 : A)) z.asIdeal
    simp
  · intro hx
    obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData A).ι_jointly_surjective x
    obtain ⟨i⟩ := i
    cases i
    · exact absurd ⟨y, rfl⟩ hx
    · have hy : (X : A[X]) ∈ y.asIdeal :=
        not_not.1 fun hy => hx ((projectiveLineYChart_mem_range_xChart_iff A y).2 hy)
      have hmem : y ∈ Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : A))) := by
        rw [range_comap_of_surjective _ _ fun a => ⟨Polynomial.C a, by simp⟩]
        change RingHom.ker _ ≤ y.asIdeal
        rwa [Polynomial.ker_evalRingHom, map_zero, sub_zero, Ideal.span_singleton_le_iff_mem]
      obtain ⟨z, hz⟩ := hmem
      exact ⟨z, congrArg (projectiveLineYChart A) hz⟩

/-- The section at infinity is a closed immersion. -/
public instance : IsClosedImmersion (projectiveLineInfinitySection A) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))) :=
    IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩
  have : IsPreimmersion (projectiveLineInfinitySection A) := by
    unfold projectiveLineInfinitySection
    infer_instance
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [range_projectiveLineInfinitySection]
  exact (projectiveLineXChart A).isOpenEmbedding.isOpen_range.isClosed_compl

/-- **The fibres of the projective line over a ring have dimension at most one.** Each point of a
fibre lies in the base change of one of the two charts, which is an open subscheme of the fibre
isomorphic to the base change of the affine line to the residue field. -/
public theorem topologicalKrullDim_fiber_projectiveLine_le_one (t : Spec (.of A)) :
    topologicalKrullDim ((projectiveLine A ↘ Spec (.of A)).fiber t) ≤ 1 := by
  let g := projectiveLine A ↘ Spec (.of A)
  change topologicalKrullDim (g.fiber t) ≤ 1
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  obtain ⟨i, w, hw⟩ := (projectiveLineGluingData A).ι_jointly_surjective (g.fiberι t z)
  have hc : (projectiveLineGluingData A).ι i ≫ g = projectiveLineAffineStructureMorphism A :=
    (projectiveLineStructureMorphism A).2 i
  obtain ⟨p, rfl⟩ :
      z ∈ Set.range (pullback.snd ((projectiveLineGluingData A).ι i) (g.fiberι t)) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨w, hw⟩
  rw [(pullback.snd ((projectiveLineGluingData A).ι i) (g.fiberι t))
    |>.isOpenEmbedding.topologicalKrullDimAt_eq]
  refine (topologicalKrullDimAt_le_topologicalKrullDim p).trans ?_
  have e : pullback ((projectiveLineGluingData A).ι i) (g.fiberι t) ≅
      pullback (Spec.map (CommRingCat.ofHom (C : A →+* A[X])))
        (Spec.map (Spec.preimage ((Spec (.of A)).fromSpecResidueField t))) :=
    pullbackRightPullbackFstIso g ((Spec (.of A)).fromSpecResidueField t)
      ((projectiveLineGluingData A).ι i) ≪≫ pullback.congrHom hc
        (Spec.map_preimage ((Spec (.of A)).fromSpecResidueField t)).symm
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
  exact topologicalKrullDim_pullback_spec_C_le_one (Field.toIsField _) _

end ProjectiveLine

end AlgebraicGeometry

end
