module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct

/-!
# The tautological endomorphism of a line in the parameter space

A closed point of the line `ℓ = 𝐏((End V)ᵛ ⧸ L)` is cut out by a nonzero functional `μ` on the
corank-two quotient `(End V)ᵛ ⧸ L`. Composing `μ` with the quotient map gives a functional on
`(End V)ᵛ`, that is an element of the double dual of `End V`, and for finite-dimensional `V` the
double dual is `End V` itself: so a closed point of the line names an endomorphism of `V`,
linearly in `μ`. This file writes that dictionary down and checks that it agrees with the
identification `AlgebraicGeometry.ProjectiveSpaceOfModule.dualEndClosedPointsEquiv` of the closed
points of the parameter space with the projective classes of endomorphisms: the endomorphism
`lineEnd μ` *represents* the point of the parameter space that `μ` cuts out on the line.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineEndₗ`: the linear map sending a functional on
  the corank-two quotient to an endomorphism of `V`, and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.lineEnd` its underlying function.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_lineEnd`: the defining identity
  `φ (lineEnd μ) = μ (φ mod L)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineEnd_ne_zero`: a nonzero functional names a
  nonzero endomorphism.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingLineι_linearFunctionalPoint`: the closed point
  of the line cut out by `μ`, read in the parameter space, is the point cut out by `μ ∘ mod L`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.representsParameterPoint_lineEnd`: **`lineEnd μ`
  represents that point of the parameter space.**

## Implementation notes

The dictionary is `LinearMap.dualMap` of the quotient map followed by the inverse of
`Module.evalEquiv`, so linearity in `μ` is immediate and no basis is chosen. The quotient map is
surjective, so its dual map is injective, which is what makes a nonzero functional name a nonzero
endomorphism.

That `lineEnd μ` represents the point is proved by comparing annihilators: both
`AlgebraicGeometry.ProjectiveSpaceOfModule.dualEndClosedPointsEquiv_apply` and
`apply_lineEnd` describe membership of a degree-one form `φ` in the homogeneous prime of the point
as the vanishing of `φ` at an endomorphism, so the two endomorphisms have the same annihilator in
`(End V)ᵛ` and `Module.Dual.exists_units_smul_eq_of_forall_eq_zero_iff`, applied to their images
under `Module.evalEquiv`, makes them proportional.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]

/-- **The tautological endomorphism attached to a functional on the corank-two quotient**, as a
linear map in that functional: compose with the quotient map `(End V)ᵛ ⟶ (End V)ᵛ ⧸ L` and read
the result in `End V` through the double dual. -/
public def lineEndₗ : Module.Dual k (lineSpace k V L) →ₗ[k] (V →ₗ[k] V) :=
  (Module.evalEquiv k (V →ₗ[k] V)).symm.toLinearMap ∘ₗ L.mkQ.dualMap

/-- **The tautological endomorphism attached to a functional on the corank-two quotient.** -/
public abbrev lineEnd (μ : Module.Dual k (lineSpace k V L)) : V →ₗ[k] V := lineEndₗ k V L μ

/-- **The defining identity of the tautological endomorphism**: a degree-one form `φ` on `End V`
takes at `lineEnd μ` the value of `μ` at the class of `φ`. -/
public theorem apply_lineEnd (μ : Module.Dual k (lineSpace k V L)) (φ : ParameterModule k V) :
    φ (lineEnd k V L μ) = μ (L.mkQ φ) := by
  have h : (Module.evalEquiv k (V →ₗ[k] V)) (lineEnd k V L μ) = L.mkQ.dualMap μ := by
    rw [lineEnd, lineEndₗ]
    exact (Module.evalEquiv k (V →ₗ[k] V)).apply_symm_apply _
  exact DFunLike.congr_fun h φ

/-- **A nonzero functional on the quotient names a nonzero endomorphism**: the quotient map is
surjective, so its dual map is injective. -/
public theorem lineEnd_ne_zero {μ : Module.Dual k (lineSpace k V L)} (hμ : μ ≠ 0) :
    lineEnd k V L μ ≠ 0 := by
  intro h
  refine hμ ((LinearMap.cancel_right L.mkQ_surjective).1 (LinearMap.ext fun φ => ?_))
  rw [LinearMap.comp_apply, ← apply_lineEnd k V L μ φ, h]
  simp

omit [FiniteDimensional k V] in
/-- **The closed point of the line cut out by `μ`, read in the parameter space**, is the closed
point cut out by `μ` composed with the quotient map. -/
public theorem movingLineι_linearFunctionalPoint {μ : Module.Dual k (lineSpace k V L)}
    (hμ : μ ≠ 0) (hcomp : μ ∘ₗ L.mkQ ≠ 0) :
    (movingLineι k V L).base (linearFunctionalPoint k (lineSpace k V L) μ hμ) =
      linearFunctionalPoint k (ParameterModule k V) (μ ∘ₗ L.mkQ) hcomp := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext fun z => ?_))
  have h1 : z ∈ ((movingLineι k V L).base
        (linearFunctionalPoint k (lineSpace k V L) μ hμ)).asHomogeneousIdeal.toIdeal ↔
      SymPow.symAlgMap L.mkQ z ∈
        (linearFunctionalPoint k (lineSpace k V L) μ hμ).asHomogeneousIdeal := Iff.rfl
  have h2 : z ∈ (linearFunctionalPoint k (ParameterModule k V) (μ ∘ₗ L.mkQ)
        hcomp).asHomogeneousIdeal.toIdeal ↔
      z ∈ (linearFunctionalPoint k (ParameterModule k V) (μ ∘ₗ L.mkQ)
        hcomp).asHomogeneousIdeal := Iff.rfl
  rw [h1, h2, linearFunctionalPoint_mem, linearFunctionalPoint_mem,
    SymPow.symAlgMap_comp_apply]

/-- **The tautological endomorphism represents the parameter point.** The closed point of the
parameter space `𝐏 = 𝐏((End V)ᵛ)` underlying the point of the line cut out by `μ` is the class of
`lineEnd μ`, so `lineEnd μ` is one of its representatives in the sense of
`AlgebraicGeometry.ProjectiveSpaceOfModule.RepresentsParameterPoint`. -/
public theorem representsParameterPoint_lineEnd [IsAlgClosed k]
    {μ : Module.Dual k (lineSpace k V L)} (hμ : μ ≠ 0)
    (p : ClosedPoints k (ParameterModule k V))
    (hp : (p : projectiveSpaceOfModule k (ParameterModule k V)) =
      (movingLineι k V L).base (linearFunctionalPoint k (lineSpace k V L) μ hμ)) :
    RepresentsParameterPoint k V p (lineEnd k V L μ) := by
  have hcomp : μ ∘ₗ L.mkQ ≠ 0 := fun h =>
    hμ ((LinearMap.cancel_right L.mkQ_surjective).1 (by rw [h, LinearMap.zero_comp]))
  have hne : lineEnd k V L μ ≠ 0 := lineEnd_ne_zero k V L hμ
  have hzero : ∀ φ : ParameterModule k V,
      (Module.evalEquiv k (V →ₗ[k] V)) (lineEnd k V L μ) φ = 0 ↔
        (Module.evalEquiv k (V →ₗ[k] V)) (dualEndClosedPointsEquiv k V p).rep φ = 0 := by
    intro φ
    rw [Module.evalEquiv_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
      Module.Dual.eval_apply,
      ← dualEndClosedPointsEquiv_apply k V p φ, hp,
      movingLineι_linearFunctionalPoint k V L hμ hcomp, linearFunctionalPoint_ι_mem,
      apply_lineEnd]
    rfl
  have hrne : (Module.evalEquiv k (V →ₗ[k] V)) (dualEndClosedPointsEquiv k V p).rep ≠ 0 :=
    fun h => (dualEndClosedPointsEquiv k V p).rep_nonzero
      ((Module.evalEquiv k (V →ₗ[k] V)).map_eq_zero_iff.1 h)
  obtain ⟨c, hc⟩ := Module.Dual.exists_units_smul_eq_of_forall_eq_zero_iff hrne hzero
  have hcr : (c : k) • (dualEndClosedPointsEquiv k V p).rep = lineEnd k V L μ := by
    refine (Module.evalEquiv k (V →ₗ[k] V)).injective ?_
    rw [map_smul, hc, Units.smul_def]
  refine ⟨hne, ?_⟩
  have h3 : Projectivization.mk k (lineEnd k V L μ) hne =
      Projectivization.mk k (dualEndClosedPointsEquiv k V p).rep
        (dualEndClosedPointsEquiv k V p).rep_nonzero :=
    (Projectivization.mk_eq_mk_iff k (lineEnd k V L μ) (dualEndClosedPointsEquiv k V p).rep hne
      (dualEndClosedPointsEquiv k V p).rep_nonzero).mpr ⟨c, by rw [Units.smul_def]; exact hcr⟩
  rw [h3, Projectivization.mk_rep]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
