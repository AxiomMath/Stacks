module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentExtensions
public import StacksFrontier.AlgebraicGeometry.Topologies.CechAmitsurQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of Čech cohomology of quasi-coherent modules on the bounded small étale site

Let `F` be a quasi-coherent module on a scheme `S`. On the cardinality-bounded small étale site
`AlgebraicGeometry.SmallEtale B S hS`, the Čech cohomology `Ȟ^p(𝒰, Fᵃ)` of the sections of `Fᵃ` on
a standard étale covering `𝒰` of an affine object vanishes for `p ≥ 1`.

The Čech complex of a family in the bounded site with coefficients `Fᵃ` is the Čech complex of its
image family in `Over S` under `AlgebraicGeometry.SmallEtale.toOver`, with the same coefficients.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsBoundedStandardCovering`: a family in the bounded small étale
  site whose image family in `Over S` is a standard étale covering of an affine object.

## Main results

* `AlgebraicGeometry.SmallEtale.cechComplexIsoImage`: the Čech complex in the bounded site is
  the Čech complex of the image family in `Over S`.
* `AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_associatedPresheaf`:
  `Ȟ^p(𝒰, Fᵃ) = 0` for `p ≥ 1` and `𝒰` a standard covering in the bounded small étale site.
* `AlgebraicGeometry.SmallEtale.IsBoundedStandardCovering.sieve₀_mem_topology`: a standard
  covering generates a covering sieve.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Standard coverings of the bounded small étale site -/

/-- A family in the cardinality-bounded small étale site of `S` is a *standard* covering when
the total space of its target is affine and the family of schemes underlying its image in
`Over S` is a standard étale covering of that total space. -/
public def IsBoundedStandardCovering {T : SmallEtale B S hS} (E : PreZeroHypercover.{v} T) :
    Prop :=
  ∃ h : _root_.AlgebraicGeometry.IsAffine ((toOver B S hS).obj T).left,
    @AlgebraicGeometry.IsStandardCovering .etale ((toOver B S hS).obj T).left h E.I₀
      (fun i ↦ ((toOver B S hS).obj (E.X i)).left)
      (fun i ↦ ((toOver B S hS).map (E.f i)).left)

/-- The target of a standard covering of the bounded small étale site, and each of its members,
has affine total space. -/
public theorem IsBoundedStandardCovering.isAffine {T : SmallEtale B S hS}
    {E : PreZeroHypercover.{v} T} (h : IsBoundedStandardCovering B S hS E) :
    _root_.AlgebraicGeometry.IsAffine ((toOver B S hS).obj T).left ∧
      ∀ i, _root_.AlgebraicGeometry.IsAffine ((toOver B S hS).obj (E.X i)).left := by
  obtain ⟨hT, hstd⟩ := h
  let := hT
  exact ⟨hT, hstd.affine_source⟩

/-- A standard covering of the bounded small étale site has finitely many members. -/
public theorem IsBoundedStandardCovering.finite {T : SmallEtale B S hS}
    {E : PreZeroHypercover.{v} T} (h : IsBoundedStandardCovering B S hS E) : Finite E.I₀ := by
  obtain ⟨hT, hstd⟩ := h
  let := hT
  exact hstd.finite_index

/-- **A standard covering of the bounded small étale site generates a covering sieve.** -/
public theorem IsBoundedStandardCovering.sieve₀_mem_topology {T : SmallEtale B S hS}
    (E : PreZeroHypercover.{v} T) (h : IsBoundedStandardCovering B S hS E) :
    E.sieve₀ ∈ topology B S hS T := by
  obtain ⟨hT, hstd⟩ := h
  refine mem_topology_of_jointlySurjective (fun x ↦ ?_)
  have hx : x ∈ (⋃ i, Set.range ((toOver B S hS).map (E.f i)).left.base) := by
    rw [hstd.jointly_surjective]; trivial
  obtain ⟨_, ⟨i, rfl⟩, y, hy⟩ := hx
  exact ⟨E.X i, E.f i, E.sieve₀_f i, y, hy⟩

/-! ### Fibre products along the inclusion of the size-bounded category of schemes -/

/-- `Over.post` of the inclusion of the size-bounded category of schemes preserves fibre
products. -/
public instance preservesPullbacks_overPostInclusion {X : B.Scheme} :
    PreservesLimitsOfShape WalkingCospan (Over.post (X := X) B.inclusion) where
  preservesLimit {K} := by
    have h : PreservesLimit K
        (Over.post (X := X) B.inclusion ⋙ Over.forget (B.inclusion.obj X)) := by
      rw [Over.post_forget_eq_forget_comp]
      infer_instance
    exact preservesLimit_of_reflects_of_preserves _ (Over.forget _)

/-! ### The Čech complex is the Čech complex of the image family -/

/-- **The Čech complex of a family in the bounded small étale site is the Čech complex of its
image family in `Over S`.** -/
public noncomputable def cechComplexIsoImage (F : S.Modules) [F.IsQuasicoherent]
    {T : SmallEtale B S hS} (E : PreZeroHypercover.{u} T) :
    cechComplex E ((toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F) ≅
      cechComplex (E.map (toOver B S hS)) (quasiCoherentPresheafFunctor S F) :=
  (cechComplexIsoOfFunctor (toOver B S hS) E (quasiCoherentPresheafFunctor S F)
    (fun n i ↦ isIso_cechProductMapOfFunctor_toOver B S hS E n i)).symm

/-! ### Vanishing of Čech cohomology on the bounded small étale site -/

/-- **Vanishing of Čech cohomology on the cardinality-bounded small étale site of `S`.** The Čech
cohomology of the sections of `Fᵃ` on a standard covering of an object of
`AlgebraicGeometry.SmallEtale B S hS` vanishes in every positive degree. -/
@[stacks 03FJ "the `Cech^p = 0 for p >= 1` clause on the cardinality-bounded small étale site"]
public theorem isZero_cechCohomology_succ_associatedPresheaf (F : S.Modules)
    [F.IsQuasicoherent] {T : SmallEtale B S hS} (E : PreZeroHypercover.{u} T)
    (h : IsBoundedStandardCovering B S hS E) (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E
      ((toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F) p) := by
  obtain ⟨hT, hstd⟩ := h
  let := hT
  exact (isZero_cechCohomology_succ_quasiCoherentPresheaf ((toOver B S hS).obj T) .etale F
      (E.map (toOver B S hS)) hstd p hp).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
      (cechComplexIsoImage B S hS F E))

end AlgebraicGeometry.SmallEtale

end
