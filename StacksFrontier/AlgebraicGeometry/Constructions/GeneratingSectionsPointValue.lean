module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety

/-!
# The value at a point of the morphism classified by a linear system

`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections` is the
morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` attached to a `k`-linear map `ψ : V → Γ(X, ℒ)` into the global
sections of an invertible module whose nonvanishing opens cover `X`. This file computes **where it
sends a point**.

The image of a point `x` is located by the first clause of
`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.Classifies`: the preimage of the standard open
`D₊(f)` of a degree-one form `f` is the nonvanishing open of `ψ(f)`. Read at `x`, this says which
degree-one forms lie in the homogeneous prime of `φ(x)` — those `v` with `ψ(v)` vanishing at
`x` — and a point of `𝐏(V)` is determined by that submodule as soon as it is the kernel of a
nonzero functional (`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace_ker`). Only the
inclusion `ker φ ≤ {v | ψ(v) vanishes at x}` is needed: a point of `𝐏(V)` lying on the
hyperplane of `φ` *is* the point of `φ`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections`.

* `preimage_basicOpen_morphismOfGeneratingSections`: the preimage of the standard open of a
  vector is the nonvanishing open of its section.
* `ι_mem_asHomogeneousIdeal_iff`: a degree-one form lies in the homogeneous prime at the image of
  `x` exactly when its section vanishes at `x`.
* `morphismOfGeneratingSections_base_eq`: **the image of `x` is the point cut out by any nonzero
  functional whose nonvanishing is the nonvanishing of the sections at `x`.**

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] globalSectionsModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]
  (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤)

/-- **The preimage of a standard open is the nonvanishing open of its section.** This is clause
(a) of [Stacks, Tag 01N8] read on a vector of `V` rather than on an abstract degree-one element:
the degree-one section the graded map attaches to `v` is `ψ v`, read in the first tensor power. -/
public theorem preimage_basicOpen_morphismOfGeneratingSections (v : V) :
    morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        _root_.AlgebraicGeometry.Proj.basicOpen (symmetricGrading k V) (SymmetricAlgebra.ι k V v) =
      nonvanishingOpen X L (ψ v) := by
  refine ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V v)).trans ?_
  change nonvanishingOpen X (natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1) = _
  rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]

/-- **Which degree-one forms vanish at the image of a point:** those whose section vanishes
there. -/
public theorem ι_mem_asHomogeneousIdeal_iff (x : X) (v : V) :
    SymmetricAlgebra.ι k V v ∈
        ((morphismOfGeneratingSections k V L ψ hψ).base x).asHomogeneousIdeal ↔
      x ∉ nonvanishingOpen X L (ψ v) := by
  have hpre : (x ∈ morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        _root_.AlgebraicGeometry.Proj.basicOpen (symmetricGrading k V) (SymmetricAlgebra.ι k V v)) ↔
      SymmetricAlgebra.ι k V v ∉
        ((morphismOfGeneratingSections k V L ψ hψ).base x).asHomogeneousIdeal := Iff.rfl
  rw [preimage_basicOpen_morphismOfGeneratingSections k V L ψ hψ v] at hpre
  rw [← not_iff_not, not_not, hpre]

/-- **The image of a point under `φ_{ℒ,ψ}`.** If a nonzero functional `φ` on `V` is nonzero
exactly on the vectors whose sections do not vanish at `x`, then `φ_{ℒ,ψ}` sends `x` to the point
of `𝐏(V)` that `φ` cuts out.

Only one inclusion of the hypothesis is used — that `ψ(v)` vanishes at `x` whenever `φ` kills
`v` — because a point lying on the hyperplane of a nonzero functional already is the point of
that functional. -/
public theorem morphismOfGeneratingSections_base_eq (x : X) {φ : Module.Dual k V} (hφ : φ ≠ 0)
    (h : ∀ v : V, φ v = 0 → x ∉ nonvanishingOpen X L (ψ v)) :
    (morphismOfGeneratingSections k V L ψ hψ).base x = linearFunctionalPoint k V φ hφ := by
  have hsub : LinearMap.ker φ ≤
      pointSubmodule k V ((morphismOfGeneratingSections k V L ψ hψ).base x) := by
    intro v hv
    rw [mem_pointSubmodule_iff, ι_mem_asHomogeneousIdeal_iff]
    exact h v (LinearMap.mem_ker.mp hv)
  have hmem := (mem_linearSubspace_iff k V (LinearMap.ker φ) _).mpr hsub
  rwa [linearSubspace_ker k V φ hφ, Set.mem_singleton_iff] at hmem

end Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

end
