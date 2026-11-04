module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The quotient of the structure sheaf by the ideal of a closed subspace

Let `Z` be a closed subspace of an algebraic space `X`, with defining ideal sheaf `𝓘_Z`. The
structure map `𝒪_X ⟶ i_*𝒪_Z` is an epimorphism with kernel `𝓘_Z` (Stacks 03MB), so
`𝒪_X / 𝓘_Z ≅ i_*𝒪_Z`; in particular the support of `𝒪_X / 𝓘_Z` is the point set of `Z`.

## Main results

* `AlgebraicGeometry.Space.cokernelDefiningIdealSheafIso`: `𝒪_X / 𝓘_Z ≅ i_*𝒪_Z`.
* `AlgebraicGeometry.Space.supportOfSheaf_cokernel_definingIdealSheaf`: the support of
  `𝒪_X / 𝓘_Z` is `|Z|`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **`𝒪_X / 𝓘_Z ≅ i_*𝒪_Z`** for a closed subspace `Z` of `X`: the structure map onto
`i_*𝒪_Z` is an epimorphism whose kernel is the defining ideal sheaf. -/
def cokernelDefiningIdealSheafIso :
    cokernel (definingIdealSheaf B S hS X Z).ι ≅
      structureSheafPushforward B S hS (subspaceInclusion B S hS X Z) := by
  let i := subspaceInclusion B S hS X Z
  let p := pushforwardStructureProjection B S hS i
  haveI : Epi p := epi_pushforwardStructureProjection B S hS i Z.2.2
  have hk : definingIdealSheaf B S hS X Z = SheafOfModules.Submodule.ker p :=
    (kernelIdealSheaf_eq_definingIdealSheaf B S hS X Z).symm.trans
      (ker_pushforwardStructureProjection B S hS i).symm
  exact eqToIso (by rw [hk]; rfl) ≪≫
    (cokernelIsCokernel (SheafOfModules.Submodule.ker p).ι).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (SheafOfModules.Submodule.isLimitKernelFork p))

attribute [local instance] pointTopology

/-- **The support of `𝒪_X / 𝓘_Z` is the point set of `Z`.** -/
theorem supportOfSheaf_cokernel_definingIdealSheaf :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
        (cokernel (definingIdealSheaf B S hS X Z).ι)) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  have h := supportOfSheaf_structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩
  refine (supportOfSheaf_eq_of_iso B S hS X (cokernelDefiningIdealSheafIso B S hS X Z)).trans ?_
  refine (supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2 _ ?_).trans ?_
  · show IsClosed (supportOfSheaf B S hS Z.1.toFunctor ((SheafOfModules.toSheaf _).obj
      (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩)))
    rw [h]
    exact isClosed_univ
  · show pointsMap B S hS Z.1.toFunctor Z.1.ι '' supportOfSheaf B S hS Z.1.toFunctor
      ((SheafOfModules.toSheaf _).obj (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩)) = _
    rw [h, Set.image_univ]

end AlgebraicGeometry.Space

end
