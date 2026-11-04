module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.KernelCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSupportedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase

/-!
# The solution of the extension problem attached to a flat deformation

Let `Y ⊂ Y'` be a first order thickening of algebraic spaces over `S`, `f : X ⟶ Y`, and let
`D = (f' : X' ⟶ Y', i : X ⟶ X')` be a flat deformation of `f` over `Y'`
(`AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation`). Following the proof of
[Stacks Project, Tag 0D17], we think of `X` as the closed subspace `X'_0 = f'⁻¹(Y)` of `X'`:

* `X'_0 ⊂ X'` is a first order thickening (base change of `Y ⊂ Y'`), and `X ≅ X'_0`;
* by [Stacks Project, Tag 06BH] the conormal map `f'^*_0 𝒞_{Y/Y'} ⟶ 𝒞_{X'_0/X'}` is an
  isomorphism, `f'_0 : X'_0 ⟶ Y` the base change of `f'`;
* hence the extension `0 → 𝒞_{X'_0/X'} → 𝒪_{X'}|_{X'_0} → 𝒪_{X'_0} → 0`, with its kernel
  identified with `f'^*_0 𝒞_{Y/Y'}`, is a solution of the extension problem of
  [Stacks Project, Tag 08UF] attached to `f'_0` (`Deformation.solution`).

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  {X : AlgebraicSpaces B S hS} {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)}
  (D : Deformation f)

/-- The closed fibre `X'_0 = f'⁻¹(Y)` of a deformation, as a closed subspace of `X'`. -/
abbrev subspace : ClosedSubspaces B S hS D.X'.1 :=
  preimageSubspace B S hS D.f' Z

/-- The base change `f'_0 : X'_0 ⟶ Y` of `f'`. -/
abbrev reduction : (⟨D.subspace.1.toFunctor, D.subspace.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  preimageProjection B S hS D.f' Z

/-- The square formed by `X'_0 ⊂ X'`, `f'`, `f'_0` and `Y ⊂ Y'` commutes. -/
theorem reduction_comm :
    subspaceInclusion B S hS D.X' D.subspace ≫ D.f' =
      D.reduction ≫ subspaceInclusion B S hS Y' Z :=
  conormalEtaleRestrictionSquare B S hS D.f' Z

/-- The square `X'_0 ⊂ X'` over `Y ⊂ Y'` is cartesian. -/
theorem isPullback_subspace :
    IsPullback (subspaceInclusion B S hS D.X' D.subspace) D.reduction D.f'
      (subspaceInclusion B S hS Y' Z) :=
  isPullback_of_isPullback_hom B S hS (isPullback_preimageSubspace B S hS D.f' Z)

/-- `X'_0 ⊂ X'` is a first order thickening. -/
theorem isFirstOrderThickening_subspace (hZ : IsFirstOrderThickening B S hS Y' Z.1) :
    IsFirstOrderThickening B S hS D.X' D.subspace.1 :=
  isFirstOrderThickening_of_isPullback B S hS D.subspace Z D.f' D.reduction
    (isPullback_preimageSubspace B S hS D.f' Z) hZ

/-- `f'_0` is flat, as a base change of `f'`. -/
theorem isFlat_reduction : IsFlat B S hS D.reduction.hom :=
  isFlat_of_isPullback_of_isAlgebraicSpace B S hS (isPullback_preimageSubspace B S hS D.f' Z).flip
    D.X'.2 Y'.2 D.flat

/-- **[Stacks Project, Tag 06BH] at a flat deformation**: the conormal map
`f'^*_0 𝒞_{Y/Y'} ⟶ 𝒞_{X'_0/X'}` is an isomorphism. -/
theorem isIso_conormalMap (hZ : IsFirstOrderThickening B S hS Y' Z.1) :
    IsIso (conormalMap B S hS D.subspace Z D.f' D.reduction D.reduction_comm) :=
  (isFlat_and_isPullback_iff_isIso_conormalMap B S hS D.f' D.subspace Z D.reduction
    D.reduction_comm (D.isFirstOrderThickening_subspace hZ) hZ D.isFlat_reduction).1
    ⟨D.flat, D.isPullback_subspace⟩

/-- The identification `X ≅ X'_0` of the source with the closed fibre of the deformation. -/
def fibreIso : X ≅ (⟨D.subspace.1.toFunctor, D.subspace.2.1⟩ : AlgebraicSpaces B S hS) :=
  IsPullback.isoIsPullback _ _ D.isPullback D.isPullback_subspace

/-- The isomorphism `X ≅ X'_0` followed by the inclusion `X'_0 ⊂ X'` is `i : X ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem fibreIso_hom_inclusion :
    D.fibreIso.hom ≫ subspaceInclusion B S hS D.X' D.subspace = D.i :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `X ≅ X'_0` followed by `f'_0 : X'_0 ⟶ Y` is `f : X ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem fibreIso_hom_reduction : D.fibreIso.hom ≫ D.reduction = f :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The solution attached to a flat deformation**: the extension
`0 → 𝒞_{X'_0/X'} → 𝒪_{X'}|_{X'_0} → 𝒪_{X'_0} → 0` of the closed fibre, with its kernel identified
with `f'^*_0 𝒞_{Y/Y'}` along the conormal map, as a solution of the extension problem of `f'_0`. -/
def solution (hZ : IsFirstOrderThickening B S hS Y' Z.1) :
    (problem D.reduction hZ).CompatibleFirstOrderThickening :=
  haveI := D.isIso_conormalMap hZ
  (problem D.reduction hZ).ofAlgebraExtension
    (squareBaseIso hZ D.subspace D.f' D.reduction D.reduction_comm)
    (squareBaseIso_hom_comp hZ D.subspace D.f' D.reduction D.reduction_comm)
    ((firstOrderAlgebraExtension B S hS D.subspace (D.isFirstOrderThickening_subspace hZ)
      D.f').transportKernel
        (asIso (conormalMap B S hS D.subspace Z D.f' D.reduction D.reduction_comm)).symm)
    (isCompatible_transportKernel hZ D.subspace (D.isFirstOrderThickening_subspace hZ) D.f'
      D.reduction D.reduction_comm)

end AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation

end
