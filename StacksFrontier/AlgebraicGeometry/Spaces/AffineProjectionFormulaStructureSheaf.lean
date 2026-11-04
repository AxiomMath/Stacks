module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraExtendScalarsTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula `f_*f^*𝒢 ≅ f_*𝒪_X ⊗ 𝒢` for an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` and let `𝒢` be a
quasi-coherent `𝒪_Y`-module.  The direct image of the pullback of `𝒢` is the tensor product of
`𝒢` with the direct image `f_*𝒪_X` of the structure sheaf:

`f_*f^*𝒢 ≅ f_*𝒪_X ⊗_{𝒪_Y} 𝒢`.

This is the special case `ℱ = 𝒪_X` of the projection formula for an affine morphism.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardPullbackIsoRestrictExtendScalars`: `f_*f^*𝒢` is the
  extension of scalars of `𝒢` along `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, read back as an `𝒪_Y`-module.
* `AlgebraicGeometry.Space.modulePushforwardPullbackIsoSheafTensor`: the projection formula, with
  the tensor product of Stacks 01CA on the small étale site of `Y`.

## Implementation notes

No computation on charts is needed.  The pullback `f^*` factors, up to isomorphism, as extension
of scalars along `f♯` followed by the quasi-inverse `L` of Stacks 08AI, because both are left
adjoints of `f_*` (`AlgebraicGeometry.Space.directImageAlgebraPullbackExtendScalarsIso`).  For an
affine `f` and a quasi-coherent module over `f_*𝒪_X` the unit of `L ⊣ f_*` is invertible
(`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom`), so
`f_*f^*𝒢` is the extension of scalars of `𝒢`; read back over `𝒪_Y`, that is the tensor product by
`f_*𝒪_X` (`AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`).

## References

* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The direct image of a pullback along an affine morphism is an extension of scalars.**  For
an affine `f : X ⟶ Y` and a quasi-coherent `𝒪_Y`-module `𝒢`, the module `f_*f^*𝒢` is the
extension of scalars of `𝒢` along `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, read back as an `𝒪_Y`-module.

The pullback is extension of scalars followed by the quasi-inverse of Stacks 08AI, and the unit
of that quasi-inverse is invertible at the quasi-coherent extension of scalars of `𝒢`. -/
def modulePushforwardPullbackIsoRestrictExtendScalars (hf : IsAffineHom B S hS f.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite) :
    (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj G) ≅
      (directImageAlgebraRestrictScalars B S hS f).obj
        ((directImageAlgebraExtendScalars B S hS f).obj G) :=
  (modulePushforward B S hS f).mapIso
      ((directImageAlgebraPullbackExtendScalarsIso B S hS f).app G).symm ≪≫
    (directImageAlgebraRestrictScalars B S hS f).mapIso
      (haveI := isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom B S hS f hf
        ((directImageAlgebraExtendScalars B S hS f).obj G)
        ((isQuasicoherentOnSite_restrictScalars_structureSharp_iff B S hS f hf _).1
          (extendScalarsPreservesQuasicoherence B S hS f hf G hG))
      (asIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app
        ((directImageAlgebraExtendScalars B S hS f).obj G))).symm)

/-- **The projection formula for the structure sheaf along an affine morphism.**  For an affine
`f : X ⟶ Y` and a quasi-coherent `𝒪_Y`-module `𝒢`,

`f_*f^*𝒢 ≅ f_*𝒪_X ⊗_{𝒪_Y} 𝒢`,

the tensor product being the tensor product sheaf of Stacks 01CA on the small étale site of
`Y`. -/
@[sga "3 VIB 11.1" "more general"]
def modulePushforwardPullbackIsoSheafTensor (hf : IsAffineHom B S hS f.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite) :
    (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS Y.1 Y.2)).obj (pushforwardStructureModule B S hS f)).obj G :=
  modulePushforwardPullbackIsoRestrictExtendScalars B S hS f hf G hG ≪≫
    restrictScalarsExtendScalarsIsoTensorModule B S hS f G ≪≫
    tensorModuleIso B S hS Y.1 Y.2 _ G ≪≫
    modulesTensorObjIso B S hS Y.1 Y.2 _ G

end AlgebraicGeometry.Space
