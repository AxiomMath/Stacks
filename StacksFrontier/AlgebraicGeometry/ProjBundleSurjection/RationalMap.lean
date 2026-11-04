module

public import StacksFrontier.AlgebraicGeometry.Morphism.Glue
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Functoriality

/-!
# The rational map of projective bundles attached to a morphism of modules

Let `u : E₁ ⟶ E₂` be a morphism of quasi-coherent modules on a scheme `X`. Applying `Sym` and
the relative homogeneous spectrum gives the **rational map of projective bundles**

`𝐏(E₂) ⊇ U(u) --r_u--> 𝐏(E₁)`

over `X`, defined on the open subscheme of `𝐏(E₂)` where `Sym(u)` induces a morphism. No
surjectivity is assumed: this is Tag 07ZG applied to the functoriality of the sheafified
symmetric algebra, and it is the general construction of which Tag 0B2W's universal family of
projective transformations is an instance.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebraHom`: `Sym(u)`, as a homomorphism of
  the sheaf-level graded `𝒪_X`-algebras.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleMapDomain`: the open `U(u) ⊆ 𝐏(E₂)`.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleRationalMap`: the morphism
  `r_u : U(u) ⟶ 𝐏(E₁)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleRationalMap_comp_toBase`: **it is a
  morphism over the base**, so it is a family of maps of the fibres.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.chartImage_le_bundleMapDomain` and
  `Stacks.AlgebraicGeometry.ProjBundleSurjection.homOfLE_comp_bundleRationalMap`: over an affine
  open of the base it is the absolute morphism of Tag 01MY for the graded ring homomorphism
  `Sym(u)` induces on homogeneous sections.

## Implementation notes

Both the open and the morphism are Tag 07ZG's, with
`Stacks.SymGraded.schemeSheafGradedAlgebraHom` supplying the homomorphism of graded algebras;
the quasi-coherence of the homogeneous pieces is discharged by
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.SymGraded

namespace Stacks.AlgebraicGeometry.ProjBundleSurjection

universe u

variable {X : Scheme.{u}} {E₁ E₂ : X.Modules} [E₁.IsQuasicoherent] [E₂.IsQuasicoherent]

/-- **`Sym(u)`**, the homomorphism of sheaf-level graded `𝒪_X`-algebras induced by a morphism of
quasi-coherent modules. -/
public def symAlgebraHom (u : E₁ ⟶ E₂) : SheafGradedAlgebraHom (symAlgebra E₁) (symAlgebra E₂) :=
  schemeSheafGradedAlgebraHom u (isQuasicoherentPieces_of_isQuasicoherent E₁)
    (isQuasicoherentPieces_of_isQuasicoherent E₂)

/-- **The open `U(u) ⊆ 𝐏(E₂)`** on which a morphism of quasi-coherent modules induces a morphism
of projective bundles: Tag 07ZG's open for `Sym(u)`. -/
public def bundleMapDomain (u : E₁ ⟶ E₂) :
    (schemeProjectiveBundle E₂ (isQuasicoherentPieces_of_isQuasicoherent E₂)).scheme.Opens :=
  (symAlgebraHom u).relativeMapDomain

/-- **The rational map of projective bundles `r_u : 𝐏(E₂) ⊇ U(u) ⟶ 𝐏(E₁)`** attached to a
morphism `u : E₁ ⟶ E₂` of quasi-coherent modules, with no surjectivity assumed. -/
public def bundleRationalMap (u : E₁ ⟶ E₂) :
    (bundleMapDomain u).toScheme ⟶
      (schemeProjectiveBundle E₁ (isQuasicoherentPieces_of_isQuasicoherent E₁)).scheme :=
  Tag07ZGMorphism.relativeMapHom (symAlgebraHom u)

/-- **The rational map of projective bundles is a morphism over the base.** -/
@[reassoc]
public theorem bundleRationalMap_comp_toBase (u : E₁ ⟶ E₂) :
    bundleRationalMap u ≫
        schemeProjectiveBundleToBase E₁ (isQuasicoherentPieces_of_isQuasicoherent E₁) =
      (bundleMapDomain u).ι ≫
        schemeProjectiveBundleToBase E₂ (isQuasicoherentPieces_of_isQuasicoherent E₂) :=
  Tag07ZGMorphism.relativeMapHom_comp_toBase (symAlgebraHom u)

/-- The chart image of the chart domain over an affine open of the base lies in `U(u)`. -/
public theorem chartImage_le_bundleMapDomain (u : E₁ ⟶ E₂) (U : AffineOpen X) :
    Tag07ZGMorphism.chartImage (symAlgebraHom u) U ≤ bundleMapDomain u :=
  Tag07ZGMorphism.chartImage_le (symAlgebraHom u) U

/-- **The defining equation of the rational map**: on the piece over an affine open of the base
it is the local morphism Tag 01MY attaches to the graded ring homomorphism of homogeneous
sections. -/
public theorem homOfLE_comp_bundleRationalMap (u : E₁ ⟶ E₂) (U : AffineOpen X) :
    (schemeProjectiveBundle E₂
            (isQuasicoherentPieces_of_isQuasicoherent E₂)).scheme.homOfLE
          (chartImage_le_bundleMapDomain u U) ≫ bundleRationalMap u =
      Tag07ZGMorphism.localHom (symAlgebraHom u) U :=
  Tag07ZGMorphism.homOfLE_comp_relativeMapHom (symAlgebraHom u) U

end Stacks.AlgebraicGeometry.ProjBundleSurjection

end
