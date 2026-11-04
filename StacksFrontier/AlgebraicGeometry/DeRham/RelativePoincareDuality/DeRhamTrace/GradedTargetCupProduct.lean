module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetFactorIso
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPushforwardCompShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductComposition
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetChase

/-!
# The relative cup product along `f = π ∘ ι`

Let `f : X ⟶ S` be a morphism of schemes, factored on ringed spaces as `ι : X ⟶ (X, f⁻¹𝒪_S)`
followed by `π : (X, f⁻¹𝒪_S) ⟶ S`, and let `g` be a morphism of ringed spaces with `ι ≫ π = g`.
By [Stacks, Tag 0FP6] the relative cup product along `g` is the relative cup product along `π`
followed by `Rπ_*` of that along `ι`, through `Rg_* ≅ Rπ_* ∘ Rι_*`. This file applies it to
morphisms `a : K₁ ⟶ Rι_*K`, `b : L₁ ⟶ Rι_*L` into direct images along `ι` and to a pairing
`φ : K ⊗^L L ⟶ M`: the composite along `π` of the relative cup products of `a`, `b` and `Rι_*φ` is
the relative cup product along `g` of `Rπ_*a` and `Rπ_*b`, followed by `Rg_*φ`.

All declarations below lie in the namespace `AlgebraicGeometry.Scheme.Hom`.

## Main definitions

* `projectionPushforwardComparison`: the morphism `Rπ_*K₁ ⟶ Rg_*K` induced by `a : K₁ ⟶ Rι_*K`.

## Main results

* `relativeCupProduct_comp_inverseImageBaseFactorIso`: [Stacks, Tag 0FP6] for `g = π ∘ ι`.
* `relativeCupProduct_map_relativeCupProduct_projectionPushforwardComparison`: the compatibility
  of relative cup products along `π`, `ι` and `g` with the pairing `φ`.

## References

* [Stacks, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
* [Stacks, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel CategoryTheory.Prod
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase inverseImageBaseProjection)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward
    derivedPushforwardCompIso)
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct)

universe u


namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- [Stacks, Tag 0FP6] for `g = π ∘ ι`, through the factorization isomorphism
`Rg_* ≅ Rι_* ⋙ Rπ_*`. -/
theorem relativeCupProduct_comp_inverseImageBaseFactorIso (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (Functor.uncurry.obj (derivedTensorProductFunctor S.toRingedSpace.sheaf)).map
        ((inverseImageBaseFactorIso f g hg).inv.app K ×ₘ (inverseImageBaseFactorIso f g hg).inv.app
            L) ≫
        relativeCupProduct g K L =
      relativeCupProduct (inverseImageBaseProjection f)
          ((derivedPushforward (toInverseImageBase f)).obj K)
          ((derivedPushforward (toInverseImageBase f)).obj L) ≫
        (derivedPushforward (inverseImageBaseProjection f)).map
          (relativeCupProduct (toInverseImageBase f) K L) ≫
        (inverseImageBaseFactorIso f g hg).inv.app
            (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj K).obj L) := by
  subst hg
  simp only [inverseImageBaseFactorIso, eqToIso_refl, Iso.trans_refl, Iso.symm_inv]
  exact Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_comp' (toInverseImageBase f)
      (inverseImageBaseProjection f) K L

/-- The composite along `π` of the relative cup products of `a`, `b` and `Rι_*φ` is the relative
cup product along `g` of `Rπ_*a` and `Rπ_*b` (through `Rg_* ≅ Rι_* ⋙ Rπ_*`), followed by
`Rg_*φ`. -/
theorem relativeCupProduct_map_relativeCupProduct_toInverseImageBase
    (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g)
    {K₁ L₁ : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    {K L M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    (a : K₁ ⟶ (derivedPushforward (toInverseImageBase f)).obj K)
    (b : L₁ ⟶ (derivedPushforward (toInverseImageBase f)).obj L)
    (φ : ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj K).obj L ⟶ M)
    (z : (derivedPushforward (toInverseImageBase f)).obj M ⟶ N) :
    relativeCupProduct (inverseImageBaseProjection f) K₁ L₁ ≫
      (derivedPushforward (inverseImageBaseProjection f)).map
        (((((derivedTensorProductFunctor (inverseImageBase f).sheaf).map a).app L₁ ≫
          ((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            ((derivedPushforward (toInverseImageBase f)).obj K)).map b) ≫
          relativeCupProduct (toInverseImageBase f) K L) ≫
          (derivedPushforward (toInverseImageBase f)).map φ ≫ z) =
      ((derivedTensorProductFunctor S.toRingedSpace.sheaf).map
          ((derivedPushforward (inverseImageBaseProjection f)).map a ≫
            (inverseImageBaseFactorIso f g hg).inv.app K)).app
          ((derivedPushforward (inverseImageBaseProjection f)).obj L₁) ≫
        ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj ((derivedPushforward g).obj K)).map
          ((derivedPushforward (inverseImageBaseProjection f)).map b ≫
            (inverseImageBaseFactorIso f g hg).inv.app L) ≫
        relativeCupProduct g K L ≫ (derivedPushforward g).map φ ≫
        (inverseImageBaseFactorIso f g hg).hom.app M ≫
        (derivedPushforward (inverseImageBaseProjection f)).map z :=
  Stacks.GradedTargetChase.relativeCupProduct_chase (derivedTensorProductFunctor
      X.toSheafedSpace.sheaf)
    (derivedTensorProductFunctor (inverseImageBase f).sheaf)
    (derivedTensorProductFunctor S.toRingedSpace.sheaf)
    (derivedPushforward (toInverseImageBase f)) (derivedPushforward (inverseImageBaseProjection f))
    (derivedPushforward g)
    (relativeCupProduct (inverseImageBaseProjection f)) (relativeCupProduct (toInverseImageBase f))
    (relativeCupProduct g) (inverseImageBaseFactorIso f g hg).symm
    (fun k l => Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural
      (inverseImageBaseProjection f) k l)
    (relativeCupProduct_comp_inverseImageBaseFactorIso f g hg) a b φ z

/-- The morphism `Rπ_*K₁ ⟶ Rg_*K` induced by `a : K₁ ⟶ Rι_*K` and the factorization
`Rg_* ≅ Rι_* ⋙ Rπ_*`. -/
def projectionPushforwardComparison (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g)
    {K₁ : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (a : K₁ ⟶ (derivedPushforward (toInverseImageBase f)).obj K) :
    (derivedPushforward (inverseImageBaseProjection f)).obj K₁ ⟶ (derivedPushforward g).obj K :=
  (derivedPushforward (inverseImageBaseProjection f)).map a ≫ (inverseImageBaseFactorIso f g
      hg).inv.app K

/-- The morphism induced by an isomorphism is an isomorphism. -/
instance isIso_projectionPushforwardComparison (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g)
    {K₁ : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (a : K₁ ⟶ (derivedPushforward (toInverseImageBase f)).obj K) [ha : IsIso a] :
    IsIso (projectionPushforwardComparison f g hg a) := by
  unfold projectionPushforwardComparison; infer_instance

/-- `relativeCupProduct_map_relativeCupProduct_toInverseImageBase` with the morphisms induced by
`a` and `b` named by `projectionPushforwardComparison`. -/
theorem relativeCupProduct_map_relativeCupProduct_projectionPushforwardComparison
    (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g)
    {K₁ L₁ : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    {K L M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    (a : K₁ ⟶ (derivedPushforward (toInverseImageBase f)).obj K)
    (b : L₁ ⟶ (derivedPushforward (toInverseImageBase f)).obj L)
    (φ : ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj K).obj L ⟶ M)
    (z : (derivedPushforward (toInverseImageBase f)).obj M ⟶ N) :
    relativeCupProduct (inverseImageBaseProjection f) K₁ L₁ ≫
      (derivedPushforward (inverseImageBaseProjection f)).map
        (((((derivedTensorProductFunctor (inverseImageBase f).sheaf).map a).app L₁ ≫
          ((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            ((derivedPushforward (toInverseImageBase f)).obj K)).map b) ≫
          relativeCupProduct (toInverseImageBase f) K L) ≫
          (derivedPushforward (toInverseImageBase f)).map φ ≫ z) =
      ((derivedTensorProductFunctor S.toRingedSpace.sheaf).map
          (projectionPushforwardComparison f g hg a)).app
          ((derivedPushforward (inverseImageBaseProjection f)).obj L₁) ≫
        ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj ((derivedPushforward g).obj K)).map
          (projectionPushforwardComparison f g hg b) ≫
        relativeCupProduct g K L ≫ (derivedPushforward g).map φ ≫
        (inverseImageBaseFactorIso f g hg).hom.app M ≫
        (derivedPushforward (inverseImageBaseProjection f)).map z :=
  relativeCupProduct_map_relativeCupProduct_toInverseImageBase f g hg a b φ z

end AlgebraicGeometry.Scheme.Hom
