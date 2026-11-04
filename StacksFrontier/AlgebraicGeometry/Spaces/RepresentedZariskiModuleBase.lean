module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback

/-!
# The module on the underlying scheme of the module attached to a quasi-coherent module there

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf
category over `S`. Consider the two passages between the quasi-coherent modules on the scheme `T`
underlying `U` and the quasi-coherent `𝒪`-modules on the small étale site of the representable
algebraic space `yoneda.obj U`:

* `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` is the equivalence
  `QCoh(𝒪_T) ≌ QCoh(𝒪_{yoneda.obj U})` composed with the comparison of the two small étale sites;
* `AlgebraicGeometry.Space.representedZariskiModule` carries an `𝒪`-module on the small étale
  site of `yoneda.obj U` to an `AlgebraicGeometry.Scheme.Modules` on `T`, by reading it on the
  small étale site of `T` and restricting to the small Zariski site.

The module on `T` of the module attached to a quasi-coherent module on `T` is that module.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso`: the isomorphism
  between the module on the scheme underlying `U` of the quasi-coherent module on the small étale
  site of `yoneda.obj U` attached to a quasi-coherent module on that scheme, and that module.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The module on the scheme underlying `U` of the quasi-coherent `𝒪`-module on the small étale
site of `yoneda.obj U` attached to a quasi-coherent module `M` on that scheme is isomorphic to
`M`. -/
public def representedZariskiModuleQuasicoherentSchemeIso
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    representedZariskiModule B S hS U
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≅ M.obj :=
  haveI := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property M
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS U).unitIso.app
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
          U.left.property).functor.obj M).obj).symm ≪≫
    (asIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property).unit.app M.obj)).symm

end AlgebraicGeometry.Space

end
