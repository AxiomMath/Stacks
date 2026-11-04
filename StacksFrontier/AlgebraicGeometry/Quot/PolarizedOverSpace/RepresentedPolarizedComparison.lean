module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarized
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget

/-!
# From space-level polarized families to polarized families of schemes

The comparison `RepresentedPolarized ⟶ Polarized` restricts the polarization of an object of
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` to the Zariski site
(`AlgebraicGeometry.Space.representedZariskiModule`), and the comparison of a morphism is
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso` followed by the restriction of the
inverse of the comparison of modules.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.toPolarizedObj` and
  `AlgebraicGeometry.PolarizedOverSpace.toPolarizedMap`: the object and morphism assignments.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

variable (B : BigFppfSite.{u})

/-- The polarized family of schemes of an object of `RepresentedPolarized`. -/
def toPolarizedObj (X : RepresentedPolarized B) : PolarizedFamily B where
  base := (BigFppfOver.forget B integerBase (hZ B)).obj X.obj.obj.base.right
  total := (BigFppfOver.toScheme B integerBase (hZ B)).obj X.obj.obj.base.left
  toBase := sch B X.obj.obj.base.hom
  proper := X.obj.property.proper
  flat := X.obj.property.flat
  finitePresentation := X.obj.property.finitePresentation
  lineBundle := zariskiPolarization B X.obj.obj
  invertible := X.obj.property.invertible
  relativelyAmple := X.obj.property.relativelyAmple

/-- The comparison of polarizations of a morphism of `RepresentedPolarized`. -/
def toPolarizedLineBundleIso {X Y : RepresentedPolarized B} (f : X ⟶ Y) :
    (Scheme.Modules.pullback (sch B f.hom.hom.base.left)).obj (zariskiPolarization B Y.obj.obj) ≅
      zariskiPolarization B X.obj.obj :=
  haveI := f.property.2
  Space.representedZariskiModulePullbackIso B integerBase (hZ B) f.hom.hom.base.left
      (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) f.hom.hom.base.left)
      Y.obj.obj.fiber Y.obj.property.quasicoherent ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase (hZ B)).obj X.obj.obj.base.left)
        X.obj.obj.base.left.left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B)
        X.obj.obj.base.left).inverse.mapIso (asIso f.hom.hom.fiber).symm)

/-- The morphism of polarized families of schemes of a morphism of `RepresentedPolarized`. -/
def toPolarizedMap {X Y : RepresentedPolarized B} (f : X ⟶ Y) :
    toPolarizedObj B X ⟶ toPolarizedObj B Y where
  baseMap := (BigFppfOver.forget B integerBase (hZ B)).map f.hom.hom.base.right
  totalMap := sch B f.hom.hom.base.left
  cartesian := f.property.1
  lineBundleIso := toPolarizedLineBundleIso B f

end AlgebraicGeometry.PolarizedOverSpace

end
