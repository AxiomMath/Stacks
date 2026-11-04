module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.PolarizedSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Polarized families of schemes with the polarization on the small étale site

An object of `AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` is a polarized family
of Stacks 0D1M whose base `V` and total space `Z` are objects of the big fppf site over
`Spec(ℤ)`, with its polarization given as a quasi-coherent `𝒪`-module `M` on the small étale
site of the representable algebraic space `yoneda Z`; the polarization on the scheme `Z` is its
restriction `R(M)` to the Zariski site (`AlgebraicGeometry.Space.representedZariskiModule`).
Morphisms are cartesian squares together with an isomorphism `M ≅ h^*M'` of the inverse image of
Stacks 03LU.

This is the category in which the line bundles of Stacks 0E94 are descended, since descent of
quasi-coherent modules on algebraic spaces (Stacks 04W8) is stated on small étale sites.
Comparing it with `AlgebraicGeometry.PolarizedFamily` through `R` is
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedOverSpace/RepresentedPolarizedComparison.lean`.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.arrowModules`: the pseudofunctor `(s : Z ⟶ V) ↦
  Modules(𝒪_{yoneda Z})` on the arrows of the site.
* `AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` and its projection
  `AlgebraicGeometry.PolarizedOverSpace.representedPolarizedProjection` to the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

variable (B : BigFppfSite.{u})

/-- The site over `Spec(ℤ)`. -/
abbrev Site := BigFppfOver B integerBase (hZ B)

/-- The underlying morphism of schemes of a morphism of the site. -/
abbrev sch {U V : Site B} (f : U ⟶ V) :
    (BigFppfOver.toScheme B integerBase (hZ B)).obj U ⟶
      (BigFppfOver.toScheme B integerBase (hZ B)).obj V :=
  (BigFppfOver.toScheme B integerBase (hZ B)).map f

/-- The total space of an arrow of the site, as an algebraic space. -/
abbrev arrowSpace : Arrow (Site B) ⥤ AlgebraicSpaces B integerBase (hZ B) :=
  Arrow.leftFunc ⋙ schemeSpaceFunctor B integerBase (hZ B)

/-- The modules on the total spaces of the arrows of the site, with their inverse images. -/
abbrev arrowModules : Pseudofunctor (LocallyDiscrete (Arrow (Site B))ᵒᵖ) Cat :=
  (arrowSpace B).op.toPseudofunctor.comp (Space.modulesPseudofunctor B integerBase (hZ B))

/-- The polarization on the scheme `Z` of a module on the small étale site of `yoneda Z`: its
restriction to the Zariski site. -/
abbrev zariskiPolarization (X : Pseudofunctor.CoGrothendieck (arrowModules B)) :
    ((BigFppfOver.toScheme B integerBase (hZ B)).obj X.base.left).Modules :=
  Space.representedZariskiModule B integerBase (hZ B) X.base.left X.fiber

/-- The conditions on an object: the structure morphism is proper, flat and of finite
presentation, the module is quasi-coherent, and its Zariski restriction is invertible and
relatively ample. -/
structure IsRepresentedPolarized (X : Pseudofunctor.CoGrothendieck (arrowModules B)) : Prop where
  proper : IsProper (sch B X.base.hom)
  flat : Flat (sch B X.base.hom)
  finitePresentation : FinitePresentation (sch B X.base.hom)
  quasicoherent : SheafOfModules.IsQuasicoherentOnSite X.fiber
  invertible : SheafOfModules.IsInvertible
    ((BigFppfOver.toScheme B integerBase (hZ B)).obj X.base.left).presheaf
    ((BigFppfOver.toScheme B integerBase (hZ B)).obj X.base.left).ringCatSheaf.2
    (zariskiPolarization B X)
  relativelyAmple :
    letI := invertible
    Stacks.RelativeAmple.IsRelativelyAmple (sch B X.base.hom) (zariskiPolarization B X)

/-- The objects of `RepresentedPolarized`. -/
abbrev RepresentedPolarizedObj := ObjectProperty.FullSubcategory (IsRepresentedPolarized B)

/-- The morphisms of `RepresentedPolarized`: cartesian squares with an invertible comparison of
modules. -/
def cartesianIso : MorphismProperty (RepresentedPolarizedObj B) := fun X Y f =>
  IsPullback (sch B f.hom.base.left) (sch B X.obj.base.hom) (sch B Y.obj.base.hom)
    (sch B f.hom.base.right) ∧ IsIso f.hom.fiber

/-- The class `cartesianIso B` contains the identities and is closed under composition. -/
instance : (cartesianIso B).IsMultiplicative where
  id_mem X := by
    refine ⟨?_, ?_⟩
    · simpa using IsPullback.id_horiz (sch B X.obj.base.hom)
    · change IsIso (((arrowModules B).mapId ⟨Opposite.op X.obj.base⟩).inv.toNatTrans.app
        X.obj.fiber)
      infer_instance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨?_, ?_⟩
    · have h := hf.1.paste_horiz hg.1
      simpa [Functor.map_comp] using h
    · have := hf.2
      have := hg.2
      change IsIso (f.hom.fiber ≫
        ((arrowModules B).map f.hom.base.op.toLoc).toFunctor.map g.hom.fiber ≫
          ((arrowModules B).mapComp g.hom.base.op.toLoc f.hom.base.op.toLoc).inv.toNatTrans.app
            Z.obj.fiber)
      infer_instance

/-- **Polarized families of schemes of the site with their polarization on the small étale
site.** -/
abbrev RepresentedPolarized := WideSubcategory (cartesianIso B)

/-- The projection to the site: the base of the family. -/
abbrev representedPolarizedProjection : RepresentedPolarized B ⥤ Site B :=
  wideSubcategoryInclusion _ ⋙ ObjectProperty.ι _ ⋙
    Pseudofunctor.CoGrothendieck.forget (arrowModules B) ⋙ Arrow.rightFunc

end AlgebraicGeometry.PolarizedOverSpace

end
