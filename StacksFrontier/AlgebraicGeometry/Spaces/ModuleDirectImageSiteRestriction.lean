module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# The direct image of modules along a representable morphism is restriction of sections

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`.  The direct image of `𝒪_Y`-modules of Stacks 03D1,
`AlgebraicGeometry.Space.moduleDirectImage`, is defined through the comparison equivalences of
Stacks 03G1 and is a module over `𝒜 = f_*𝒪_Y`.  For a representable morphism base change of
étale charts `V ↦ V ×_X Y` is a continuous functor of small étale sites, and restriction along it
is another direct image, over the restricted structure sheaf `u_*𝒪_Y`.  This file identifies the
two: there is an isomorphism of sheaves of rings `𝒜 ≅ u_*𝒪_Y`
(`AlgebraicGeometry.Space.directImageRingIso`), and through the induced equivalence of categories
of modules the direct image of Stacks 03D1 *is* restriction along base change
(`AlgebraicGeometry.Space.moduleDirectImageIsoSiteDirectImage`).

## Main definitions

* `AlgebraicGeometry.Space.siteDirectImageRing`: the restriction `u_*𝒪_Y` of the structure sheaf.
* `AlgebraicGeometry.Space.siteDirectImage`: restriction of `𝒪_Y`-modules along base change.
* `AlgebraicGeometry.Space.directImageRingIso`: `𝒜 ≅ u_*𝒪_Y`.
* `AlgebraicGeometry.Space.directImageRingEquivalence`: the induced equivalence of the categories
  of modules, whose functor is restriction of scalars.
* `AlgebraicGeometry.Space.moduleDirectImageIsoSiteDirectImage`: `f_* ≅ siteDirectImage ⋙ E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)

attribute [local instance] isContinuous_smallBaseChange

/-- The restriction `u_*𝒪_Y` of the structure sheaf of `Y` along base change of charts. -/
abbrev siteDirectImageRing : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  ((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).obj
      (structureRingSheaf B S hS Y)

/-- Restriction of `𝒪_Y`-modules along base change of charts. -/
abbrev siteDirectImage :
    SheafOfModules.{u} (structureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (siteDirectImageRing B S hS f hf) :=
  SheafOfModules.pushforward (𝟙 _)

/-- The comparison of the two inverse images of the structure sheaf of `Y`. -/
def directImageRingMap :
    structureRingSheafDirectImage B S hS f ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
        ((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1))
        (structureRingSheaf B S hS Y) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS Y)
    (smallEtaleDirectImageIsoSheafPushforward B S hS f hf).hom

/-- The comparison `directImageRingMap` is an isomorphism: after forgetting to sheaves of types
it is the isomorphism `smallEtaleDirectImageIsoSheafPushforward`. -/
instance isIso_directImageRingMap : IsIso (directImageRingMap B S hS f hf) := by
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (directImageRingMap B S hS f hf)) := by
    rw [directImageRingMap, ringSheafMap_pullbackRingSheafMapOfNatTrans]
    exact (smallEtaleDirectImageIsoSheafPushforward B S hS f hf).app _ |>.isIso_hom
  exact isIso_of_reflects_iso _ (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u}))

/-- **The direct-image algebra of a representable morphism is the restricted structure sheaf**:
`f_*𝒪_Y ≅ u_*𝒪_Y`. -/
def directImageRingIso :
    structureRingSheafDirectImage B S hS f ≅ siteDirectImageRing B S hS f hf :=
  asIso (directImageRingMap B S hS f hf) ≪≫
    restrictionRingIso (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (smallBaseChange B S hS f hf) (structureRingSheaf B S hS Y)

/-- The equivalence of categories of modules induced by `directImageRingIso`; its functor is
restriction of scalars along it. -/
def directImageRingEquivalence :
    SheafOfModules.{u} (siteDirectImageRing B S hS f hf) ≌
      SheafOfModules.{u} (structureRingSheafDirectImage B S hS f) :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (restrictionRingIso (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
        (smallBaseChange B S hS f hf) (structureRingSheaf B S hS Y)).symm).trans
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (asIso (directImageRingMap B S hS f hf)).symm)

/-- **The direct image of Stacks 03D1 along a representable morphism is restriction along base
change of charts**, read through `directImageRingEquivalence`. -/
def moduleDirectImageIsoSiteDirectImage :
    moduleDirectImage B S hS f ≅
      siteDirectImage B S hS f hf ⋙ (directImageRingEquivalence B S hS f hf).functor :=
  pullbackModuleFunctorIsoOfNatIso (SmallEtale.topology B S hS X.1)
      (structureRingSheaf B S hS Y) (smallEtaleDirectImageIsoSheafPushforward B S hS f hf)
      (directImageRingMap B S hS f hf)
      (ringSheafMap_pullbackRingSheafMapOfNatTrans.{u, u, u, u + 1, u, u + 1} _ _ _) ≪≫
    Functor.isoWhiskerRight
      (restrictionModuleIso (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
        (smallBaseChange B S hS f hf) (structureRingSheaf B S hS Y)) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Space
