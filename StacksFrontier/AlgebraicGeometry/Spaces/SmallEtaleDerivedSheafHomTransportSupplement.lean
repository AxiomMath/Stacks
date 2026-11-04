module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTransport
public import StacksFrontier.CategoryTheory.Adjunction.LeftTensorHomDiagonalTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import all StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTransport

/-!
# Sheafification on the ringed small étale site of an algebraic space

Sheafification of abelian presheaves, and the description of local isomorphisms as locally
bijective morphisms, on the equi-universe model of the small étale site of an algebraic space,
stated at the Grothendieck topology of `AlgebraicGeometry.Space.smallEtaleModelRingedSite`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModelRingedSite_hasSheafify`: abelian presheaves on the
  ringed small étale site have a sheafification.
* `AlgebraicGeometry.Space.smallEtaleModelRingedSite_wEqualsLocallyBijective`: the local
  isomorphisms of abelian presheaves on the ringed small étale site are the locally bijective
  morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

/- Sheafification on the small étale site comes from its small model
(`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`), not from the plus construction. -/

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Sheafification of abelian presheaves on the equi-universe model of the small étale site, as
an instance at the spelling of the ringed site, where instance search does not unfold
`AlgebraicGeometry.Space.smallEtaleModelRingedSite` to the small site of the model. -/
instance smallEtaleModelRingedSite_hasSheafify (X : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleModelRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (smallEtaleModelTopology B S hS X.1) AddCommGrpCat.{u})

/-- The local isomorphisms of abelian presheaves on the equi-universe model of the small étale
site are the locally bijective morphisms, at the spelling of the ringed site. -/
instance smallEtaleModelRingedSite_wEqualsLocallyBijective (X : AlgebraicSpaces B S hS) :
    (smallEtaleModelRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((smallEtaleModelTopology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})

end AlgebraicGeometry.Space

end
