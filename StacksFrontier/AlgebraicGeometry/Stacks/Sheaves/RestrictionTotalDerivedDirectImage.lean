module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictionDerivedDirectImageAbelian
public import StacksFrontier.CategoryTheory.Functor.KanExtension.PointwiseExistence
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The restricted total derived direct image

Let `S` be a scheme in a big fppf site and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_{fppf}`, with `𝒳` representable by an algebraic space `F` and `𝒴` by an
algebraic space `G`, and write `f : F ⟶ G` for the induced morphism of algebraic spaces. Stacks
075N asserts that

`(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})`

(1) in `D(G_étale)` for an abelian sheaf `ℱ` on `𝒳_étale`, and (2) in `D(𝒪_G)` for a sheaf of
`𝒪_𝒳`-modules `ℱ`.

The four total right derived direct images in this display exist. Every site in it is
essentially small: the small étale site of an algebraic space always, and `𝒳`, `𝒴` because they
are representable (`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver`). So abelian
sheaves and sheaves of modules on them form Grothendieck abelian categories, every complex in
them has a K-injective resolution (Stacks 079P,
`Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian`), and by Stacks 070K
every functor out of their homotopy categories has a total right derived functor. The derived
direct images below are the repository's total right derived functors of degreewise direct image,
`Stacks.DerivedFunctor.totalRightDerived` for abelian sheaves and
`Stacks.Cohomology.DerivedPushforward.derivedPushforward` for sheaves of modules, and the two
clauses of Stacks 075N are the comparison isomorphisms
`AlgebraicGeometry.Space.restrictedAbelianDerivedDirectImageIso` and
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso` evaluated at them. The right Kan
extension along `f` which the direct image of sheaves of sets along `f` needs exists for the same
reason, `𝒳` being essentially small and `𝒴` locally small
(`CategoryTheory.Functor.hasPointwiseRightKanExtension_of_essentiallySmall_of_locallySmall`).

## Main definitions

* `AlgebraicGeometry.Space.derivedAbelianDirectImageFibred` and
  `AlgebraicGeometry.Space.derivedDirectImageFibred`: the total right derived direct images
  `Rf_*` of abelian sheaves and of sheaves of modules along the 1-morphism `f : 𝒳 ⥤ 𝒴`.
* `AlgebraicGeometry.Space.derivedAbelianDirectImageSpace` and
  `AlgebraicGeometry.Space.derivedDirectImageSpace`: the total right derived direct images
  `Rf_{small,*}` of abelian sheaves and of sheaves of modules along the induced morphism of
  algebraic spaces.
* `AlgebraicGeometry.Space.derivedModuleRestriction`: the restriction `(-)|_{F_étale}` on derived
  categories of modules.
* `AlgebraicGeometry.Space.restrictedAbelianTotalDerivedDirectImageIso` and
  `AlgebraicGeometry.Space.restrictedTotalDerivedDirectImageIso`: clauses (1) and (2) of Stacks
  075N for these derived direct images.
* `AlgebraicGeometry.Space.restrictedTotalDerivedDirectImageIsoClauses`: **Stacks 075N**, both
  clauses, with nothing beyond the source's data.

## Main results

* `AlgebraicGeometry.Space.isGrothendieckAbelian_fibredSite_addCommGrpCat` and
  `AlgebraicGeometry.Space.isGrothendieckAbelian_fibredSite_modules`: abelian sheaves and sheaves
  of modules on the site inherited by an essentially small category fibred in groupoids form
  Grothendieck abelian categories; `AlgebraicGeometry.Space.hasSheafify_fibredSite_addCommGrpCat`,
  and `AlgebraicGeometry.Space.wEqualsLocallyBijective_fibredSite_addCommGrpCat` are the
  sheafification instances this rests on.
* `AlgebraicGeometry.Space.isGrothendieckAbelian_smallEtaleRingedTopos_addCommGrpCat` and
  `AlgebraicGeometry.Space.isGrothendieckAbelian_smallEtaleRingedTopos_modules`: the same on the
  small étale site of an algebraic space.

## Implementation notes

The essential smallness of `𝒳` and `𝒴` is a consequence of the presentations `eF`, `eG`, which are
data, so it cannot be found by instance search. In `restrictedTotalDerivedDirectImageIsoClauses`
it is therefore introduced by `letI` from the presentations, and the instances above derive from
it everything the statement needs; the clause-level declarations take it as an instance argument
instead, so that they can be used at any essentially small `𝒳`, `𝒴`.

Every derived category is taken in an arbitrary model, `[HasDerivedCategory C]`. In
`restrictedTotalDerivedDirectImageIsoClauses` the models of the derived categories of the two
sites `𝒳`, `𝒴` are instance arguments whose types are formed under the same `letI`, because the
abelian structure of a category of sheaves on `𝒳` is the one given by sheafification on the
essentially small site.

## References

* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

universe u v w v' w' dX dY dF dG mX mY mF mG

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Cohomology.UnboundedComplexes Stacks.Topos.AbelianPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  Functor.hasPointwiseRightKanExtension_of_essentiallySmall_of_locallySmall

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (fStack : 𝒳 ⥤ 𝒴) (hfStack : p.IsFibredOneMorphism q fStack)

/-! ### Sheafification and Grothendieck abelianness on the two kinds of site -/

section FibredSite

variable [EssentiallySmall.{u} 𝒳] (τ : SiteKind)

/-- Abelian sheaves on the site inherited by an essentially small category fibred in groupoids
have a sheafification. -/
instance hasSheafify_fibredSite_addCommGrpCat :
    HasSheafify (FibredSite.associatedRingedTopos B S hS p hp τ).J AddCommGrpCat.{u} :=
  haveI : EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS p hp τ).C :=
    ‹EssentiallySmall.{u} 𝒳›
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _

/-- On the site inherited by an essentially small category fibred in groupoids, a morphism of
presheaves of abelian groups becomes invertible after sheafification exactly when it is locally
bijective. -/
instance wEqualsLocallyBijective_fibredSite_addCommGrpCat :
    (FibredSite.associatedRingedTopos B S hS p hp τ).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  haveI : EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS p hp τ).C :=
    ‹EssentiallySmall.{u} 𝒳›
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _

/-- Abelian sheaves on the site inherited by an essentially small category fibred in groupoids
form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_fibredSite_addCommGrpCat :
    IsGrothendieckAbelian.{u}
      (Sheaf (FibredSite.associatedRingedTopos B S hS p hp τ).J AddCommGrpCat.{u}) :=
  haveI : EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS p hp τ).C :=
    ‹EssentiallySmall.{u} 𝒳›
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Sheaves of modules over the structure sheaf of the site inherited by an essentially small
category fibred in groupoids form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_fibredSite_modules :
    IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS p hp τ).Modules :=
  haveI : EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS p hp τ).C :=
    ‹EssentiallySmall.{u} 𝒳›
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall.{u} _

end FibredSite

section SmallEtale

/-- Abelian sheaves on the small étale site of an algebraic space form a Grothendieck abelian
category. -/
instance isGrothendieckAbelian_smallEtaleRingedTopos_addCommGrpCat :
    IsGrothendieckAbelian.{u}
      (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}) :=
  haveI : EssentiallySmall.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Sheaves of `𝒪`-modules on the small étale site of an algebraic space form a Grothendieck
abelian category. -/
instance isGrothendieckAbelian_smallEtaleRingedTopos_modules :
    IsGrothendieckAbelian.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules :=
  haveI : EssentiallySmall.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall.{u} _

end SmallEtale

/-! ### The four total right derived direct images -/

section DerivedDirectImages

variable
  [HasDerivedCategory.{dF} (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dG} (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{mF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  [HasDerivedCategory.{mG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]

/-- **`Rf_{small,*}` on abelian sheaves**: the total right derived functor
`Stacks.DerivedFunctor.totalRightDerived` of degreewise direct image of abelian sheaves along the
morphism of algebraic spaces `F ⟶ G` induced by `f`. -/
abbrev derivedAbelianDirectImageSpace :
    DerivedCategory (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}) :=
  Stacks.DerivedFunctor.totalRightDerived
    (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack)

/-- The unit of `derivedAbelianDirectImageSpace`, exhibiting it as a right derived functor. -/
abbrev derivedAbelianDirectImageSpaceUnit :
    mapToDerivedCategory (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack) ⟶
      DerivedCategory.Qh ⋙
        derivedAbelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack :=
  (mapToDerivedCategory
    (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- **`Rf_{small,*}` on sheaves of modules**: the total right derived functor of degreewise
direct image `AlgebraicGeometry.RingedToposHom.pushforwardToDerivedCategory` of sheaves of
modules along the morphism of algebraic spaces `F ⟶ G` induced by `f`. -/
abbrev derivedDirectImageSpace :
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules ⥤
      DerivedCategory (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules :=
  (smallEtaleRingedToposHom B S hS (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack
    hfStack)).pushforwardToDerivedCategory.totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules
        (ComplexShape.up ℤ))

/-- The unit of `derivedDirectImageSpace`, exhibiting it as a right derived functor. -/
abbrev derivedDirectImageSpaceUnit :
    (smallEtaleRingedToposHom B S hS (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack
        hfStack)).pushforwardToDerivedCategory ⟶
      DerivedCategory.Qh ⋙ derivedDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack :=
  (smallEtaleRingedToposHom B S hS (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack
    hfStack)).pushforwardToDerivedCategory.totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules
        (ComplexShape.up ℤ))

variable [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]
  [HasDerivedCategory.{dX}
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY}
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [HasDerivedCategory.{mY} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]

/-- **`Rf_*` on abelian sheaves**: the total right derived functor
`Stacks.DerivedFunctor.totalRightDerived` of degreewise direct image of abelian sheaves along the
1-morphism `f : 𝒳 ⥤ 𝒴`, for essentially small `𝒳` and `𝒴`. -/
abbrev derivedAbelianDirectImageFibred :
    DerivedCategory (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J
        AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J
        AddCommGrpCat.{u}) :=
  Stacks.DerivedFunctor.totalRightDerived
    (abelianDirectImageFibred B S hS p q hp hq fStack hfStack)

/-- The unit of `derivedAbelianDirectImageFibred`, exhibiting it as a right derived functor. -/
abbrev derivedAbelianDirectImageFibredUnit :
    mapToDerivedCategory (abelianDirectImageFibred B S hS p q hp hq fStack hfStack) ⟶
      DerivedCategory.Qh ⋙ derivedAbelianDirectImageFibred B S hS p q hp hq fStack hfStack :=
  (mapToDerivedCategory
    (abelianDirectImageFibred B S hS p q hp hq fStack hfStack)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- **`Rf_*` on sheaves of modules**: the total right derived functor of degreewise direct image
`AlgebraicGeometry.RingedToposHom.pushforwardToDerivedCategory` of sheaves of modules along the
1-morphism `f : 𝒳 ⥤ 𝒴`, for essentially small `𝒳` and `𝒴`. -/
abbrev derivedDirectImageFibred :
    DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules ⥤
      DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules :=
  (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack
    .etale).pushforwardToDerivedCategory.totalRightDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso
        (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))

/-- The unit of `derivedDirectImageFibred`, exhibiting it as a right derived functor. -/
abbrev derivedDirectImageFibredUnit :
    (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack
        .etale).pushforwardToDerivedCategory ⟶
      DerivedCategory.Qh ⋙ derivedDirectImageFibred B S hS p q hp hq fStack hfStack :=
  (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack
    .etale).pushforwardToDerivedCategory.totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso
        (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))

end DerivedDirectImages

/-- **The restriction `(-)|_{F_étale}` on derived categories of modules**: the functor
`D(𝒪_𝒳) ⥤ D(𝒪_F)` induced by the exact restriction of sheaves of modules to the small étale site
of `F`, `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact` of the morphism of ringed
topoi `π_F` of Stacks 073M. -/
abbrev derivedModuleRestriction {𝒵 : Type v} [Category.{w} 𝒵] (r : 𝒵 ⥤ BigFppfOver B S hS)
    (hr : r.IsFiberedInGroupoids) (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hH : IsAlgebraicSpace B S hS H)
    (eH : StacksRepresentableCFG.EquivalenceOver r (presheafOfCategories (H ⋙ typeToCat)).p)
    [EssentiallySmall.{u} 𝒵]
    [HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS r hr .etale).Modules]
    [HasDerivedCategory.{mF} (smallEtaleRingedTopos B S hS ⟨H, hH⟩).Modules] :
    DerivedCategory (FibredSite.associatedRingedTopos B S hS r hr .etale).Modules ⥤
      DerivedCategory (smallEtaleRingedTopos B S hS ⟨H, hH⟩).Modules :=
  RingedToposHom.derivedPushforwardOfExact
    (X := FibredSite.associatedRingedTopos B S hS r hr .etale)
    (Y := smallEtaleRingedTopos B S hS ⟨H, hH⟩) (projectionRingedToposHom B S hS H r hr hH eH)

/-! ### Stacks 075N -/

section Clauses

variable
  [HasDerivedCategory.{dF} (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dG} (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{mF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  [HasDerivedCategory.{mG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]
  [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]
  [HasDerivedCategory.{dX}
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY}
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [HasDerivedCategory.{mY} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]

/-- **Stacks 075N, clause (1), for the total right derived direct images**: for an abelian sheaf
`ℱ` on `𝒳_étale`, `(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})` in `D(G_étale)`, as an
isomorphism of functors; the restrictions are exact and appear underived. It is
`AlgebraicGeometry.Space.restrictedAbelianDerivedDirectImageIso` at
`derivedAbelianDirectImageFibred` and `derivedAbelianDirectImageSpace`. -/
def restrictedAbelianTotalDerivedDirectImageIso :
    derivedAbelianDirectImageFibred B S hS p q hp hq fStack hfStack ⋙
        (abelianRestrictionFunctor B S hS G q hq hG eG).mapDerivedCategory ≅
      (abelianRestrictionFunctor B S hS F p hp hF eF).mapDerivedCategory ⋙
        derivedAbelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack :=
  restrictedAbelianDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fStack hfStack
    (derivedAbelianDirectImageFibred B S hS p q hp hq fStack hfStack)
    (derivedAbelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack)
    (derivedAbelianDirectImageFibredUnit B S hS p q hp hq fStack hfStack)
    (derivedAbelianDirectImageSpaceUnit B S hS F G p q hF hG eF eG fStack hfStack)

/-- **Stacks 075N, clause (2), for the total right derived direct images**: for a complex `ℱ` of
`𝒪_𝒳`-modules, `(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})` in `D(𝒪_G)`, as an isomorphism
of functors; the restrictions are exact and appear underived. It is
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso` at `derivedDirectImageFibred` and
`derivedDirectImageSpace`. -/
def restrictedTotalDerivedDirectImageIso :
    derivedDirectImageFibred B S hS p q hp hq fStack hfStack ⋙
        derivedModuleRestriction B S hS q hq G hG eG ≅
      derivedModuleRestriction B S hS p hp F hF eF ⋙
        derivedDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack :=
  restrictedDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fStack hfStack
    (derivedDirectImageFibred B S hS p q hp hq fStack hfStack)
    (derivedDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack)
    (derivedDirectImageFibredUnit B S hS p q hp hq fStack hfStack)
    (derivedDirectImageSpaceUnit B S hS F G p q hF hG eF eG fStack hfStack)

end Clauses

/-- **Stacks 075N.** Let `S` be a scheme in a big fppf site, let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_{fppf}` with `𝒳` presented by an algebraic space `F`
and `𝒴` by an algebraic space `G`, and let `f : F ⟶ G` be the induced morphism of algebraic
spaces. Then

1. for an abelian sheaf `ℱ` on `𝒳_étale`, `(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})` in
   `D(G_étale)`;
2. for a complex `ℱ` of `𝒪_𝒳`-modules, the same identity in `D(𝒪_G)`.

Here `Rf_*` and `Rf_{small,*}` are the total right derived direct images
`derivedAbelianDirectImageFibred`, `derivedAbelianDirectImageSpace`, `derivedDirectImageFibred`
and `derivedDirectImageSpace`, which exist because the four sites are essentially small — `𝒳`
and `𝒴` by their presentations — so that K-injective resolutions exist (Stacks 079P). The
restrictions `(-)|_{F_étale}`, `(-)|_{G_étale}` are exact and appear underived, as in the source.
Each component is the canonical comparison of the two derived composites around the square of
Stacks 073N, shown invertible. -/
@[stacks 075N "Both clauses, with the four derived direct images constructed: (1) for abelian \
  sheaves (Rf_*F)|_{G_etale} = Rf_{small,*}(F|_{F_etale}) in D(G_etale), (2) the same identity in \
  D(O_G) for sheaves of modules. Rf_* and Rf_{small,*} are the total right derived functors of \
  degreewise direct image, which exist by K-injective resolutions (Tag 079P) on the four \
  essentially small sites; the only inputs are S, the 1-morphism and the two presentations."]
def restrictedTotalDerivedDirectImageIsoClauses
    [HasDerivedCategory.{dF} (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
    [HasDerivedCategory.{dG} (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u})]
    [HasDerivedCategory.{mF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
    [HasDerivedCategory.{mG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]
    [letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF;
      letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG;
      HasDerivedCategory.{dX}
        (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
    [letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF;
      letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG;
      HasDerivedCategory.{dY}
        (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
    [letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF;
      letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG;
      HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
    [letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF;
      letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG;
      HasDerivedCategory.{mY} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules] :
    letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF
    letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG
    (derivedAbelianDirectImageFibred B S hS p q hp hq fStack hfStack ⋙
        (abelianRestrictionFunctor B S hS G q hq hG eG).mapDerivedCategory ≅
      (abelianRestrictionFunctor B S hS F p hp hF eF).mapDerivedCategory ⋙
        derivedAbelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack) ×
      (derivedDirectImageFibred B S hS p q hp hq fStack hfStack ⋙
          derivedModuleRestriction B S hS q hq G hG eG ≅
        derivedModuleRestriction B S hS p hp F hF eF ⋙
          derivedDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack) :=
  letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF
  letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG
  ⟨restrictedAbelianTotalDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fStack hfStack,
    restrictedTotalDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fStack hfStack⟩

end AlgebraicGeometry.Space

end
