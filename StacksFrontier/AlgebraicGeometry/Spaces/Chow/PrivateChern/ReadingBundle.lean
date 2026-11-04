module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistDescent

/-!
# The projective bundles of the readings of a module on schemes over an algebraic space

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module. Over every
object `T` of the big fppf site with a morphism `ψ : T ⟶ X` the module reads as a quasi-coherent
module `ℰ_ψ` on the scheme `T` (`AlgebraicGeometry.Space.schemeReading`), and `T`
carries the projective bundle `𝐏(ℰ_ψ) = Proj_T(Sym(ℰ_ψ)) ⟶ T` of Stacks 01OB. Over a morphism
`g : T' ⟶ T` with `g ≫ ψ = ψ'` the comparison `g^*ℰ_ψ ≅ ℰ_{ψ'}` gives the base-change morphism
`𝐏(ℰ_{ψ'}) ⟶ 𝐏(ℰ_ψ)` over `g`, with a cartesian square (Stacks 01O3), and these morphisms
compose. Over the étale charts of `X` these are the chart bundles from which the projective
bundle of `ℰ` is glued; over an arbitrary scheme over `X` they describe its base change.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.readingBundle`: the projective bundle `𝐏(ℰ_ψ)`.
* `AlgebraicGeometry.Space.PrivateChern.readingBundleMap`: the base-change morphisms.
* `AlgebraicGeometry.Space.PrivateChern.readingBundleSite`: `𝐏(ℰ_ψ)` as an object of the big
  fppf site, when `ℰ` is finite locally free.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.isPullback_readingBundleMap`: the cartesian squares.
* `AlgebraicGeometry.Space.PrivateChern.readingBundleMap_comp`: the composition law.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The scheme morphism underlying a morphism of the big fppf site, in the spelling of the
associated big étale site, between the schemes underlying its source and target. -/
abbrev siteSchemeHom {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (BigFppfOver.toScheme B S hS).obj T' ⟶ (BigFppfOver.toScheme B S hS).obj T :=
  _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
include hE

/-- The reading `ℰ_ψ` of `ℰ` on a scheme `T` over `X` is quasi-coherent. -/
instance instIsQuasicoherentSchemeReading {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) : (schemeReading E ψ).IsQuasicoherent :=
  isQuasicoherent_schemeReading E hE ψ

/-- **The projective bundle `𝐏(ℰ_ψ)`** of the reading of `ℰ` on a scheme `T` over `X`. -/
abbrev readingBundle {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    Scheme.{u} :=
  Stacks.RelativeProj.projectiveBundle ((BigFppfOver.toScheme B S hS).obj T) (schemeReading E ψ)

/-- Its projection to `T`. -/
abbrev readingBundleToBase {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    readingBundle E ψ ⟶ (BigFppfOver.toScheme B S hS).obj T :=
  Stacks.RelativeProj.projectiveBundleToBase ((BigFppfOver.toScheme B S hS).obj T)
    (schemeReading E ψ)

/-- **The base-change morphism** `𝐏(ℰ_{ψ'}) ⟶ 𝐏(ℰ_ψ)` over `g : T' ⟶ T` with `g ≫ ψ = ψ'`. -/
def readingBundleMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    readingBundle E ψ' ⟶ readingBundle E ψ :=
  Stacks.RelativeProj.projectiveBundleBaseChange (siteSchemeHom g) (schemeReading E ψ)
    (schemeReading E ψ') (schemeReadingPullbackIso E hE g w).symm

/-- **The base-change square is cartesian**: `𝐏(ℰ_{ψ'}) = 𝐏(ℰ_ψ) ×_T T'`. -/
theorem isPullback_readingBundleMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    IsPullback (readingBundleMap E g w) (readingBundleToBase E ψ') (readingBundleToBase E ψ)
      (siteSchemeHom g) :=
  Stacks.RelativeProj.isPullback_projectiveBundleBaseChange (siteSchemeHom g) (schemeReading E ψ)
    (schemeReading E ψ') (schemeReadingPullbackIso E hE g w).symm

/-- The base-change morphism lies over `g`: it commutes with the projections to `T'` and `T`. -/
@[reassoc]
theorem readingBundleMap_toBase {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    readingBundleMap E g w ≫ readingBundleToBase E ψ =
      readingBundleToBase E ψ' ≫ siteSchemeHom g :=
  (isPullback_readingBundleMap E g w).w

/-- **The composition law of the base-change morphisms.** -/
theorem readingBundleMap_comp {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    {ψ'' : representedAlgebraicSpace B S hS T'' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') (w' : representedSpaceMap B S hS h ≫ ψ' = ψ'')
    (w'' : representedSpaceMap B S hS (h ≫ g) ≫ ψ = ψ'') :
    readingBundleMap E h w' ≫ readingBundleMap E g w = readingBundleMap E (h ≫ g) w'' := by
  refine Stacks.RelativeProj.projectiveBundleBaseChange_comp (siteSchemeHom h) (siteSchemeHom g)
    (schemeReading E ψ) (schemeReading E ψ') (schemeReading E ψ'') _ _ _ ?_
  have key := congrArg Iso.hom (schemeReadingPullbackIso_comp E hE h g w w' w'')
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at key
  simp only [Iso.symm_inv]
  exact key.symm

/-! ### The bundles in the big fppf site -/

section Site

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
include hfree

/-- **The reading of a finite locally free module on a scheme over `X` is finite locally
free.** -/
theorem isFiniteLocallyFree_schemeReading {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (schemeReading E ψ) := by
  have h₁ := isFiniteLocallyFreeOnSite_modulePullback B S hS ψ E hE hfree
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj
        ((modulePullback B S hS ψ).obj E)) :=
    (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS T _).1
      (SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
        ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app _).symm h₁)
  exact
    AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property _ h₂

/-- The projective bundle `𝐏(ℰ_ψ)` is contained in the big fppf site. -/
theorem contains_readingBundle {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) : B.Contains (readingBundle E ψ) := by
  have := isFiniteLocallyFree_schemeReading E hfree ψ
  have : (schemeReading E ψ).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree _
  have := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType
    ((BigFppfOver.toScheme B S hS).obj T) (schemeReading E ψ)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (readingBundleToBase E ψ)
    T.left.property

/-- `𝐏(ℰ_ψ)` as an object of the big fppf site over `S`. -/
def readingBundleSite {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    BigFppfOver B S hS :=
  BigFppfOver.siteObjectOver B S hS T (contains_readingBundle E hfree ψ) (readingBundleToBase E ψ)

/-- Its projection to `T`, as a morphism of the site. -/
def readingBundleSiteToBase {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) : readingBundleSite E hfree ψ ⟶ T :=
  BigFppfOver.siteMapOver B S hS T (contains_readingBundle E hfree ψ) (readingBundleToBase E ψ)

/-- The base-change morphism, as a morphism of the site. -/
def readingBundleSiteMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    readingBundleSite E hfree ψ' ⟶ readingBundleSite E hfree ψ :=
  Over.homMk (ObjectProperty.homMk (readingBundleMap E g w)) (by
    apply ObjectProperty.hom_ext
    change readingBundleMap E g w ≫ readingBundleToBase E ψ ≫ T.hom.hom =
      readingBundleToBase E ψ' ≫ T'.hom.hom
    rw [← Category.assoc, readingBundleMap_toBase, Category.assoc]
    exact congrArg (readingBundleToBase E ψ' ≫ ·) (congrArg (fun k => k.hom) (Over.w g)))

/-- The scheme morphism underlying `readingBundleSiteMap` is `readingBundleMap`. -/
@[simp]
theorem toScheme_map_readingBundleSiteMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    (BigFppfOver.toScheme B S hS).map (readingBundleSiteMap E hfree g w) = readingBundleMap E g w :=
  rfl

/-- **The base-change square of the site bundles is cartesian.** -/
theorem isPullback_readingBundleSiteMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    IsPullback (readingBundleSiteMap E hfree g w) (readingBundleSiteToBase E hfree ψ')
      (readingBundleSiteToBase E hfree ψ) g :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) (isPullback_readingBundleMap E g w)

/-- **The composition law of the base-change morphisms of the site bundles.** -/
theorem readingBundleSiteMap_comp {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    {ψ'' : representedAlgebraicSpace B S hS T'' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') (w' : representedSpaceMap B S hS h ≫ ψ' = ψ'')
    (w'' : representedSpaceMap B S hS (h ≫ g) ≫ ψ = ψ'') :
    readingBundleSiteMap E hfree h w' ≫ readingBundleSiteMap E hfree g w =
      readingBundleSiteMap E hfree (h ≫ g) w'' :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (readingBundleMap_comp E h g w w' w''))

/-- Over an étale chart of `X` the bundle is the chart bundle of the projective bundle of `ℰ`. -/
theorem readingBundleSite_chartToSpace (V : SmallEtale B S hS X.1) :
    readingBundleSite E hfree (chartToSpace B S hS X V) = (projectiveBundleChartFamily E
        hfree).site V :=
  rfl

/-- Over a morphism of étale charts of `X` the base-change morphism is the transition morphism
of the chart bundles of the projective bundle of `ℰ`. -/
theorem readingBundleSiteMap_chart {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    readingBundleSiteMap E hfree ((SmallEtale.toOver B S hS X.1).map h)
        (representedSpaceMap_toOver_map_comp_chartToSpace h) =
      (projectiveBundleChartFamily E hfree).siteMap h :=
  rfl

end Site

end AlgebraicGeometry.Space.PrivateChern

end
