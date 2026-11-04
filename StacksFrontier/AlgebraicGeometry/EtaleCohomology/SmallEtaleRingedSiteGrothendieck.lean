module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Sheaves of modules on the small étale site are Grothendieck abelian in the module universe

Let `S` be a scheme.  The small étale site `AlgebraicGeometry.SmallEtale` of `S` has its objects
in `Type (u + 1)` and its morphisms in `Type u`, and its structure sheaf takes values in the
rings of `Type u`.  Its sheaves of `𝒪`-modules with sections in `u` are therefore
`SheafOfModules.{u}` over a site whose objects do *not* fit in `u`, and none of the general
Grothendieck abelianness results applies to them:
`SheafOfModules.instIsGrothendieckAbelian` asks for a site that is small on the nose,
`Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules` asks for `UnivLE.{u + 1, u}`,
and `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` and
`StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian` state the module universe as the
literal maximum of the site universes, which here is `u + 1`.

What does apply is essential smallness.  The small étale site is `EssentiallySmall.{u}`
(`AlgebraicGeometry.SmallEtale.essentiallySmall`), and
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` transports Mathlib's instance along
the equivalence with a small model, asking only for essential smallness at the module universe
and the two sheafification hypotheses that the small étale site also satisfies
(`AlgebraicGeometry.SmallEtale.hasSheafify`,
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective`).  That result is a theorem rather than an
instance on purpose: as an instance it would be attempted at every site in the development.
This file applies it once at each of the two spellings of the small étale site, and reads off the
functorial K-injective resolution of Stacks 079P, which is what needed the Grothendieck abelian
structure in the module universe.

## Main results

* `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheafOfModules`: the sheaves of modules
  over a sheaf of rings on the small étale site of `S`, with sections in the universe of the
  schemes, form a Grothendieck abelian category at that universe.
* `AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian` is the same statement for the
  projections of `AlgebraicGeometry.smallEtaleRingedSite`, which instance search does not unfold.

## Main definitions

* `AlgebraicGeometry.SmallEtale.ringedSite_kInjectiveResolution` and
  `AlgebraicGeometry.SmallEtale.ringedSite_kInjectiveAugmentation`: the chosen functorial
  K-injective resolution of a complex of sheaves of `𝒪`-modules with sections in the universe of
  the schemes on the small étale ringed site of `S`, and its augmentation.

## Implementation notes

`CategoryTheory.IsGrothendieckAbelian` is a `Prop`, so the two instances below cannot diamond
against each other or against any other route to the same goal, and neither takes an instance
argument of its own class, so neither can enter a loop.  This is the same reason the three
sheafification instances of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleRingedSiteInternalHom.lean` are safe,
and the reason the abelian structure is *not* restated there: `CategoryTheory.Abelian` is data.

Both instances mention the topology of the small étale site — the first as
`AlgebraicGeometry.SmallEtale.topology`, the second as the `J` projection of
`AlgebraicGeometry.smallEtaleRingedSite` — so neither can be used at any other site; that is
what keeps them from behaving like the generic instance the underlying theorem would be.

The derived internal Hom bifunctor `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` is
still not available here, and not for want of this instance: it is stated for a
`AlgebraicGeometry.RingedSite.{u, u, u}`, whereas `AlgebraicGeometry.smallEtaleRingedSite` is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, so the two do not even have the same type.  The
K-injective resolution below is the part of that construction which the universes do permit, and
it is obtained from `Stacks.Injectives.kInjectiveResolutionFunctor` directly rather than from
`AlgebraicGeometry.RingedSite.kInjectiveResolution`, which carries the same restriction.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Grothendieck abelianness at the two spellings of the site -/

/-- **The sheaves of modules over a sheaf of rings on the small étale site of `S`, with sections
in the universe of the schemes, form a Grothendieck abelian category at that universe.**

The objects of the site live in `Type (u + 1)`, so this is not an instance of Mathlib's
`SheafOfModules.instIsGrothendieckAbelian`; it is
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` applied to
`AlgebraicGeometry.SmallEtale.essentiallySmall`. -/
public instance SmallEtale.isGrothendieckAbelian_sheafOfModules
    (R : Sheaf (SmallEtale.topology B S hS) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

/-- The sheaves of modules over a sheaf of rings on the small étale ringed site of `S`, with
sections in the universe of the schemes, form a Grothendieck abelian category at that universe.

The content is `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheafOfModules`; this restates
it for the projections of `AlgebraicGeometry.smallEtaleRingedSite`, which instance search does
not unfold. -/
public instance smallEtaleRingedSite_isGrothendieckAbelian
    (R : Sheaf (smallEtaleRingedSite B S hS).J RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

namespace SmallEtale

/-! ### The functorial K-injective resolution -/

/-- **The chosen functorial K-injective resolution of complexes of sheaves of `𝒪`-modules with
sections in the universe of the schemes on the small étale ringed site of `S`.**

This is `Stacks.Injectives.kInjectiveResolutionFunctor`, which needs those module sheaves to be
Grothendieck abelian in their own universe; that is
`AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`. -/
public abbrev ringedSite_kInjectiveResolution :
    CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ℤ :=
  Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))

/-- The augmentation of a complex of sheaves of `𝒪`-modules with sections in the universe of the
schemes on the small étale ringed site of `S` into its chosen K-injective resolution. -/
public abbrev ringedSite_kInjectiveAugmentation :
    Functor.id
        (CochainComplex (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ℤ) ⟶
      ringedSite_kInjectiveResolution B S hS :=
  Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))

end SmallEtale

end AlgebraicGeometry

end
