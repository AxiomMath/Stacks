module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement

/-!
# The unbounded derived direct image of modules on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  The direct image of `𝒪`-modules on the small étale sites,
`AlgebraicGeometry.Space.modulePushforward` (the pushforward half of Stacks 03LU), is additive,
so it acts on the unbounded homotopy categories of cochain complexes.  This file proves that the
resulting functor to the derived category of `𝒪_Y`-modules has a *right derived functor on the
whole unbounded derived category* `D(𝒪_X)`, with no further hypothesis — the existence of `Rf_*`
that the derived adjunction of Stacks 07A6 consumes.

The content is that `Mod(𝒪_X)` is Grothendieck abelian, so Stacks 079P supplies a functorial
K-injective resolution of every complex, and a functor out of the homotopy category that admits
K-injective resolutions has a pointwise right derived functor.

## Main results

* `AlgebraicGeometry.Space.isGrothendieckAbelian_modules`: the `𝒪_F`-modules on the small étale
  ringed site of an algebraic space form a Grothendieck abelian category at the universe of the
  structure rings.
* `AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`: every cochain complex of
  `𝒪_F`-modules admits a quasi-isomorphism into a K-injective complex.
* `AlgebraicGeometry.Space.hasPointwiseRightDerivedFunctor_modulePushforward` and
  `AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`: **the unbounded derived
  direct image `Rf_*` exists**, for every morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isIso_app_of_isKInjective_modulePushforward`: a K-injective complex
  computes it — on such a complex the comparison from the degreewise direct image to any right
  derived functor of it is invertible.
* `AlgebraicGeometry.Space.isIso_totalRightDerivedUnit_app_modulePushforward_of_isKInjective`:
  the same for the chosen total right derived functor and its canonical unit, which is the form
  `f_*I ⟶ Rf_*I` and which exhibits inhabitants for the instance hypotheses of the previous
  item.

## Implementation notes

*Why the general ringed-topos form does not apply.*  Stacks 07A6 is developed for a ringed topos by
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pushforward_hasRightDerivedFunctor`,
which is exactly this statement.  Neither of its two shape requirements is met here.  It is
stated for
`AlgebraicGeometry.RingedTopos.{w, w, w}`, whereas the small étale ringed topos of an algebraic
space is `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — objects in `Type (u + 1)`, morphisms
and structure rings in `Type u`.  And it consumes an `AlgebraicGeometry.RingedToposSiteHom`,
whose geometric morphism is presented by a continuous functor between the underlying sites;
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` is an `AlgebraicGeometry.RingedToposHom`,
presented by a `AlgebraicGeometry.MorphismOfTopoi`, because a morphism of algebraic spaces
induces no functor between the small étale sites — the geometric morphism is assembled on the
spaces-étale site and conjugated by the comparison equivalences of Stacks 03G1.

*What replaces the pinned input.*  The off-diagonal universes are exactly what
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`
(`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjects.lean`) is for; the
`{w, w, w}` file instead uses `SheafOfModules.isGrothendieckAbelianU`, which asks for a site
small on the nose.  The `EssentiallySmall` instance it needs is
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`, but it has to be restated by `change`
at the reduced spelling of the site: instance search does not unfold the projection
`(smallEtaleRingedSite B S hS F hF).C`, and an instance *at* the projection spelling must not be
added, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentGrothendieck.lean`.

*No new definition, and no instance.*  `Functor.HasPointwiseRightDerivedFunctor` and
`Functor.HasRightDerivedFunctor` are `Prop`-valued classes, so the two existence results are
plain theorems and a consumer supplies them with `have`; `Rf_*` itself is then
`Functor.totalRightDerived` of the functor written out below, and is not given a second name
here.  `HasDerivedCategory` is data, so it is carried as an instance binder rather than fixed to
`HasDerivedCategory.standard` by a local attribute: the results then hold for whichever derived
category a consumer has chosen, which is what the statements of Tags 08FA, 08GK, 08GY and 08II need.
The last theorem specializes them to the chosen derived category and the chosen total right
derived functor, using `attribute [local instance]` on `HasDerivedCategory.standard` and on
`hasRightDerivedFunctor_modulePushforward`; both are file-scoped, so no global instance is
added and nothing outside this file can be redirected by them.

*No tag is placed.*  None of these statements is a clause of Stacks 07A6, which asserts the
*adjunction* `Lf^* ⊣ Rf_*`; they are the existence premise it consumes, and
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction` carries no `@[stacks]` attribute on its
own copy of them either.  Nor are they a clause of Stacks 03LU, whose direct-image,
inverse-image, adjunction and additivity clauses are already tagged elsewhere.  The same
reasoning, with the same conclusion, is recorded at
`Stacks.Sheaves.RingedToposModules.additive_pushforwardModules`.

*The derived inverse image is not here, and is not reachable the same way.*  A left derived
functor needs a resolving class, and the one Stacks resolves by — the K-flat complexes with flat
terms of Stacks 06YS — is unavailable on this site:
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` demands
`CategoryTheory.SmallCategory` of the site, which the small étale site of an algebraic space is
not.  Even granted resolutions, the exactness half
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso` is carried as a
hypothesis throughout the ringed-topos development and is stated there for a morphism of
sites.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪_F`-modules on the small étale ringed site of an algebraic space form a Grothendieck
abelian category, at the universe of the structure rings.

This is `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` for the small étale site,
whose objects live in `Type (u + 1)` while its structure sheaf is `CommRingCat.{u}`-valued.  It
is stated as a theorem rather than an instance because an `EssentiallySmall` instance at the
projection spelling `(smallEtaleRingedSite B S hS F hF).C` breaks existing lemmas that unify
against the reduced spelling. -/
theorem isGrothendieckAbelian_modules (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  exact SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- **Stacks 079P for the modules on an algebraic space.**  Every cochain complex of
`𝒪_F`-modules on the small étale ringed site of an algebraic space admits a quasi-isomorphism
into a K-injective complex.

The category of such modules is Grothendieck abelian by
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`, so Stacks 079P supplies a *functorial*
K-injective resolution; only its value at the given complex is recorded here. -/
theorem exists_quasiIso_isKInjective_modules (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (K : CochainComplex (Modules.{u, u} B S hS F hF) ℤ) :
    ∃ (I : CochainComplex (Modules.{u, u} B S hS F hF) ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    isGrothendieckAbelian_modules B S hS F hF
  obtain ⟨R⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{u}
    (Modules.{u, u} B S hS F hF)
  exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩

variable {X Y : AlgebraicSpaces B S hS}

/-- K-injective resolutions compute the derived direct image pointwise: the degreewise direct
image of `𝒪_X`-modules, followed by localization to `D(𝒪_Y)`, has a *pointwise* right derived
functor on the unbounded derived category of `𝒪_X`-modules. -/
theorem hasPointwiseRightDerivedFunctor_modulePushforward (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)] :
    ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} _
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)).1

/-- **The unbounded derived direct image `Rf_*` exists**, for every morphism `f : X ⟶ Y` of
algebraic spaces and with no further hypothesis: the degreewise direct image of `𝒪_X`-modules,
followed by localization, has a right derived functor on the whole of `D(𝒪_X)`.

`Rf_*` is then `Functor.totalRightDerived` of that functor, and a K-injective complex computes
it by `AlgebraicGeometry.Space.isIso_app_of_isKInjective_modulePushforward`. -/
theorem hasRightDerivedFunctor_modulePushforward (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)] :
    ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  have := hasPointwiseRightDerivedFunctor_modulePushforward B S hS f
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- A K-injective complex computes the derived direct image: for *any* right derived functor
`RF` of the degreewise direct image, with comparison `α`, the component of `α` at a K-injective
complex is an isomorphism.

Taking `L := DerivedCategory.Qh`, `RF := Functor.totalRightDerived …` and `α` its unit gives the
statement that `f_* I ⟶ Rf_* I` is invertible for `I` K-injective. -/
theorem isIso_app_of_isKInjective_modulePushforward (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
    {D : Type (u + 1)} [Category.{u + 1} D]
    (L : HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (RF : D ⥤ DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
      (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} _
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)).2 L RF α I hI

section Standard

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasRightDerivedFunctor_modulePushforward

/-- `f_*I ⟶ Rf_*I` is invertible for a K-injective complex `I`, with `Rf_*` the chosen total
right derived functor of the degreewise direct image and the comparison its canonical unit.

This is `AlgebraicGeometry.Space.isIso_app_of_isKInjective_modulePushforward` at the one
localization and one right derived functor that are always available, and it is what exhibits
inhabitants for that statement's `HasDerivedCategory`, `Functor.IsLocalization` and
`Functor.IsRightDerivedFunctor` hypotheses: the chosen derived category, `DerivedCategory.Qh`,
and `Functor.totalRightDerived` with its unit.  Both instance attributes are `local`, so no
global instance is declared. -/
theorem isIso_totalRightDerivedUnit_app_modulePushforward_of_isKInjective (f : X ⟶ Y)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective) :
    IsIso ((((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)).obj I)) :=
  isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh _ _ I hI

end Standard

end AlgebraicGeometry.Space

end
