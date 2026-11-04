module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a derived direct image along an étale morphism of algebraic spaces

Let

```
U --f'--> V
|i        |g
X --f---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale — equivalently, `g : V ⟶ Y` is étale, `U = V ×_Y X` and `f'` is the projection.
Then restriction to `V` commutes with the unbounded derived direct image:
`(Rf_*E)|_V ≅ Rf'_*(E|_U)` for `E` in `D(𝒪_X)`.  This is Stacks 08GE.

The two inputs of the source's argument are both available.  The first is that restriction along
an étale morphism carries K-injective complexes to K-injective complexes, Stacks 08FI read at
the small étale site of an algebraic space; it is
`AlgebraicGeometry.Space.isKInjective_etaleModulePullback` below.  The second is the underived
comparison `f'_*(F|_U) = (f_*F)|_V` of Stacks 03LX, which is
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`.

## Main definitions

* `AlgebraicGeometry.Space.etaleModulePushforwardRestrictHomotopyIso`: the comparison of Stacks
  03LX on homotopy categories of cochain complexes — the isomorphism
  `(f_*I)|_V ≅ f'_*(I|_U)` that the source's proof uses on a K-injective representative.
* `AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIso`: **Stacks 08GE**, the
  natural isomorphism `Rf ⋙ Rg ≅ Ri ⋙ Rf'` of functors `D(𝒪_X) ⥤ D(𝒪_V)`.

## Main results

* `AlgebraicGeometry.Space.isKInjective_etaleModulePullback`: restriction of modules along an
  étale morphism of algebraic spaces carries K-injective complexes of `𝒪_Y`-modules to
  K-injective complexes of `𝒪_X`-modules.  This is the content of Stacks 08FI at the spelling
  used here; the tag itself stays on
  `Stacks.Cohomology.Localization.isKInjective_over`, which states it for restriction to the
  site localized at an object.
* `AlgebraicGeometry.Space.isIso_etaleModulePullback_derivedUnit`: the unit of any total right
  derived functor of restriction along an étale morphism is an isomorphism, so such a derived
  functor really is ordinary restriction on derived categories.

## Implementation notes

*Extension by zero enters as data, and why that is the unconditional statement.*  Stacks 08FI is
the adjoint criterion of Stacks 08BJ applied to the exact left adjoint `j_!` of restriction.  On
the small étale site of an algebraic space that left adjoint is not constructed in this
development: `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RestrictExtensionByZero.lean` already
carries it as data for Stacks 08HA, with exactly the justification that applies here — a left
adjoint together with an adjunction exhibiting it as one determines the functor up to a unique
compatible isomorphism, so the hypotheses `fShriek`, `adj` and the three exactness instances pin
`j_!` rather than weaken the statement.  The same convention is followed below, so Stacks 08GE
is stated for a general étale `g` and not only for the special cases in which `j_!` happens to
be available.  Nothing else about `j_!` is used: only `AlgebraicGeometry.Space.etaleModulePullback`
appears in the conclusion of Stacks 08GE.

*Why the library's Stacks 08FI does not apply directly.*
`Stacks.Cohomology.Localization.isKInjective_over` is Stacks 08FI for restriction to the site
localized at an *object*, `CategoryTheory.SheafOfModules.overFunctor`, over a site whose objects
lie in the universe of its morphisms.  Neither shape matches: restriction along an étale
morphism of algebraic spaces is `AlgebraicGeometry.Space.etaleModulePullback`, restriction of
sections along `AlgebraicGeometry.Space.smallEtalePostcomp` — identified with the restriction of
modules of Stacks 03D1 by `AlgebraicGeometry.Space.etaleModulePullback_eq_restrictionModules`,
*not* with a slice — and the small étale ringed site of an algebraic space is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, whose objects are one universe above its
morphisms.  `isKInjective_etaleModulePullback` below is therefore the bridge to that spelling,
written as an ordinary API lemma: the existing `@[stacks 08FI]` attribute states the tag faithfully
and stays exactly where it is, and no second attribute for it is added here.

*The derived functors are arbitrary choices.*  As in the ringed-space analogue
`Stacks.Cohomology.derivedPushforwardRestrictIso` of Stacks 08FE, the
four functors `Rf`, `Rf'`, `Ri`, `Rg` are taken as arguments together with natural
transformations exhibiting them as total right derived functors.  A caller holding any model of
`Rf_*` can therefore use the result, and no choice of K-injective resolutions is built into the
statement.  Restriction along an étale morphism is exact, so the unit of any right derived
functor of it is invertible — `isIso_etaleModulePullback_derivedUnit` — and `Ri` and `Rg` really
are ordinary restriction.

*What makes the two composites right derived functors.*
`Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives` needs the first
comparison to be invertible on K-injective complexes and the second on their images.  For
`Rf ⋙ Rg` the first is `AlgebraicGeometry.Space.isIso_app_of_isKInjective_modulePushforward` and
the second is exactness of restriction; for `Ri ⋙ Rf'` the first is exactness of restriction and
the second is where Stacks 08FI is consumed, through
`isKInjective_etaleModulePullback`.  The Grothendieck abelian hypothesis it asks of `D(𝒪_X)` is
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`.

*The inherited caveat.*  The source asserts an equality of functors, and the underived input
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` has the right endpoints but is not
proved to be the adjunction mate of the identification of the two composite inverse images
around the square; that standing is recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePushforwardBaseChange.lean`.  The derived
comparison constructed here is the image of that underived one under
`CategoryTheory.Functor.rightDerivedNatIso`, so it inherits the caveat and nothing more.

## References

* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-! ### Stacks 08FI at the small étale site of an algebraic space -/

/-- Restriction of modules along an étale morphism `f : X ⟶ Y` of algebraic spaces carries a
K-injective complex of `𝒪_Y`-modules to a K-injective complex of `𝒪_X`-modules.

This is the content of Stacks 08FI at the spelling the small étale site of an algebraic space
uses.  **No `@[stacks 08FI]` attribute is placed here**: that tag is already carried by
`Stacks.Cohomology.Localization.isKInjective_over`, which states it faithfully for restriction to
the site localized at an object.  What this adds is the Lean-side bridge to
`AlgebraicGeometry.Space.etaleModulePullback`, which is restriction of sections along
`AlgebraicGeometry.Space.smallEtalePostcomp` and not a slice; see the implementation notes.

Extension by zero enters as data — the functor `fShriek`, the adjunction `adj` exhibiting it as a
left adjoint of restriction, and its exactness — exactly as in Stacks 08HA
(`AlgebraicGeometry.Space.isIso_restrictExtensionByZeroMap`); an adjoint and its adjunction
determine the functor up to a unique compatible isomorphism, so this pins `j_!`.  With that, the
statement is the adjoint criterion of Stacks 08BJ,
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`. -/
theorem isKInjective_etaleModulePullback
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {fShriek : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (adj : fShriek ⊣ etaleModulePullback.{u, u} B S hS f hf)
    [fShriek.Additive] [PreservesFiniteLimits fShriek] [PreservesFiniteColimits fShriek]
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((etaleModulePullback.{u, u} B S hS f hf).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  have := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (etaleModulePullback.{u, u} B S hS f hf) fShriek adj I

/-! ### Restriction needs no derivation -/

/-- Restriction along an étale morphism of algebraic spaces is exact, so the comparison from its
degreewise extension to the homotopy category into any total right derived functor of it is an
isomorphism: such a derived functor is ordinary restriction on derived categories. -/
theorem isIso_etaleModulePullback_derivedUnit
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
    (Rf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (α : (etaleModulePullback.{u, u} B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))] :
    IsIso α :=
  Stacks.Cohomology.Localization.isIso_of_isRightDerivedFunctor_of_exact
    (etaleModulePullback.{u, u} B S hS f hf) Rf α

/-! ### The comparison of Stacks 03LX on homotopy categories -/

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y}

/-- The comparison of Stacks 03LX, applied termwise to cochain complexes and passed to homotopy
categories: `(f_*I)|_{Y'} ≅ f'_*(I|_{X'})` for a cartesian square with `g` étale.  This is the
isomorphism the proof of Stacks 08GE uses on a K-injective representative. -/
def etaleModulePushforwardRestrictHomotopyIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (etaleModulePullback.{u, u} B S hS i
            (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) :=
  let e : (modulePushforward B S hS f ⋙
        etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (etaleModulePullback.{u, u} B S hS i
            (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
          modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) :=
    { hom := (modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).inv.mapHomotopyCategory
        (ComplexShape.up ℤ)
      inv := (modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).hom.mapHomotopyCategory
        (ComplexShape.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePushforward B S hS f ⋙ etaleModulePullback.{u, u} B S hS g hg))
      (ComplexShape.up ℤ)) ≪≫ e ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleModulePullback.{u, u} B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        modulePushforward B S hS f')) (ComplexShape.up ℤ)).symm

/-! ### Stacks 08GE -/

/-- **Stacks 08GE.**  Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`, let `g : Y' ⟶ Y` be an étale morphism, set `X' = Y' ×_Y X` and let `f' : X' ⟶ Y'` be the
projection.  Then restricting the unbounded derived direct image along `g` agrees with taking the
derived direct image along `f'` after restricting along `i`:
`(Rf_*E)|_{Y'} ≅ Rf'_*(E|_{X'})` for `E` in `D(𝒪_X)`.

The four derived functors are arbitrary choices equipped with their canonical units, so the
result applies in particular to the standard `Rf_*` of
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward` and to the exact restriction
functors.  Extension by zero along `i` enters as data, for the reason recorded in the
implementation notes of this file and in Stacks 08HA; it is the only such input, because on the
`Rf ⋙ Rg` side exactness of restriction along `g` already makes the comparison invertible. -/
@[stacks 08GE]
def derivedModulePushforwardEtaleRestrictIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    {iShriek : Modules.{u, u} B S hS X'.1 X'.2 ⥤ Modules.{u, u} B S hS X.1 X.2}
    (adji : iShriek ⊣ etaleModulePullback.{u, u} B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    [iShriek.Additive] [PreservesFiniteLimits iShriek] [PreservesFiniteColimits iShriek]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X'.1 X'.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y'.1 Y'.2)]
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (Rf' : DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2))
    (Ri : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2))
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2))
    (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (αf' : (modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
    (αi : (etaleModulePullback.{u, u} B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
    (αg : (etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf'
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X'.1 X'.2) (ComplexShape.up ℤ))]
    [Ri.IsRightDerivedFunctor αi
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))] :
    Rf ⋙ Rg ≅ Ri ⋙ Rf' := by
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  haveI : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  have hαg : IsIso αg := isIso_etaleModulePullback_derivedUnit B S hS g hg Rg αg
  have hαi : IsIso αi := isIso_etaleModulePullback_derivedUnit B S hS i hi Ri αi
  have hleft : (Rf ⋙ Rg).IsRightDerivedFunctor
      (Functor.whiskerLeft
          ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ)) αg ≫
        Functor.whiskerRight αf Rg)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
    refine Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
      (modulePushforward B S hS f) (etaleModulePullback.{u, u} B S hS g hg) Rf Rg αf αg
      (fun I hI => ?_) (fun I _ => ?_)
    · exact isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh Rf αf I hI
    · have := hαg
      infer_instance
  have hright : (Ri ⋙ Rf').IsRightDerivedFunctor
      (Functor.whiskerLeft
          ((etaleModulePullback.{u, u} B S hS i hi).mapHomotopyCategory
            (ComplexShape.up ℤ)) αf' ≫
        Functor.whiskerRight αi Rf')
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
    refine Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
      (etaleModulePullback.{u, u} B S hS i hi) (modulePushforward B S hS f') Ri Rf' αi αf'
      (fun I _ => ?_) (fun I hI => ?_)
    · have := hαi
      infer_instance
    · exact isIso_app_of_isKInjective_modulePushforward B S hS f' DerivedCategory.Qh Rf' αf'
        (((etaleModulePullback.{u, u} B S hS i hi).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
        (isKInjective_etaleModulePullback B S hS i hi adji I hI)
  have := hleft
  have := hright
  exact Functor.rightDerivedNatIso (Rf ⋙ Rg) (Ri ⋙ Rf')
    (Functor.whiskerLeft
        ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ)) αg ≫
      Functor.whiskerRight αf Rg)
    (Functor.whiskerLeft
        ((etaleModulePullback.{u, u} B S hS i hi).mapHomotopyCategory
          (ComplexShape.up ℤ)) αf' ≫
      Functor.whiskerRight αi Rf')
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (etaleModulePushforwardRestrictHomotopyIso B S hS sq hg) DerivedCategory.Qh)

end Square

end AlgebraicGeometry.Space

end
