module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Finitely presented modules over a localization, and their pure spreadouts

Let `A → B` be a ring map of finite presentation, let `S` be a multiplicative subset of `B`,
and let `N` be a finitely presented module over `S⁻¹B`. A *pure spreadout* of this situation
consists of an affine open of `Spec B` containing `Spec S⁻¹B` and a finitely presented module
on it which localizes to `N`, such that the spreadout module is projective over `A` and its
localization map is universally injective over `A`.

## Main definitions

* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation` bundles the rings, the
  multiplicative subset, a localization, and the finitely presented module.
* `AlgebraicGeometry.PureSpreadout` packages a pure spreadout of such a situation.

## Implementation notes

The localization `S⁻¹B` is represented abstractly by a `B`-algebra satisfying
`IsLocalization S`, so later statements do not depend on a chosen construction of the
localization. Its `A`-algebra structure and the restricted `B`- and `A`-module structures on
`N` are supplied canonically as instances.

An affine open of `Spec B` is represented by a `B`-algebra `C` for which `Spec C ⟶ Spec B` is
an open immersion. The condition that it contain `Spec S⁻¹B` is represented by a compatible
algebra structure `C → S⁻¹B`. The map from the spreadout module to `N` is required to exhibit
`N` as its localization at `S`; retaining it as a `C`-linear map also records compatibility
with the module of sections on the affine open.

Universal injectivity uses `UniversallyInjectivePoly`, so the universe of the test module is
independent of the universe of the spreadout module. In particular, it can be chosen to
contain quotients of the base ring.

## References

* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0AT6.** The standing situation of a finitely presented algebra `B`
over `A`, a multiplicative subset `S ⊆ B`, and a finitely presented module over a
localization of `B` at `S`. -/
@[stacks 0AT6]
structure FinitelyPresentedLocalizedModuleSituation where
  /-- The base ring. -/
  A : Type u₁
  /-- The finitely presented algebra over `A`. -/
  B : Type u₂
  /-- A ring realizing the localization of `B` at `S`. -/
  Bₛ : Type u₃
  /-- The module over the localized ring. -/
  N : Type u₄
  /-- The commutative ring structure on `A`. -/
  [commRingA : CommRing A]
  /-- The commutative ring structure on `B`. -/
  [commRingB : CommRing B]
  /-- The map `A → B`. -/
  [algebraAB : Algebra A B]
  /-- The map `A → B` is of finite presentation. -/
  [finitePresentationAB : Algebra.FinitePresentation A B]
  /-- The multiplicative subset of `B`. -/
  S : Submonoid B
  /-- The commutative ring structure on the localized ring. -/
  [commRingBₛ : CommRing Bₛ]
  /-- The localization map `B → Bₛ`. -/
  [algebraBBₛ : Algebra B Bₛ]
  /-- The ring `Bₛ` is a localization of `B` at `S`. -/
  [isLocalization : IsLocalization S Bₛ]
  /-- The additive group underlying `N`. -/
  [addCommGroupN : AddCommGroup N]
  /-- The module structure on `N` over the localization. -/
  [moduleBₛN : Module Bₛ N]
  /-- The module `N` is finitely presented over the localization. -/
  [finitePresentationN : Module.FinitePresentation Bₛ N]

attribute [instance]
  FinitelyPresentedLocalizedModuleSituation.commRingA
  FinitelyPresentedLocalizedModuleSituation.commRingB
  FinitelyPresentedLocalizedModuleSituation.algebraAB
  FinitelyPresentedLocalizedModuleSituation.finitePresentationAB
  FinitelyPresentedLocalizedModuleSituation.commRingBₛ
  FinitelyPresentedLocalizedModuleSituation.algebraBBₛ
  FinitelyPresentedLocalizedModuleSituation.isLocalization
  FinitelyPresentedLocalizedModuleSituation.addCommGroupN
  FinitelyPresentedLocalizedModuleSituation.moduleBₛN
  FinitelyPresentedLocalizedModuleSituation.finitePresentationN

namespace FinitelyPresentedLocalizedModuleSituation

/-- The composite algebra structure on the localization. -/
instance algebraLocalized (X : FinitelyPresentedLocalizedModuleSituation) :
    Algebra X.A X.Bₛ :=
  ((algebraMap X.B X.Bₛ).comp (algebraMap X.A X.B)).toAlgebra

/-- The algebra structures on `Bₛ` form the canonical tower `A → B → Bₛ`. -/
instance isScalarTower_localized (X : FinitelyPresentedLocalizedModuleSituation) :
    IsScalarTower X.A X.B X.Bₛ :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical `B`-module structure on the localized module. -/
instance moduleAlgebra (X : FinitelyPresentedLocalizedModuleSituation) : Module X.B X.N :=
  Module.compHom X.N (algebraMap X.B X.Bₛ)

/-- The canonical `A`-module structure on the localized module. -/
instance moduleBase (X : FinitelyPresentedLocalizedModuleSituation) : Module X.A X.N :=
  Module.compHom X.N (algebraMap X.A X.Bₛ)

/-- Restriction of scalars from `Bₛ` to `B` is compatible with scalar multiplication. -/
instance isScalarTower_moduleAlgebra (X : FinitelyPresentedLocalizedModuleSituation) :
    IsScalarTower X.B X.Bₛ X.N :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Restriction of scalars from `Bₛ` to `A` is compatible with scalar multiplication. -/
instance isScalarTower_moduleBase (X : FinitelyPresentedLocalizedModuleSituation) :
    IsScalarTower X.A X.Bₛ X.N :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The restricted `A`- and `B`-module structures on `N` form a scalar tower. -/
instance isScalarTower_module (X : FinitelyPresentedLocalizedModuleSituation) :
    IsScalarTower X.A X.B X.N :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

end FinitelyPresentedLocalizedModuleSituation

/-- A pure spreadout of a finitely presented module over a localization.

The algebra `C` is the ring of functions on the chosen affine open. The `B`-algebra map from
`C` to `Bₛ` says that the localized spectrum is contained in that open. -/
structure PureSpreadout
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄}) where
  /-- The coordinate ring of the affine open. -/
  C : Type u₂
  /-- The coordinate ring is commutative. -/
  [commRingC : CommRing C]
  /-- The structural map from `B` to the coordinate ring. -/
  [algebraBC : Algebra X.B C]
  /-- The induced map from the base ring to the coordinate ring. -/
  [algebraAC : Algebra X.A C]
  /-- The maps out of `A` and `B` into the coordinate ring form a tower. -/
  [isScalarTowerABC : IsScalarTower X.A X.B C]
  /-- The corresponding morphism of spectra identifies `Spec C` with an open
  subscheme of `Spec B`. -/
  [isOpenImmersion :
    IsOpenImmersion (Scheme.Spec.map (CommRingCat.ofHom (algebraMap X.B C)).op)]
  /-- The localized spectrum factors through the chosen affine open. -/
  [algebraCBₛ : Algebra C X.Bₛ]
  /-- The factorization of the localization map through the coordinate ring is a tower. -/
  [isScalarTowerBCBₛ : IsScalarTower X.B C X.Bₛ]
  /-- The module extending `N` over the affine open. -/
  N' : Type u₄
  /-- The additive group underlying the spreadout module. -/
  [addCommGroupN' : AddCommGroup N']
  /-- The module structure of the spreadout module over the coordinate ring. -/
  [moduleCN' : Module C N']
  /-- The restricted `B`-module structure on the spreadout module. -/
  [moduleBN' : Module X.B N']
  /-- The restricted `A`-module structure on the spreadout module. -/
  [moduleAN' : Module X.A N']
  /-- Restriction of scalars from `C` to `B` on the spreadout module is a tower. -/
  [isScalarTowerBCN' : IsScalarTower X.B C N']
  /-- Restriction of scalars from `C` to `A` on the spreadout module is a tower. -/
  [isScalarTowerACN' : IsScalarTower X.A C N']
  /-- The action of `C` on the localized module, through `toLocalization`. -/
  [moduleCN : Module C X.N]
  /-- Restriction of scalars from `Bₛ` to `C` on the localized module is a tower. -/
  [isScalarTowerCBₛN : IsScalarTower C X.Bₛ X.N]
  /-- Restriction of scalars from `C` to `B` on the localized module is a tower. -/
  [isScalarTowerBCN : IsScalarTower X.B C X.N]
  /-- Restriction of scalars from `C` to `A` on the localized module is a tower. -/
  [isScalarTowerACN : IsScalarTower X.A C X.N]
  /-- The spreadout module is finitely presented over the affine open. -/
  finitePresentation : Module.FinitePresentation C N'
  /-- The spreadout module is projective over the base ring. -/
  projective : Module.Projective X.A N'
  /-- The map identifying the localization of the spreadout module with `N`. -/
  localizationMap : N' →ₗ[C] X.N
  /-- The preceding map exhibits `N` as the localization at `S`. -/
  isLocalizedModule : IsLocalizedModule X.S (localizationMap.restrictScalars X.B)
  /-- The localization map is universally injective over `A`. -/
  universallyInjective :
    UniversallyInjectivePoly.{u₁, u₅} (localizationMap.restrictScalars X.A)

end AlgebraicGeometry
