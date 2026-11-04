module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiPushforwardAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange

/-!
# The small Zariski higher direct images of an associated module

Let `f : T ⟶ S` be a morphism of schemes of a big Zariski site and let `𝓕 ↦ 𝓕^a` be the
associated-module functor of [Stacks, Tag 03DU] (4) at `τ = Zariski`.  This file proves the
Zariski half of [Stacks, Tag 071N]:

`R ⁱ f_{small, *}(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`

for every degree `i`, naturally in `𝓕`, where `f_{small, *}` is the direct image along the
morphism of ringed sites `f_small` of [Stacks, Tag 070R] (2).

## Main definitions

* `AlgebraicGeometry.SmallZariski.pushforwardAssociatedModuleSquareIso`: the degree-zero
  comparison as an isomorphism of *functors*, which is what the derived statement consumes.
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModuleIso`: **the comparison in
  every degree.**
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIso`: the same comparison
  in the `ℤ`-indexed derived-category convention `CategoryTheory.Functor.rightDerivedPlus`.
* `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusObjIso`: that comparison
  **at a single module**, which is the shape the tag's statement is read in, together with
  `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusObjIso_naturality`.

## Implementation notes

The whole argument is that at `τ = Zariski` the associated-module adjunction is an adjoint
equivalence — `AlgebraicGeometry.SmallZariski.isEquivalence_associatedModule`, from Tag 03FG —
so `𝓕 ↦ 𝓕^a` is exact and carries injective objects to injective objects, the latter by
Mathlib's instance for an equivalence.  Base change for right derived functors across a square
of additive functors whose horizontal legs are exact and whose left leg preserves injectives is
`StacksTag03LR.rightDerivedBaseChangeIso`, and the square it consumes is the degree-zero
comparison read as an isomorphism of functors.

`AlgebraicGeometry.SmallZariski.pushforwardAssociatedModuleIso` is the degree-zero comparison at
one module; the functor-level form is not a second proof of it but the same three isomorphisms
composed before evaluation, so that the result is natural in `𝓕` by construction.  The three are
the counit of the adjunction of `S_Zar`, the square of direct images
`AlgebraicGeometry.SmallZariski.restrictModulePushforwardSquareIso` — already an isomorphism of
functors — and the unit of the adjunction of `T_Zar`.  Associativity of functor composition and
the two unitors hold definitionally here, so no transport along them appears.

**No hypothesis is imposed on `f` or on `𝓕`.**  [Stacks, Tag 071N] states its comparison for a
quasi-compact quasi-separated `f` and a quasi-coherent `𝓕`, because the étale half needs both;
the Zariski half needs neither, the adjunction being an equivalence at every object.  The
statement below is therefore stronger than the tag asks on this side.

The degree runs over `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, the convention `StacksTag03LR.rightDerivedBaseChangeIso`
is stated in.

**The two indexings.**  [Stacks, Tag 071N] is read in the `ℤ`-indexed derived-category
convention `CategoryTheory.Functor.rightDerivedPlus` of [Stacks, Tag 05U4], at a degree `i : ℕ`
cast to `ℤ`.  Nothing has to be re-derived to get there: the base-change statement is available
in that convention as `StacksTag03LR.rightDerivedPlusBaseChangeIso`, which is the
injective-resolution one conjugated on both sides by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard` — the `ℕ`/`ℤ` comparison of
right derived functors, equivalently `Stacks.DerivedIndexing.rightDerivedIso`.  So
`higherDirectImageAssociatedModulePlusIso` is the *same* square fed to that variant, not a
transport of `higherDirectImageAssociatedModuleIso`, and the module-level
`higherDirectImageAssociatedModulePlusObjIso` is its component.  The `HasDerivedCategory`
instances needed to speak of `rightDerivedPlus` at all are left free, as in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedConservativity.lean`;
`CategoryTheory.HasDerivedCategory.standard` is one choice of them.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 05U4](https://stacks.math.columbia.edu/tag/05U4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w₁ w₂ w₃ w₄

-- With the module-universe-`max u v r w` instances of
-- `StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules` in the import
-- closure, instance search for `Abelian` on the modules at module universe `u` commits to them
-- and then fails on the universe constraint. The priority raise is the one documented in
-- `StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean`; it is
-- `local`, so no global instance is declared.
attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallZariski

/-! ### The abelian structure on modules over the small Zariski site -/

section Abelian

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Abelian presheaves on the small Zariski site of `S` sheafify.**  The site is essentially
small, so this is `AlgebraicGeometry.hasSheafifyEssentiallySmallSite`.
`AlgebraicGeometry.SmallZariski.hasWeakSheafify_smallZariski` proves the weak form from exactly
this, inside its own proof; the strong form is what makes modules over the structure sheaf
abelian, so it is recorded. -/
public instance hasSheafify_smallZariski :
    HasSheafify (SmallZariski.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- **Modules over the structure sheaf of the small Zariski site have enough injectives.**
Restriction to the opens of the space is an equivalence onto the `𝒪_S`-modules of the scheme
(Tag 03FG), which have enough injectives, and enough injectives transport along an
equivalence. -/
public noncomputable instance enoughInjectives_smallZariskiModules :
    EnoughInjectives (SheafOfModules.{u} (structureSheaf B S hS)) :=
  EnoughInjectives.of_equivalence (restrictModule B S hS)

/-- Restriction to the opens of the space is additive, being a direct image of sheaves of
modules. -/
public instance restrictModule_additive : (restrictModule B S hS).Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- The associated-module functor of the small Zariski site is additive, being a left adjoint of
an additive functor. -/
public instance associatedModule_additive : (associatedModule B S hS).Additive :=
  (associatedModuleAdjunction B S hS).left_adjoint_additive

end Abelian

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- The direct image along `f_small` is additive, being a direct image of sheaves of modules
along a continuous functor. -/
public instance pushforward_structureMapRing_additive :
    (SheafOfModules.pushforward.{u} (structureMapRing B f)).Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- The unit of the associated-module adjunction of the small Zariski site is an isomorphism of
functors, not merely at each object. -/
public instance isIso_unit_associatedModuleAdjunction' :
    IsIso (associatedModuleAdjunction B S.1 S.property).unit :=
  NatIso.isIso_of_isIso_app _

/-- The counit of the associated-module adjunction of the small Zariski site is an isomorphism
of functors. -/
public instance isIso_counit_associatedModuleAdjunction' :
    IsIso (associatedModuleAdjunction B S.1 S.property).counit :=
  NatIso.isIso_of_isIso_app _

/-- **The degree-zero comparison `f_{small, *}(𝓕^a) ≅ (f_* 𝓕)^a` as an isomorphism of
functors.**  This is the square of additive functors that the derived statement consumes: the
counit of the adjunction of `S_Zar`, the square of direct images
`AlgebraicGeometry.SmallZariski.restrictModulePushforwardSquareIso`, and the unit of the
adjunction of `T_Zar`. -/
public noncomputable def pushforwardAssociatedModuleSquareIso :
    associatedModule B T.1 T.property ⋙
        SheafOfModules.pushforward.{u} (structureMapRing B f) ≅
      Scheme.Modules.pushforward (schemeHom B f) ⋙ associatedModule B S.1 S.property :=
  Functor.isoWhiskerLeft
      (associatedModule B T.1 T.property ⋙
        SheafOfModules.pushforward.{u} (structureMapRing B f))
      (asIso (associatedModuleAdjunction B S.1 S.property).counit).symm ≪≫
    Functor.isoWhiskerLeft (associatedModule B T.1 T.property)
      (Functor.isoWhiskerRight (restrictModulePushforwardSquareIso B f)
        (associatedModule B S.1 S.property)) ≪≫
    Functor.isoWhiskerRight
      (asIso (associatedModuleAdjunction B T.1 T.property).unit).symm
      (Scheme.Modules.pushforward (schemeHom B f) ⋙ associatedModule B S.1 S.property)

/-- **The Zariski half of [Stacks, Tag 071N].**  For a morphism `f : T ⟶ S` of schemes of a big
Zariski site and every degree `i`, the `i`-th higher direct image along `f_small` of the
associated module of an `𝒪_T`-module is the associated module of the `i`-th higher direct image
along `f`:

`R ⁱ f_{small, *}(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`,

naturally in `𝓕`.

No hypothesis is placed on `f` or on `𝓕`: at `τ = Zariski` the associated-module functor is an
equivalence, hence exact and injective-preserving, so base change for right derived functors
applies to the degree-zero square with nothing further assumed. -/
public noncomputable def higherDirectImageAssociatedModuleIso (i : ℕ) :
    associatedModule B T.1 T.property ⋙
        (SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerived i ≅
      (Scheme.Modules.pushforward (schemeHom B f)).rightDerived i ⋙
        associatedModule B S.1 S.property :=
  StacksTag03LR.rightDerivedBaseChangeIso
    (associatedModule B T.1 T.property)
    (Scheme.Modules.pushforward (schemeHom B f))
    (SheafOfModules.pushforward.{u} (structureMapRing B f))
    (associatedModule B S.1 S.property)
    (pushforwardAssociatedModuleSquareIso B f) i

/-! ### The derived-category convention -/

section DerivedPlus

variable [HasDerivedCategory.{w₁} T.1.Modules]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B T.1 T.property))]
  [HasDerivedCategory.{w₃} S.1.Modules]
  [HasDerivedCategory.{w₄} (SheafOfModules.{u} (structureSheaf B S.1 S.property))]

/-- **The Zariski half of [Stacks, Tag 071N], in the `ℤ`-indexed derived-category convention.**
For a morphism `f : T ⟶ S` of schemes of a big Zariski site and every degree `i : ℕ`,

`R ⁱ f_{small, *}(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`,

naturally in `𝓕`, with the higher right derived functors taken as
`CategoryTheory.Functor.rightDerivedPlus` in degree `(i : ℤ)` — the convention
[Stacks, Tag 05U4] and the statement of [Stacks, Tag 071N] use.

This is `StacksTag03LR.rightDerivedPlusBaseChangeIso` applied to the degree-zero square
`AlgebraicGeometry.SmallZariski.pushforwardAssociatedModuleSquareIso`, exactly as
`AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModuleIso` is the
injective-resolution variant applied to the same square.  No hypothesis is placed on `f` or on
`𝓕`, for the reason recorded in the module documentation. -/
public noncomputable def higherDirectImageAssociatedModulePlusIso (i : ℕ) :
    associatedModule B T.1 T.property ⋙
        (SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus (i : ℤ) ≅
      (Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus (i : ℤ) ⋙
        associatedModule B S.1 S.property :=
  StacksTag03LR.rightDerivedPlusBaseChangeIso
    (associatedModule B T.1 T.property)
    (Scheme.Modules.pushforward (schemeHom B f))
    (SheafOfModules.pushforward.{u} (structureMapRing B f))
    (associatedModule B S.1 S.property)
    (pushforwardAssociatedModuleSquareIso B f) i

/-- **The Zariski half of [Stacks, Tag 071N] at one module.**  For an `𝒪_T`-module `𝓕` and a
degree `i : ℕ`, the `i`-th higher direct image along `f_small` of `𝓕^a` is the associated module
of the `i`-th higher direct image of `𝓕` along `f`:

`(R ⁱ f_{small, *})(𝓕^a) ≅ (R ⁱ f_* 𝓕)^a`,

in the `ℤ`-indexed convention.  This is the component at `𝓕` of
`AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusIso`, so its naturality in
`𝓕` is `AlgebraicGeometry.SmallZariski.higherDirectImageAssociatedModulePlusObjIso_naturality`.

[Stacks, Tag 071N] asks for this with `f` quasi-compact and quasi-separated and `𝓕`
quasi-coherent; neither is needed on the Zariski side, so neither is assumed. -/
public noncomputable def higherDirectImageAssociatedModulePlusObjIso (i : ℕ) (𝓕 : T.1.Modules) :
    ((SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus (i : ℤ)).obj
        ((associatedModule B T.1 T.property).obj 𝓕) ≅
      (associatedModule B S.1 S.property).obj
        (((Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus (i : ℤ)).obj 𝓕) :=
  (higherDirectImageAssociatedModulePlusIso B f i).app 𝓕

/-- **Naturality of the Zariski comparison of [Stacks, Tag 071N] in the module.**  The
comparison commutes with the associated module of every morphism `α : 𝓕 ⟶ 𝓖` of
`𝒪_T`-modules. -/
public theorem higherDirectImageAssociatedModulePlusObjIso_naturality (i : ℕ)
    {𝓕 𝓖 : T.1.Modules} (α : 𝓕 ⟶ 𝓖) :
    ((SheafOfModules.pushforward.{u} (structureMapRing B f)).rightDerivedPlus (i : ℤ)).map
          ((associatedModule B T.1 T.property).map α) ≫
        (higherDirectImageAssociatedModulePlusObjIso B f i 𝓖).hom =
      (higherDirectImageAssociatedModulePlusObjIso B f i 𝓕).hom ≫
        (associatedModule B S.1 S.property).map
          (((Scheme.Modules.pushforward (schemeHom B f)).rightDerivedPlus (i : ℤ)).map α) :=
  (higherDirectImageAssociatedModulePlusIso B f i).hom.naturality α

end DerivedPlus

end AlgebraicGeometry.SmallZariski

end
