module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyDegreewise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two spellings of the local cohomology sheaves `ℋ ⁿ_Z`, and 0G74 (2) in the second one

Let `Z` be a closed subset of a ringed space `X`. The local cohomology sheaves of `𝒪_X`-modules
along `Z` occur in this library in two spellings which, before this file, no declaration related:

* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctor X Z hZ n`, for `n : ℕ`,
  Mathlib's classical right derived functor `Rⁿ H_Z` computed from an injective resolution. This
  is the spelling of [Stacks, Tag 0G74] part (2) as the library has it degreewise, namely
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso`.
* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplex X Z hZ c K`, the degree-`c`
  cohomology sheaf of `RH_Z(K)` for `K` in the unbounded derived category. Applied to a module
  placed in degree `0` this is the spelling in which the target of
  `AlgebraicGeometry.Scheme.Hom.gysinMap` is written, by way of
  `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`.

This file identifies the two, naturally in the module and in each degree, and transports
[Stacks, Tag 0G74] part (2) across the identification. The point of the transport is that
`ℋ ᶜ_Z` in the Gysin map's spelling then acts on a morphism of the underlying abelian sheaves —
a morphism which need not be `𝒪_X`-linear, a de Rham differential being the case of interest.
That is step (1) of the proof of [Stacks, Tag 0G85], the compatibility of the Gysin map of
[Stacks, Tag 0G83] with the de Rham differentials.

The identification itself is not new mathematics: `RH_Z` on the unbounded derived category *is*
a right derived functor of `H_Z`, with unit
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedUnit` — this is the
instance `derivedSupportedSectionsOnClosed_isRightDerivedFunctor` — so the general comparison
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` between `Hⁿ(Rw(ℱ[0]))` and
`Rⁿw(ℱ)` applies to it verbatim. All that was missing was the instantiation.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctor`: the
  `localCohomologySheafOfComplex` spelling of `ℋ ⁿ_Z` read as a functor of the coefficient
  module, in an arbitrary integer degree.
* `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed`, with its unit
  `derivedAbelianSupportedSectionsOnClosedUnit`: a canonical total right derived functor of
  abelian sections supported on `Z`, the abelian counterpart of
  `derivedSupportedSectionsOnClosed`. The library had none, which is why every earlier statement
  of [Stacks, Tag 0G74] part (2) quantified over one.

## Main results

* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctor_obj`: the functor
  evaluates to `localCohomologySheafOfComplex` at the module placed in degree `0`, which is how
  the target of the Gysin map is spelled.
* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso`: **the bridge.**
  In degree `(n : ℤ)` for `n : ℕ`, the `localCohomologySheafOfComplex` spelling is the
  `ℕ`-indexed `localCohomologySheafFunctor`, naturally in the module. No hypotheses.
* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIsoInt`: the same
  bridge with the target spelled as the `ℤ`-indexed `localCohomologySheafFunctorInt`, the
  `CategoryTheory.Functor.rightDerivedPlus` model.
* `derivedAbelianSupportedSectionsOnClosed_isRightDerivedFunctor`, in the same namespace: the
  canonical abelian derived functor is a right derived functor of abelian supported sections.
* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso`: **[Stacks, Tag
  0G74] part (2) in the `localCohomologySheafOfComplex` spelling** — the underlying abelian sheaf
  of `ℋ ⁿ_Z(ℱ[0])`, taken as the degree-`n` cohomology sheaf of `RH_Z(ℱ[0])`, is the local
  cohomology sheaf `ℋ ⁿ_Z(ℱ_ab)` of the underlying abelian sheaf, naturally in `ℱ`. No
  hypotheses. `localCohomologySheafOfComplexForgetIsoOfRightDerived` is the same statement for
  an arbitrary abelian total right derived functor.
* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexAbelianMap`: **the action of
  `ℋ ⁿ_Z` in the Gysin map's spelling on a morphism of the underlying abelian sheaves**, which
  need not be `𝒪_X`-linear.
* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexAbelianMap_toSheaf_map`: that
  action agrees with the functorial one on a morphism that *is* `𝒪_X`-linear. This is what makes
  the previous definition the right notion rather than merely a map of the right type.

## Implementation notes

**Carried hypotheses: none, beyond `hZ : IsClosed Z`.** Every declaration in this file is
hypothesis-free, which took discharging two separate `IsRightDerivedFunctor` obligations.

* On the module side, `localCohomologySheafFunctorForgetIso` and the general comparison it rests
  on quantify over a total right derived functor of `H_Z` with its unit. Here they are
  instantiated at the canonical `derivedSupportedSectionsOnClosed` and
  `derivedSupportedSectionsOnClosedUnit`, whose `IsRightDerivedFunctor` instance
  (`derivedSupportedSectionsOnClosed_isRightDerivedFunctor`) holds unconditionally. The existence
  of K-injective resolutions is discharged by `Stacks.Cohomology.Localization.enoughKInjectives`,
  `Mod(𝒪_X)` being Grothendieck abelian.
* On the abelian side the library had no canonical choice at all, which is why
  `localCohomologySheafFunctorForgetIso` takes `RHab` and `aHab` as parameters with an instance.
  This file supplies one, `derivedAbelianSupportedSectionsOnClosed`, by the same
  `CategoryTheory.Functor.totalRightDerived` recipe as the module side; its
  `HasRightDerivedFunctor` hypothesis is not an instance in the library and is supplied from the
  lemma `hasRightDerivedFunctor_abelianSheaves` of
  `Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport`, abelian sheaves on a space being
  Grothendieck abelian. Both the functor and its unit supply it the same way, so they agree by
  proof irrelevance and the instance is proved by `infer_instance` after unfolding, exactly as
  `derivedSupportedSectionsOnClosed_isRightDerivedFunctor` is.

`localCohomologySheafOfComplexForgetIsoOfRightDerived` keeps the abelian derived functor
quantified and is therefore formally stronger; it is retained because it costs nothing, and the
hypothesis-free `localCohomologySheafOfComplexForgetIso` is its value at the canonical choice.

**What is not reached.** The following are *not* proved here and are not assumed:

* Nothing is said about the direct image along `i : Z ⟶ X`. The target of
  `AlgebraicGeometry.Scheme.Hom.gysinMap` is `i_*` of a `localCohomologySheafOfComplex`, whereas
  `localCohomologySheafOfComplexAbelianMap` below acts on the local cohomology sheaf itself, on
  `Z`, before any direct image. Pushing the abelian action forward along `i` — which needs the
  underlying abelian sheaf of the module-level `i_*` to be the abelian `i_*` — is a further step,
  not taken here.
* Nothing is said about the `supportCohomologySheafFunctor` spelling of
  `Stacks.Perfect.SupportedFraction`, the degree-`p` cohomology sheaf of `i_* R𝓗_T(ℱ[0])` with
  the direct image taken *before* the cohomology. That third spelling is related to the Gysin
  map's by `Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`; composing that
  with the bridge below would relate it to `localCohomologySheafFunctor`, but the composite is
  not formed here, this file deliberately not depending on the `AlgebraicGeometry` tree.
* The class map of [Stacks, Tag 0G7Q] is not made natural in a merely additive morphism, and
  nothing here mentions a class map, a Čech complex or a cokernel. Nothing in this file says that
  the comparison square of step (ii) of [Stacks, Tag 0G85] commutes; what it provides is the
  right-hand vertical arrow of that square, which the library previously lacked.
* The two constructions of the class map in the project,
  `Stacks.Perfect.SupportedFraction.supportedFractionSource` and
  `Stacks.Perfect.FractionClass.pushforwardFractionClass`, remain unidentified; that is
  independent of everything here.
* The docstring of `localCohomologySheafOfComplex` says the comparison of the unbounded model
  with `localCohomologySheafFunctorInt` "is only available as an existence statement". That is
  what `localCohomologySheafOfComplexFunctorIsoInt` supersedes, and by a different route: through
  the chosen injective resolution, on which the unit of `RH_Z` is invertible, rather than through
  the `Nonempty` comparisons of the two models used in
  `isZero_rightDerivedPlus_supportedSectionsOnClosedFunctor_modulePushforward`. That older
  statement is left untouched, as is its docstring.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (enoughKInjectives)
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport (hasRightDerivedFunctor_abelianSheaves)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-! ### The `localCohomologySheafOfComplex` spelling as a functor of the module -/

/-- **`ℱ ↦ ℋ ⁿ_Z(ℱ[0])` with the cohomology sheaf taken in the unbounded derived category**, as a
functor of the coefficient module: the module placed in degree `0`, its derived sections supported
on `Z`, and the degree-`n` cohomology sheaf of the result.

This is the order in which the target of `AlgebraicGeometry.Scheme.Hom.gysinMap` is written, and
`localCohomologySheafOfComplexFunctor_obj` records that the values are literally
`localCohomologySheafOfComplex`. The degree is an arbitrary integer, as it is there; the bridge to
the `ℕ`-indexed spelling is available for the degrees of the form `(n : ℤ)`. -/
public def localCohomologySheafOfComplexFunctor (n : ℤ) :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)) :=
  DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
    derivedSupportedSectionsOnClosed X Z hZ ⋙
      DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) n

/-- The functor evaluates to the degree-`n` local cohomology sheaf of the module placed in degree
`0`, which is the way the target of the Gysin map is spelled. -/
public theorem localCohomologySheafOfComplexFunctor_obj (n : ℤ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (localCohomologySheafOfComplexFunctor X Z hZ n).obj F =
      localCohomologySheafOfComplex X Z hZ n
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj F) :=
  rfl

/-! ### The bridge between the two spellings -/

/-- **The two spellings of `ℋ ⁿ_Z` agree, naturally in the coefficient module.** For `n : ℕ`, the
degree-`n` cohomology sheaf of `RH_Z(ℱ[0])` taken in the unbounded derived category is Mathlib's
classical right derived functor `Rⁿ H_Z` applied to `ℱ`.

`RH_Z` is a right derived functor of `H_Z` with unit `derivedSupportedSectionsOnClosedUnit` — the
instance `derivedSupportedSectionsOnClosed_isRightDerivedFunctor` — so this is the general
comparison `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` instantiated
there. Both sides are computed from the chosen injective resolution of `ℱ`: the right-hand side
by definition, the left-hand side because the extended resolution is K-injective, so the unit of
`RH_Z` is invertible on it. The existence of K-injective resolutions is discharged by
`Stacks.Cohomology.Localization.enoughKInjectives`, `Mod(𝒪_X)` being Grothendieck abelian; there
are no hypotheses beyond `hZ`. -/
public def localCohomologySheafOfComplexFunctorIso (n : ℕ) :
    localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ) ≅
      localCohomologySheafFunctor X Z hZ n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (supportedSectionsOnClosedFunctor X Z hZ)
    (derivedSupportedSectionsOnClosed X Z hZ)
    (derivedSupportedSectionsOnClosedUnit X Z hZ)
    Stacks.Cohomology.Localization.enoughKInjectives n

/-- **The unbounded model of `ℋ ⁿ_Z` agrees with the `rightDerivedPlus` model**, naturally in the
coefficient module: `localCohomologySheafOfComplexFunctorIso` followed by the comparison
`localCohomologySheafFunctorIntIso` of the `ℕ`-indexed `rightDerived` with the `ℤ`-indexed
`localCohomologySheafFunctorInt`. -/
public def localCohomologySheafOfComplexFunctorIsoInt (n : ℕ) :
    localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ) ≅
      localCohomologySheafFunctorInt X Z hZ (n : ℤ) :=
  localCohomologySheafOfComplexFunctorIso X Z hZ n ≪≫
    localCohomologySheafFunctorIntIso X Z hZ n

/-! ### A canonical total right derived functor of abelian supported sections -/

/-- **`RH_Z` on abelian sheaves**, the total right derived functor of the sections of an abelian
sheaf supported on the closed subset `Z`, along the localization of the homotopy category at the
quasi-isomorphisms. This is the abelian counterpart of `derivedSupportedSectionsOnClosed`,
constructed by the same `CategoryTheory.Functor.totalRightDerived` recipe.

The library had no such functor, which is why its statements of [Stacks, Tag 0G74] part (2)
quantify over one. The `HasRightDerivedFunctor` hypothesis of `totalRightDerived` is not an
instance and is supplied from the lemma `hasRightDerivedFunctor_abelianSheaves` of
`Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport`: abelian sheaves on a space are
Grothendieck abelian, so every complex of them admits a quasi-isomorphism into a K-injective
one. -/
@[sga "4 V 6.3" "special case"]
public def derivedAbelianSupportedSectionsOnClosed :
    DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) :=
  letI := hasRightDerivedFunctor_abelianSheaves X
    ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  Functor.totalRightDerived
    ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The canonical comparison from the sections of a complex of abelian sheaves supported on `Z` to
the value of `derivedAbelianSupportedSectionsOnClosed` on it: the derivation unit of that total
right derived functor, with the `HasRightDerivedFunctor` hypothesis supplied exactly as in the
functor itself. -/
public def derivedAbelianSupportedSectionsOnClosedUnit :
    (abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianSupportedSectionsOnClosed X Z hZ :=
  letI := hasRightDerivedFunctor_abelianSheaves X
    ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  Functor.totalRightDerivedUnit
    ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- **The comparison exhibits `derivedAbelianSupportedSectionsOnClosed` as the right derived
functor of abelian supported sections.** Both it and its unit are the `totalRightDerived` data of
the same functor, so the general instance applies after unfolding; the `HasRightDerivedFunctor`
hypothesis is supplied the same way in both, hence the two agree by proof irrelevance. -/
public instance derivedAbelianSupportedSectionsOnClosed_isRightDerivedFunctor :
    (derivedAbelianSupportedSectionsOnClosed X Z hZ).IsRightDerivedFunctor
      (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  dsimp only [derivedAbelianSupportedSectionsOnClosed,
    derivedAbelianSupportedSectionsOnClosedUnit]
  infer_instance

/-! ### Stacks 0G74 part (2) in the `localCohomologySheafOfComplex` spelling -/

section Forget

variable
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  [RHab.IsRightDerivedFunctor aHab
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- **[Stacks, Tag 0G74] part (2) in the spelling of the local cohomology sheaves that the Gysin
map uses**, for an arbitrary abelian total right derived functor `RHab` with unit `aHab`. For
`n : ℕ`, the degree-`n` cohomology sheaf of `RH_Z(ℱ[0])` has underlying abelian sheaf the
degree-`n` local cohomology sheaf `ℋ ⁿ_Z(ℱ_ab)` of the underlying abelian sheaf of `ℱ`, naturally
in `ℱ`.

This is `localCohomologySheafFunctorForgetIso`, which states the same thing for the `ℕ`-indexed
`localCohomologySheafFunctor`, carried across the bridge
`localCohomologySheafOfComplexFunctorIso`. The module-side total right derived functor of that
statement is instantiated at the canonical `derivedSupportedSectionsOnClosed` and so disappears.
`localCohomologySheafOfComplexForgetIso` is this at the canonical abelian choice, and has no
hypotheses at all. -/
public def localCohomologySheafOfComplexForgetIsoOfRightDerived (n : ℕ) :
    localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ) ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ n :=
  Functor.isoWhiskerRight (localCohomologySheafOfComplexFunctorIso X Z hZ n)
      (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))) ≪≫
    localCohomologySheafFunctorForgetIso X Z hZ RHab aHab
      (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ) n

end Forget

/-- **[Stacks, Tag 0G74] part (2) in the spelling of the local cohomology sheaves that the Gysin
map uses, with no hypotheses.** For `n : ℕ` and a sheaf of `𝒪_X`-modules `ℱ`, the degree-`n`
cohomology sheaf of `RH_Z(ℱ[0])` — the local cohomology sheaf in the spelling of
`localCohomologySheafOfComplex`, hence of `AlgebraicGeometry.Scheme.Hom.gysinMap` — has underlying
abelian sheaf the degree-`n` local cohomology sheaf `ℋ ⁿ_Z(ℱ_ab)` of the underlying abelian sheaf,
naturally in `ℱ`.

This is `localCohomologySheafOfComplexForgetIsoOfRightDerived` at the canonical abelian derived
functor `derivedAbelianSupportedSectionsOnClosed` supplied above. -/
public def localCohomologySheafOfComplexForgetIso (n : ℕ) :
    localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ) ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ n :=
  localCohomologySheafOfComplexForgetIsoOfRightDerived X Z hZ
    (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ) n

/-! ### Acting on a morphism which is not `𝒪_X`-linear -/

/-- **`ℋ ⁿ_Z` in the Gysin map's spelling, acting on a morphism of the underlying abelian
sheaves.** Given `𝒪_X`-modules `ℱ` and `𝒢` and a morphism `φ : ℱ_ab ⟶ 𝒢_ab` of the underlying
abelian sheaves — not required to be `𝒪_X`-linear — this is the induced morphism
`ℋ ⁿ_Z(ℱ[0])_ab ⟶ ℋ ⁿ_Z(𝒢[0])_ab`, with the local cohomology sheaves taken as degree-`n`
cohomology sheaves of `RH_Z(-[0])` in the unbounded derived category.

It is the abelian local cohomology functor `ℋ ⁿ_Z` of
`ClosedImmersionSheaves.localCohomologySheafFunctor` applied to `φ`, conjugated by the
identification `localCohomologySheafOfComplexForgetIso` of [Stacks, Tag 0G74] part (2) at `ℱ` and
at `𝒢`. This is what lets `ℋ ᶜ_Z` act on a de Rham differential, which is `f⁻¹𝒪_S`-linear but not
`𝒪_X`-linear and so has no image under the module-level functor at all; the differential itself is
nowhere mentioned here, the statement being about an arbitrary morphism of the underlying abelian
sheaves.

`localCohomologySheafOfComplexAbelianMap_toSheaf_map` checks that on a morphism which *is*
`𝒪_X`-linear this agrees with the functorial action. -/
public def localCohomologySheafOfComplexAbelianMap (n : ℕ)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (φ : (_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj F ⟶
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj G) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))).obj
        ((localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ)).obj F) ⟶
      (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))).obj
        ((localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ)).obj G) :=
  (localCohomologySheafOfComplexForgetIso X Z hZ n).hom.app F ≫
    (ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ n).map φ ≫
      (localCohomologySheafOfComplexForgetIso X Z hZ n).inv.app G

/-- **The abelian action extends the `𝒪_X`-linear one.** On the underlying morphism of abelian
sheaves of a morphism `ψ : ℱ ⟶ 𝒢` of `𝒪_X`-modules, the action of
`localCohomologySheafOfComplexAbelianMap` is the underlying morphism of abelian sheaves of the
functorial action of `ℋ ⁿ_Z` on `ψ`.

This is the naturality of the identification `localCohomologySheafOfComplexForgetIso` at `ψ`, and
nothing else. -/
public theorem localCohomologySheafOfComplexAbelianMap_toSheaf_map (n : ℕ)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (ψ : F ⟶ G) :
    localCohomologySheafOfComplexAbelianMap X Z hZ n
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).map ψ) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))).map
        ((localCohomologySheafOfComplexFunctor X Z hZ (n : ℤ)).map ψ) :=
  NatIso.naturality_2 (localCohomologySheafOfComplexForgetIso X Z hZ n) ψ

end Stacks.Cohomology.SupportedComplexes

end
