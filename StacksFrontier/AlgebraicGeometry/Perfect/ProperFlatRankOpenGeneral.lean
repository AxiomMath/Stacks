module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpen
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.FibreEulerCharacteristic

/-!
# The open subscheme of Stacks Tag 0B9S, for an arbitrary morphism to the base

`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatRankOpen.lean` constructs, for `f : X ⟶ S`
proper of finite presentation and an `𝒪_X`-module `ℱ` of finite presentation flat over `S`, the
open subscheme `AlgebraicGeometry.ProperFlatRankOpen.rankOpen f ℱ i r` and proves its
characterising property for open immersions `T ⟶ S`. This file states the property for an
arbitrary morphism `g : T ⟶ S`.

## Main results

* `AlgebraicGeometry.ProperFlatRankOpen.factorsThrough_rankOpen_iff_of_isPullback`: for a
  cartesian square with base `g : T ⟶ S`, `g` factors through `rankOpen f ℱ i r` exactly when
  `Rf_{T,*}ℱ_T` is a finite locally free module of rank `r` placed in degree `i`.
* `AlgebraicGeometry.ProperFlatRankOpen.exists_opens_factorsThrough_iff`: the existence statement
  of [Stacks, Tag 0B9S].

Both theorems take two propositions as arguments: `hPerfBC`, the statement of
[Stacks, Tag 0A1H] (perfectness of `Rf_*(E ⊗^L G)` and its base change), and
`hRankOpen`, description (2) of [Stacks, Tag 0BDK] for an arbitrary morphism. Neither is
registered here.

## References

* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (derivedPushforwardModule)
open Stacks.SchemeCohomology (hom)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryIsoOfNatIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatRankOpen

variable {X S : Scheme.{u}}

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
/-- **The characterising property of the open subscheme of [Stacks, Tag 0B9S], for an arbitrary
morphism `T ⟶ S`**. The theorem takes two propositions as arguments: `_hPerfBC`, the
statement of [Stacks, Tag 0A1H], and `hRankOpen`, description (2) of [Stacks, Tag 0BDK]
for arbitrary morphisms. Let `f : X ⟶ S` be proper of finite
presentation, let `ℱ` be an `𝒪_X`-module of finite presentation, flat over `S`, and fix `i` and
`r`. For every cartesian square with base `g : T ⟶ S`, the morphism `g` factors through
`rankOpen f ℱ i r` exactly when `Rf_{T,*}ℱ_T` is isomorphic to a finite locally free module of
rank `r` placed in degree `i`.

`hRankOpen` is description (2) of [Stacks, Tag 0BDK] at full generality — every
scheme, every perfect `E`, every `i` and `r`, every morphism — for the open subscheme
`AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen` that the base already carries with
description (1) and with description (2) for open immersions
(`AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff`). The proof is the
source's: `Rf_*ℱ` is perfect and `Lg^*Rf_*ℱ ≅ Rf_{T,*}ℱ_T`, both by [Stacks, Tag 0B91]
(`AlgebraicGeometry.ProperFlatBaseChange.isPerfect_derivedPushforward_module`,
`AlgebraicGeometry.ProperFlatBaseChange.nonempty_derivedPullback_derivedPushforward_module_iso`),
and then [Stacks, Tag 0BDK] at `Rf_*ℱ`. The rank is a natural number, as for
`factorsThrough_rankOpen_iff`. -/
theorem factorsThrough_rankOpen_iff_of_isPullback
    (_hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) (r : ℕ)
    {T XT : Scheme.{u}} (g : T ⟶ S) (fT : XT ⟶ T) (g' : XT ⟶ X)
    (hsq : IsPullback g' fT f g) :
    (∃ h : T ⟶ (rankOpen f F i r).toScheme, h ≫ (rankOpen f F i r).ι = g) ↔
      ∃ M : T.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty (derivedPushforwardModule fT ((Scheme.Modules.pullback g').obj F) ≅
            (DerivedCategory.singleFunctor T.Modules i).obj M) := by
  obtain ⟨e⟩ := ProperFlatBaseChange.nonempty_derivedPullback_derivedPushforward_module_iso
    f g fT g' hsq hf hproper F hfp hflat
  rw [hRankOpen (derivedPushforwardModule f F)
    (ProperFlatBaseChange.isPerfect_derivedPushforward_module f hf hproper F hfp hflat)
    i r g]
  exact exists_congr fun M => and_congr_right fun _ =>
    ⟨fun hw => ⟨e.symm ≪≫ hw.some⟩, fun hw => ⟨e ≪≫ hw.some⟩⟩

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
/-- **[Stacks, Tag 0B9S].** The theorem takes two propositions as arguments: `hPerfBC`,
the statement of [Stacks, Tag 0A1H], and `hRankOpen`, description (2) of
[Stacks, Tag 0BDK] for arbitrary morphisms. Let `f : X ⟶ S` be a proper morphism of
finite presentation and let `ℱ` be an `𝒪_X`-module of finite presentation, flat over `S`. Fix `i`
and `r`. There exists an open subscheme `U ⊆ S` such that a morphism `g : T ⟶ S` factors through
`U` if and only if `Rf_{T,*}ℱ_T` is isomorphic to a finite locally free module of rank `r`
placed in degree `i`; here `f_T : X ×_S T ⟶ T` is the base change and `ℱ_T` the pullback of `ℱ`
to `X ×_S T`. The open subscheme is `rankOpen f ℱ i r`; see
`factorsThrough_rankOpen_iff_of_isPullback`. The rank is a natural number, as for
`factorsThrough_rankOpen_iff`. -/
theorem exists_opens_factorsThrough_iff
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) (r : ℕ) :
    ∃ U : S.Opens, ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ U.toScheme, h ≫ U.ι = g) ↔
        ∃ M : T.Modules,
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
            Nonempty (derivedPushforwardModule (pullback.snd f g)
                ((Scheme.Modules.pullback (pullback.fst f g)).obj F) ≅
              (DerivedCategory.singleFunctor T.Modules i).obj M) :=
  ⟨rankOpen f F i r, fun g => factorsThrough_rankOpen_iff_of_isPullback hPerfBC
    hRankOpen f hf hproper F hfp hflat i r g (pullback.snd f g) (pullback.fst f g)
    (IsPullback.of_hasPullback f g)⟩

end AlgebraicGeometry.ProperFlatRankOpen

end
