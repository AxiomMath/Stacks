module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDevissage
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction

/-!
# Closed support is preserved by derived direct image from an open subspace

Let `X` be a ringed space, `U ⊆ X` an open subspace, `j : U ⟶ X` the inclusion and `T ⊆ X` an
arbitrary **closed** subset. If every cohomology sheaf of an object `E` of `D(𝒪_U)` is supported
on the preimage of `T` in `U`, then every cohomology sheaf of `Rj_* E` is supported on `T`.

## Main results

* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_of_isClosed` is the statement
  above, for an arbitrary right derived functor of `j_*` presented by its own unit.
* `Stacks.DerivedQCoh.exists_isPullback_of_preimage` records that an open subspace of an open
  subspace, cut out as the preimage of an open of the ambient space, is the fibre product of the
  two open immersions — the Cartesian square that [Stacks, Tag 08FE] consumes.

## Implementation notes

The library's form of [Stacks, Tag 08DF] in
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean`
identifies `Rj_*E` with the extension by zero of `E` and so reads off the support, but only
when `T ⊆ U`; the Mayer--Vietoris cover `X = U ∪ (X \ T)` it runs on is a cover only then. For
an arbitrary closed `T` the support is instead read off from base change along `X \ T`: the
square cut out by `U ∩ (X \ T)` is Cartesian, so the restriction of `Rj_*E` to `X \ T` is the
derived direct image of the restriction of `E`, which vanishes.

Only the *underived* half of [Stacks, Tag 08FE] is used, namely
`Stacks.Cohomology.pushforwardRestrictMap_isIso`. Choosing a K-injective representative `I` of
`E` first makes the derived comparison unnecessary: `Rj_*E` is then represented by `j_*I`, the
restriction of `I` to `U ∩ (X \ T)` is K-injective and acyclic and hence null-homotopic, and an
additive functor carries a null-homotopic complex to a null-homotopic one. This is the same
device as `isZero_Q_restrictPush_of_supported` in the 08DF file, and it is what removes the need
for a second derived functor on `U ∩ (X \ T)` together with its additivity.

The Cartesian square is produced here rather than imported: the scheme-level
`AlgebraicGeometry.isPullback_morphismRestrict` does not apply to a ringed space, and the
ringed-space squares already available
(`Stacks.Cohomology.ClosedSupportPerfect`, through `IsPullback.of_vert_isIso_mono`) have an
isomorphism for one leg, which forces the smaller open to lie inside `U` — exactly the
hypothesis being removed. `exists_isPullback_of_preimage` instead verifies the universal
property directly, by lifting along an open immersion.

Everything is stated at the locally small derived category of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`: no `HasDerivedCategory` binder occurs,
so instance search supplies `SheafOfModules.hasDerivedCategory`, which is the model the
dévissage of `StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean` is stated at.
The structure sheaf of the open subspace is written
`ExtensionByZeroModules.resRing U (structureSheafRing X)` in the statement,
the spelling 08DF and the dévissage use, and
`structureSheafRing (X.restrict U.isOpenEmbedding)` in the proof, the
spelling the ringed-space pushforward and pullback use; the two are definitionally equal at
default transparency and the identification is spent once, at the application of the private
base-change lemma.

## References

* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

-- `AlgebraicGeometry` also declares a `CohomologySupportedOn`; this file means the one of
-- `Stacks.Cohomology.PushforwardRestriction`, opened selectively below, so the other is hidden.
open AlgebraicGeometry hiding CohomologySupportedOn
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology
open Stacks.Cohomology.PushforwardRestriction (CohomologySupportedOn
  isZero_derived_restrict_compl_of_supported)

universe u

namespace Stacks.DerivedQCoh

/-! ### Open subspaces of a ringed space form Cartesian squares -/

/-- **The universal property of an open immersion of ringed spaces.** A morphism whose
topological image lies in the image of an open immersion factors through it. This is the
`SheafedSpace`-level form of `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`, obtained
from it because forgetting the sheaf condition is fully faithful. -/
private def openLift {A B C : RingedSpace.{u, u}} (f : A ⟶ C)
    [H : SheafedSpace.IsOpenImmersion f] (g : B ⟶ C)
    (hr : Set.range g.hom.base ⊆ Set.range f.hom.base) : B ⟶ A :=
  SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
    (PresheafedSpace.IsOpenImmersion.lift (hf := H) f.hom g.hom hr)

/-- The factorisation produced by `openLift` is a factorisation. -/
private theorem openLift_fac {A B C : RingedSpace.{u, u}} (f : A ⟶ C)
    [H : SheafedSpace.IsOpenImmersion f] (g : B ⟶ C)
    (hr : Set.range g.hom.base ⊆ Set.range f.hom.base) : openLift f g hr ≫ f = g := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  rw [Functor.map_comp]
  exact PresheafedSpace.IsOpenImmersion.lift_fac (hf := H) f.hom g.hom hr

/-- **A square of open immersions of ringed spaces in which the top arrow is the full preimage
of the bottom one is Cartesian.** The two vertical arrows `i` and `j` are open immersions, the
image of `i` is the whole preimage under `f` of the image of `j`, and the left arrow is the
factorisation of `i ≫ f` through `j`. A cone over `f` and `j` lands in that preimage, hence
factors through `i`, uniquely because `i` is a monomorphism. -/
private theorem isPullback_openLift {XX XU XV XW : RingedSpace.{u, u}}
    (f : XU ⟶ XX) (i : XW ⟶ XU) (j : XV ⟶ XX)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (hsub : Set.range (i ≫ f).hom.base ⊆ Set.range j.hom.base)
    (hfull : ∀ z : XU, f.hom.base z ∈ Set.range j.hom.base → z ∈ Set.range i.hom.base) :
    IsPullback i (openLift j (i ≫ f) hsub) f j := by
  have hcomm : i ≫ f = openLift j (i ≫ f) hsub ≫ j := (openLift_fac j (i ≫ f) hsub).symm
  have key : ∀ s : PullbackCone f j, Set.range s.fst.hom.base ⊆ Set.range i.hom.base := by
    rintro s _ ⟨z, rfl⟩
    refine hfull _ ⟨s.snd.hom.base z, ?_⟩
    simpa using (congrArg (fun q : s.pt ⟶ XX => q.hom.base z) s.condition).symm
  exact IsPullback.of_isLimit' ⟨hcomm⟩
    (PullbackCone.IsLimit.mk hcomm (fun s => openLift i s.fst (key s))
      (fun s => openLift_fac i s.fst (key s))
      (fun s => (cancel_mono j).1 (by
        rw [Category.assoc, ← hcomm, ← Category.assoc, openLift_fac i s.fst (key s), s.condition]))
      (fun s m hm1 _ => (cancel_mono i).1 (by rw [hm1, openLift_fac i s.fst (key s)])))

/-- **An open subspace of an open subspace which is cut out as a preimage is a fibre product.**
If `W ⊆ U` is the preimage in `U` of an open `V ⊆ X`, the square formed by the inclusions of
`W` into `U`, of `U` into `X` and of `V` into `X` is Cartesian in ringed spaces. This is the
input [Stacks, Tag 08FE] asks for. -/
theorem exists_isPullback_of_preimage (X : RingedSpace.{u, u}) (U V : Opens X)
    (W : Opens (X.restrict U.isOpenEmbedding))
    (hW : ∀ z : (X.restrict U.isOpenEmbedding).carrier,
      z ∈ W ↔ (X.ofRestrict U.isOpenEmbedding).hom.base z ∈ V) :
    ∃ g : (X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding ⟶
        X.restrict V.isOpenEmbedding,
      IsPullback ((X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding) g
        (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) := by
  have hrj : Set.range (X.ofRestrict V.isOpenEmbedding).hom.base = (V : Set X) :=
    Opens.set_range_inclusion' V
  have hri : Set.range
      ((X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding).hom.base =
      (W : Set (X.restrict U.isOpenEmbedding).carrier) := Opens.set_range_inclusion' W
  have hsub : Set.range
      (((X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding) ≫
        X.ofRestrict U.isOpenEmbedding).hom.base ⊆
      Set.range (X.ofRestrict V.isOpenEmbedding).hom.base := by
    rw [hrj]
    rintro x ⟨w, rfl⟩
    have hwW : ((X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding).hom.base w ∈ W := by
      rw [← SetLike.mem_coe, ← hri]
      exact ⟨w, rfl⟩
    have h2 := (hW _).1 hwW
    simp only [SheafedSpace.comp_hom_base, CategoryTheory.comp_apply]
    exact h2
  refine ⟨_, isPullback_openLift _ _ _ hsub (fun z hz => ?_)⟩
  rw [hri]
  rw [hrj] at hz
  exact (hW z).2 hz

/-- **A commutative square of ringed spaces whose top arrow exhausts the intersection of the two
images is Cartesian.** The right arrow `jU` and the top arrow `iV` are open immersions, and every
point of `XV` whose image lies in the image of `jU` is already in the image of `iV`; then the
square is a fibre product.

This is `Stacks.DerivedQCoh.isPullback_openLift` with the left arrow given rather than
constructed: the factorisation through an open immersion is unique, so any commutative square
with the stated range condition is the one that lemma builds. Unlike
`Stacks.DerivedQCoh.exists_isPullback_of_preimage` the two opens are presented by arbitrary open
immersions, which is what [Stacks, Tag 08DG] consumes -- there one of the two opens is the
spectrum of the sections over an affine open, not a subspace of the ambient space. -/
theorem isPullback_of_range {XX XU XV XW : RingedSpace.{u, u}} (jU : XU ⟶ XX) (jV : XV ⟶ XX)
    (iU : XW ⟶ XU) (iV : XW ⟶ XV) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion iV] (hcomm : iU ≫ jU = iV ≫ jV)
    (hfull : ∀ z : XV, jV.hom.base z ∈ Set.range jU.hom.base →
      z ∈ Set.range iV.hom.base) :
    IsPullback iU iV jU jV := by
  have hsub : Set.range (iV ≫ jV).hom.base ⊆ Set.range jU.hom.base := by
    rw [← hcomm]
    rintro x ⟨w, rfl⟩
    exact ⟨iU.hom.base w, by simp⟩
  have hpb := (isPullback_openLift jV iV jU hsub hfull).flip
  have heq : openLift jU (iV ≫ jV) hsub = iU :=
    (cancel_mono jU).1 (by rw [openLift_fac jU (iV ≫ jV) hsub, hcomm])
  rwa [heq] at hpb

/-! ### Restriction to an open subspace, in two spellings -/

/-- Pullback of modules along the inclusion of an open subspace is restriction: both are left
adjoint to the direct image. This is `Stacks.Cohomology.openInclusionModulePullbackIso` with the
restriction functor named as in [Stacks, Tag 08DF]. -/
private def modulePullbackRestrictIso (X : RingedSpace.{u, u}) (U : Opens X) :
    modulePullback (X.ofRestrict U.isOpenEmbedding) ≅ jStar U (structureSheafRing X) :=
  (openInclusionModulePullbackIso X U).symm

/-! ### Null-homotopic complexes -/

/-- **An acyclic K-injective complex is already zero in the homotopy category**, because its
identity is homotopic to zero. -/
private alias isZero_quotient_of_acyclic_isKInjective :=
  Stacks.Cohomology.PushforwardRestriction.isZero_homotopyCategory_of_acyclic_isKInjective

/-- **Direct image kills an acyclic K-injective complex.** Such a complex is null-homotopic, and
direct image is additive, so its image is null-homotopic too and vanishes in the derived
category. -/
private theorem isZero_Q_modulePushforward_of_isZero_Q {XW XV : RingedSpace.{u, u}}
    (g : XW ⟶ XV) (I : CochainComplex (SheafOfModules.{u} (structureSheafRing XW)) ℤ)
    [I.IsKInjective] (h : IsZero (DerivedCategory.Q.obj I)) :
    IsZero (DerivedCategory.Q.obj (((modulePushforward g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)) := by
  have hac : I.Acyclic := by
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (Functor.map_isZero (DerivedCategory.homologyFunctor _ n) h).of_iso
      ((DerivedCategory.homologyFunctorFactors _ n).app I).symm
  have hq := isZero_quotient_of_acyclic_isKInjective I hac
  have h1 : IsZero (((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := Functor.map_isZero _ hq
  have h2 : IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    h1.of_iso (((modulePushforward g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm
  exact (Functor.map_isZero DerivedCategory.Qh h2).of_iso
    ((DerivedCategory.quotientCompQhIso _).app _).symm

/-- **A right derived functor of direct image is computed by a K-injective representative.** The
unit of any right derived functor of `f_*` is invertible at a K-injective complex, so the value
of that functor at the class of `I` is the class of `f_*I`. -/
private def derivedPushforwardIsoQ {XU XX : RingedSpace.{u, u}} (f : XU ⟶ XX)
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing XU)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing XX)))
    (αj : (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing XU)) (ComplexShape.up ℤ)))
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing XU)) ℤ) (hI : I.IsKInjective) :
    Rj.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((modulePushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have := hRj
  have hα : IsIso (αj.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective XU)).2
      DerivedCategory.Qh Rj αj I hI
  exact (Rj.mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing XU))).app I)).symm ≪≫
    (asIso (αj.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso
      (((modulePushforward f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing XX))).app _

/-! ### Base change for a Cartesian square of open immersions -/

/-- **The vanishing half of [Stacks, Tag 08FE].** In a Cartesian square of ringed spaces whose
vertical arrows `i` and `j` are open immersions, if the restriction of `E` along `i` vanishes
then so does the restriction along `j` of any right derived direct image of `E` along `f`.

The two restriction functors are supplied as functors `RW` and `RV` identified with the abstract
pullbacks, so that the caller may use whichever spelling of restriction it has. -/
private theorem isZero_derivedRestrict_derivedPushforward {XX XU XV XW : RingedSpace.{u, u}}
    (f : XU ⟶ XX) (i : XW ⟶ XU) (j : XV ⟶ XX) (g : XW ⟶ XV)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (hsq : IsPullback i g f j)
    (RV : SheafOfModules.{u} (structureSheafRing XX) ⥤ SheafOfModules.{u} (structureSheafRing XV))
    (eV : modulePullback j ≅ RV)
    (hVa : RV.Additive) (hVl : PreservesFiniteLimits RV) (hVc : PreservesFiniteColimits RV)
    (RW : SheafOfModules.{u} (structureSheafRing XU) ⥤ SheafOfModules.{u} (structureSheafRing XW))
    (eW : modulePullback i ≅ RW)
    (hWa : RW.Additive) (hWl : PreservesFiniteLimits RW) (hWc : PreservesFiniteColimits RW)
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing XU)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing XX)))
    (αj : (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing XU)) (ComplexShape.up ℤ)))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing XU)))
    (hE : IsZero (RW.mapDerivedCategory.obj E)) :
    IsZero (RV.mapDerivedCategory.obj (Rj.obj E)) := by
  obtain ⟨I, φ, hKI, hφ⟩ := DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective XU
    (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := SheafOfModules.{u} (structureSheafRing XU)) φ).2 hφ
  have e : E ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫ asIso (DerivedCategory.Q.map φ)
  -- the restriction of `I` to `XW` is acyclic
  have h0 : IsZero (RW.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) :=
    hE.of_iso (RW.mapDerivedCategory.mapIso e).symm
  have h1 : IsZero (DerivedCategory.Q.obj
      ((RW.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    h0.of_iso (RW.mapDerivedCategoryFactors.app I).symm
  have h2 : IsZero (DerivedCategory.Q.obj
      (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    h1.of_iso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex eW (ComplexShape.up ℤ)).app I))
  -- hence its direct image along `g` is acyclic, being K-injective and acyclic
  have hKIW : CochainComplex.IsKInjective
      (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    openImmersionModulePullback_preservesKInjective i I
  have h3 : IsZero (DerivedCategory.Q.obj
      (((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    isZero_Q_modulePushforward_of_isZero_Q g _ h2
  -- base change identifies it with the restriction of `f_*I` to `XV`
  have hbc : IsIso (pushforwardRestrictMap f i j g hsq.w) :=
    pushforwardRestrictMap_isIso f i j g hsq
  have ebc : modulePushforward f ⋙ modulePullback j ≅ modulePullback i ⋙ modulePushforward g :=
    asIso (pushforwardRestrictMap f i j g hsq.w)
  have h4 : IsZero (DerivedCategory.Q.obj
      ((RV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    h3.of_iso <| DerivedCategory.Q.mapIso <|
      ((NatIso.mapHomologicalComplex eV (ComplexShape.up ℤ)).app _).symm ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (modulePushforward f ⋙ modulePullback j)) (ComplexShape.up ℤ)).app I ≪≫
      (NatIso.mapHomologicalComplex ebc (ComplexShape.up ℤ)).app I ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (modulePullback i ⋙ modulePushforward g)) (ComplexShape.up ℤ)).app I).symm
  have h5 : IsZero (RV.mapDerivedCategory.obj (DerivedCategory.Q.obj
      (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    h4.of_iso (RV.mapDerivedCategoryFactors.app _)
  exact h5.of_iso (RV.mapDerivedCategory.mapIso
    (Rj.mapIso e ≪≫ derivedPushforwardIsoQ f Rj αj hRj I hKI))

/-- **The vanishing half of [Stacks, Tag 08FE].** In a Cartesian square of ringed spaces whose
vertical arrows `i` and `j` are open immersions, if the restriction of `E` along `i` vanishes
then so does the restriction along `j` of any right derived direct image of `E` along `f`.

The two restriction functors are supplied as functors `RW` and `RV` identified with the abstract
pullbacks, so that the caller may use whichever spelling of restriction it has. -/
alias isZero_derivedRestrict_derivedPushforward_of_isPullback := isZero_derivedRestrict_derivedPushforward

/-! ### Closed support and derived direct image from an open -/

/-- **Closed support is preserved by derived direct image from an open subspace, for an
arbitrary closed subset of the ambient space.** Let `U` be an open subspace of a ringed space
`X`, let `T ⊆ X` be closed, and let `Rj` be any right derived functor of the direct image
`j_* : Mod(𝒪_U) ⥤ Mod(𝒪_X)`, presented by its unit `αj`. If every cohomology sheaf of `E` has
vanishing stalks outside the preimage of `T` in `U`, then every cohomology sheaf of `Rj E` has
vanishing stalks outside `T`.

This is the form of [Stacks, Tag 08DF] that the dévissage of [Stacks, Tag 09T6] consumes. The
library's parts (1) and (2) of 08DF assume `T ⊆ U`; here `T` is an arbitrary closed subset, and the
support is read off from base change along the open complement `X \ T` instead of from the
Mayer--Vietoris cover `X = U ∪ (X \ T)`, which is a cover only under that assumption.

The additivity of `j_*` and the right-derived-functor property of `Rj` are explicit arguments
rather than instances: both statements mention the structure sheaf of the open subspace, whose
`ExtensionByZeroModules.resRing` and `structureSheafRing` spellings are equal
only at default transparency, so instance search does not bridge them and the identification is
instead made once, by the defeq check of an application. -/
theorem cohomologySupportedOn_derivedPushforward_of_isClosed (X : RingedSpace.{u, u})
    (U : Opens X) (T : Set X) (hT : IsClosed T)
    (hjPush : (jPush U (structureSheafRing X)).Additive)
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (αj : (jPush U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U (structureSheafRing X)))
        (ComplexShape.up ℤ)))
    (E : DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X))))
    (hE : CohomologySupportedOn (resRing U (structureSheafRing X))
      ((fun x : Usp U ↦ x.1) ⁻¹' T) E) :
    CohomologySupportedOn (structureSheafRing X) T (Rj.obj E) := by
  have := hjPush
  have hS : IsClosed ((fun x : Usp U ↦ x.1) ⁻¹' T) := hT.preimage continuous_subtype_val
  obtain ⟨hVa, hVl, hVc⟩ :=
    jStar_additive_and_exact (structureSheafRing X) ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨hWa, hWl, hWc⟩ := jStar_additive_and_exact (resRing U (structureSheafRing X))
    ⟨((fun x : Usp U ↦ x.1) ⁻¹' T)ᶜ, hS.isOpen_compl⟩
  obtain ⟨g, hsq⟩ := exists_isPullback_of_preimage X U ⟨Tᶜ, hT.isOpen_compl⟩
    ⟨((fun x : Usp U ↦ x.1) ⁻¹' T)ᶜ, hS.isOpen_compl⟩ (fun z => Iff.rfl)
  have hzero : IsZero ((jStar ⟨Tᶜ, hT.isOpen_compl⟩ (structureSheafRing X)).mapDerivedCategory.obj
      (Rj.obj E)) :=
    isZero_derivedRestrict_derivedPushforward (X.ofRestrict U.isOpenEmbedding) _ _ g hsq
      (jStar ⟨Tᶜ, hT.isOpen_compl⟩ (structureSheafRing X))
      (modulePullbackRestrictIso X ⟨Tᶜ, hT.isOpen_compl⟩) hVa hVl hVc
      (jStar ⟨((fun x : Usp U ↦ x.1) ⁻¹' T)ᶜ, hS.isOpen_compl⟩ (resRing U (structureSheafRing X)))
      (modulePullbackRestrictIso (X.restrict U.isOpenEmbedding)
        ⟨((fun x : Usp U ↦ x.1) ⁻¹' T)ᶜ, hS.isOpen_compl⟩) hWa hWl hWc
      Rj αj hRj E
      (isZero_derived_restrict_compl_of_supported (resRing U (structureSheafRing X))
        ((fun x : Usp U ↦ x.1) ⁻¹' T) hS E hE)
  refine cohomologySupportedOn_mono (structureSheafRing X) (fun x hx => ?_)
    (cohomologySupportedOn_compl_of_isZero_restrict (structureSheafRing X) ⟨Tᶜ, hT.isOpen_compl⟩
      (Rj.obj E) hzero)
  simpa using hx

end Stacks.DerivedQCoh

end
