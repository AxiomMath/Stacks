module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback and quasi-coherence of cohomology

Let `f : X ⟶ Y` be a morphism of schemes. [Stacks, Tag 08DW] part (1) says that the derived
pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` carries complexes with quasi-coherent cohomology to complexes
with quasi-coherent cohomology — the hypothesis `hpull` of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`, and the
last input of the Stacks route to [Stacks, Tag 0A9E].

The general statements are proved from one named hypothesis, essential surjectivity of derived
sheafification, which is [Stacks, Tag 06Z0]:

  `hess : ∀ R : CommRingCat.{u}, (AlgebraicGeometry.derivedTilde R).EssSurj`.

The Stacks proof uses Tag 06Z0 in exactly this place and in no other. Everything else — the
reduction of the general case to the affine one, and the affine case given `hess` — is proved
unconditionally. The hypothesis is written out in the house style of
`AlgebraicGeometry.KFlatTilde`, as an argument of the three statements that need it, and
instance search discharges it from the equivalence
`AlgebraicGeometry.derivedTilde_isEquivalence` through Mathlib's
`CategoryTheory.Functor.IsEquivalence.essSurj`, giving part (1) outright as
`Stacks.Duality.isQuasicoherent_homology_derivedPullback'`.

## Why Tag 06Z0 is unavoidable here

The affine case is the content: for `φ : R ⟶ S` and `E ∈ D_QCoh(𝒪_{Spec R})` one has to know that
`E` is the derived sheafification of a complex of `R`-modules, because only then does the affine
comparison square of Tag 08DW part (2) — proved as
`AlgebraicGeometry.affinePullbackComparison` — apply and identify `L(Spec φ)^*E` with
`(S ⊗ᴸ_R M^•)~`, whose cohomology sheaves are quasi-coherent by construction. Nothing in the
statement of `E` itself produces such an `M^•`; that is Tag 06Z0.

Derived sheafification is an equivalence of triangulated categories,
`AlgebraicGeometry.derivedTilde_isEquivalence`, so the hypothesis holds: an equivalence is
essentially surjective, which instance search finds through
`CategoryTheory.Functor.IsEquivalence.essSurj`.

## Main definitions

* `Stacks.Duality.derivedPullbackCompIso` — the composition formula
  `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of [Stacks, Tag 0D5S] for schemes, read off
  `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, which takes the model
  binders.
* `Stacks.Duality.derivedPullbackMapDerivedIso` — for a morphism of schemes along which
  degreewise pullback is exact, the derived pullback *is* degreewise pullback, read off
  `AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`, which takes the model binders.
* `Stacks.Duality.homologyDerivedPullbackIso` — hence, for such a morphism of schemes,
  `f^*H^i(E) ≅ H^i(Lf^*E)`.

## Main results

* `Stacks.Duality.isQuasicoherent_homology_derivedPullback_of_preservesFiniteLimits` — Tag 08DW
  part (1) for a morphism along which pullback is exact, unconditionally. Open immersions and
  isomorphisms of schemes are the cases used below.
* `Stacks.Duality.isQuasicoherent_homology_derivedPullback_specMap` — the affine case, from
  essential surjectivity of derived sheafification and Tag 08DW part (2).
* `Stacks.Duality.isQuasicoherent_homology_derivedPullback_of_isAffine` — the case of a morphism
  of affine schemes.
* `Stacks.Duality.isQuasicoherent_homology_derivedPullback` — Tag 08DW part (1) for an
  arbitrary morphism of schemes, given `hess`. Its statement is literally the hypothesis `hpull`
  of `Stacks.Duality.quasiCoherentDerivedPullback`.
* `Stacks.Duality.isQuasicoherent_homology_derivedPullback'` — **Tag 08DW part (1)**, with no
  hypothesis, and `Stacks.Duality.quasiCoherentDerivedPullback'` the resulting functor
  `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.
* `Stacks.Duality.isQuasicoherent_homology_modulePullback_of_kFlat` — **Tag 08DW part (1) with no
  derived category in the statement**: the cohomology sheaves of the degreewise pullback `f^*P`
  of a K-flat complex `P` with quasi-coherent cohomology are quasi-coherent.
* `Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel` — **Tag 08DW part (1) at an
  arbitrary model** of the two derived categories, hence at
  `CategoryTheory.HasDerivedCategory.standard` as well.

Tag 08DW is now covered. Its covering set is part (1) here together with part (2), which is
`AlgebraicGeometry.affinePullbackComparison` and `AlgebraicGeometry.affinePullbackComparison_fac`
of `StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean`; the latter
two receive the tag by `add_to_stacks` at the end of this file, which is the first module that
sees both parts.

## Implementation notes

*The model of the derived categories.* The main statements are at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, as those of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean` are, and
for the reason given there: `Stacks.Duality.derivedPullback` is pinned there because a free
binder at the scheme spelling of the category is not found for a goal presented at the
ringed-space spelling, and the quasi-coherent inputs exist only at that model. No declaration
here mentions `CategoryTheory.HasDerivedCategory.standard`.

*How part (1) is carried to every other model.* `HasDerivedCategory` is data, so the pinned
statements above say nothing about any other model, and in particular nothing about the standard
one, at which the Fourier-Mukai functor `AlgebraicGeometry.fourierMukai` and the derived tensor
product of [Stacks, Tag 08DX] are read. The gap is crossed the way
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean` and
`StacksFrontier/AlgebraicGeometry/Intersection/TorFormula/CoherentTorSheaves.lean` cross it: the
content is restated with **no derived category in it at all** — a statement about a K-flat complex
`P` of `𝒪_Y`-modules and the degreewise pullback `f^*P`, which is
`isQuasicoherent_homology_modulePullback_of_kFlat` — and then read back at a free
`[HasDerivedCategory.{w}]` binder by `isQuasicoherent_homology_derivedPullback_anyModel`. The
hinge is `Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`, which rests on
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`: the
canonical comparison
`Lf^* ⟶ K(f^*)` is invertible at a K-flat complex at *any* model, so `Lf^*` of the class of `P` is
the class of `f^*P` there, and the existence of K-flat resolutions ([Stacks, Tag 06YF]) presents
every object of `D(𝒪_Y)` as such a class. The two binders are written at the ringed-space spelling
`SheafOfModules (structureSheafRing X.toRingedSpace)`, which is the spelling
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` asks for, so instance search
finds them; a binder at the scheme spelling would not be found, which is the obstruction recorded
in the paragraph above.

*Why the unconditional composition formula is restated.* Not because of the model: this file used
to say that
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/CompositionUnconditional.lean` opens
with
a file-level `attribute [local instance] HasDerivedCategory.standard`, and it does not — that file
contains no `attribute` command at all, its own module documentation says that everything in it
carrying a derived category carries the `HasDerivedCategory` binders, and
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` is stated at three free
binders `[HasDerivedCategory.{w₁} (ModuleSheaves X)]`, `[.{w₂} (ModuleSheaves Y)]`,
`[.{w₃} (ModuleSheaves Z)]`. So it holds at the model used here, and
`Stacks.Duality.derivedPullbackCompIso` below is exactly that isomorphism applied to
`f.toLRSHom.toShHom`: what the restatement supplies is the crossing from the ringed-space
spelling of the module category to the scheme spelling, the crossing recorded in the paragraph
below, and nothing else. The parametric layer underneath needs no restating either:
`Stacks.DerivedPullback.Composition.derivedPullbackCompComparison`,
`Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparison` and
`Stacks.DerivedPullback.Composition.isIso_app_of_resolving` carry the three model binders
themselves, and so do
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`,
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat` and
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`.

*Crossing to the scheme spelling.* `Scheme.Modules.pullback f` and
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` are equal by `rfl`, but the
`HasDerivedCategory` instance is found only at the first spelling, because `Scheme.Modules` is a
`def` and not a reducible abbreviation. Every statement here is therefore made at the scheme
spelling and the crossing happens in term position, where the conversion check runs at default
transparency: `inferInstanceAs` transports the two exactness instances, and the model binders of
the ringed-space declarations are solved by unification with the scheme-spelled expected type.

*Locality.* The cover used is the family of affine opens of `X` contained in the preimage of an
affine open of `Y`, which is a cover because the affine opens of `Y` cover `Y` and the affine
opens of `X` contained in a given open form a basis of it. Quasi-coherence is assembled from it
by `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations`, which asks for
a presentation of each restriction rather than for quasi-coherence, and on an affine open
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec` manufactures one.
`AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen` is not usable: it asks for *every*
affine open of `X`, and an affine open of `X` need not lie in the preimage of an affine open
of `Y`.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe w₁ w₂ u

namespace Stacks.Duality

open Stacks.DerivedPullback

/-! ### The two structural isomorphisms, for schemes -/

/-- **The composition formula for derived pullback of sheaves of modules on schemes**, at the
locally small model: `Lf₂^* ⋙ Lf₁^* ≅ L(f₁ ≫ f₂)^*`. -/
def derivedPullbackCompIso {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    derivedPullback f₂ ⋙ derivedPullback f₁ ≅ derivedPullback (f₁ ≫ f₂) :=
  Composition.derivedPullbackCompIsoCanonical f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom

/-- **For a morphism of schemes along which degreewise pullback is exact, the derived pullback is
degreewise pullback.** -/
def derivedPullbackMapDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteLimits (Scheme.Modules.pullback f)]
    [PreservesFiniteColimits (Scheme.Modules.pullback f)] :
    derivedPullback f ≅ (Scheme.Modules.pullback f).mapDerivedCategory :=
  haveI : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback f))
  haveI : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso f.toLRSHom.toShHom

/-- **For a morphism of schemes along which degreewise pullback is exact, `f^*` commutes with the
cohomology of the derived category**: `f^*H^i(E) ≅ H^i(Lf^*E)`. -/
def homologyDerivedPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteLimits (Scheme.Modules.pullback f)]
    (E : DerivedCategory Y.Modules) (i : ℤ) :
    (Scheme.Modules.pullback f).obj ((DerivedCategory.homologyFunctor Y.Modules i).obj E) ≅
      (DerivedCategory.homologyFunctor X.Modules i).obj ((derivedPullback f).obj E) :=
  haveI : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteColimits_modulesPullback f
  derivedHomologyMapIso (Scheme.Modules.pullback f) E i ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((derivedPullbackMapDerivedIso f).app E).symm

/-- **Tag 08DW part (1) for a morphism along which degreewise pullback is exact**: there the
cohomology of the derived pullback is the pullback of the cohomology, and pullback preserves
quasi-coherence by Tag 01BG. Unconditional. -/
theorem isQuasicoherent_homology_derivedPullback_of_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [PreservesFiniteLimits (Scheme.Modules.pullback f)]
    (E : DerivedCategory Y.Modules) (i : ℤ)
    (hE : ((DerivedCategory.homologyFunctor Y.Modules i).obj E).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj E)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (homologyDerivedPullbackIso f E i)
    (Stacks.Modules.isQuasicoherent_pullback f _ hE)

/-! ### The affine case -/

/-- Pullback along an open immersion of schemes preserves finite limits. -/
private theorem preservesFiniteLimits_pullback_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback f)

/-- If `E ≅ E'` and the `i`-th cohomology of `E'` is quasi-coherent, so is that of `E`. -/
private theorem isQuasicoherent_homology_of_iso {X : Scheme.{u}}
    {E E' : DerivedCategory X.Modules} (e : E ≅ E') (i : ℤ)
    (h : ((DerivedCategory.homologyFunctor X.Modules i).obj E').IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules i).mapIso e).symm h

/-- **Tag 08DW part (1) for `Spec φ`**, given that derived sheafification is essentially
surjective.

Essential surjectivity writes `E` as the derived sheafification of a complex `M^•` of
`R`-modules; the affine comparison square of Tag 08DW part (2),
`AlgebraicGeometry.affinePullbackComparison`, then identifies `L(Spec φ)^*E` with the derived
sheafification of `S ⊗ᴸ_R M^•`, whose cohomology sheaves are quasi-coherent by
`AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj`.

This is the only place where Tag 06Z0 is used, here and in the Stacks proof both. -/
theorem isQuasicoherent_homology_derivedPullback_specMap
    {R S : CommRingCat.{u}} (hess : (derivedTilde R).EssSurj) (φ : R ⟶ S)
    (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec S).Modules i).obj
      ((derivedPullback (Spec.map φ)).obj E)).IsQuasicoherent := by
  have := hess
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := derivedTilde R)
    (⟨E, hE⟩ : quasiCoherentDerivedCategory (Spec R))
  have e₁ : (tilde.functor R).mapDerivedCategory.obj M ≅ E :=
    ((derivedTildeCompι R).app M).symm ≪≫
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.mapIso e
  have e₂ : (derivedPullback (Spec.map φ)).obj E ≅
      (tilde.functor S).mapDerivedCategory.obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (CommRingCat.Hom.hom φ)).functor.obj M) :=
    (derivedPullback (Spec.map φ)).mapIso e₁.symm ≪≫ (affinePullbackComparison R S φ).app M
  exact isQuasicoherent_homology_of_iso e₂ i
    (isQuasicoherent_homology_mapDerivedCategory_obj S _ i)

/-- **Tag 08DW part (1) for a morphism of affine schemes**, given essential surjectivity of
derived sheafification.

The morphism factors as `A ≅ Spec Γ(A) ⟶ Spec Γ(B) ≅ B`, the two isomorphisms are open
immersions and so have exact pullback, and the middle map is handled by
`isQuasicoherent_homology_derivedPullback_specMap`. The three derived pullbacks are composed by
`derivedPullbackCompIso`. -/
theorem isQuasicoherent_homology_derivedPullback_of_isAffine
    (hess : ∀ R : CommRingCat.{u}, (derivedTilde R).EssSurj)
    {A B : Scheme.{u}} [IsAffine A] [IsAffine B] (g : A ⟶ B)
    (E : DerivedCategory B.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor B.Modules n).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor A.Modules i).obj
      ((derivedPullback g).obj E)).IsQuasicoherent := by
  have hcomp : A.isoSpec.hom ≫ Spec.map g.appTop ≫ B.isoSpec.inv = g := by
    apply (cancel_mono B.isoSpec.hom).1
    calc
      (A.isoSpec.hom ≫ Spec.map g.appTop ≫ B.isoSpec.inv) ≫ B.isoSpec.hom =
          A.isoSpec.hom ≫ Spec.map g.appTop := by simp [Category.assoc]
      _ = g ≫ B.isoSpec.hom := Scheme.isoSpec_hom_naturality g
  have := preservesFiniteLimits_pullback_of_isOpenImmersion B.isoSpec.inv
  have := preservesFiniteLimits_pullback_of_isOpenImmersion A.isoSpec.hom
  have h₁ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(B, ⊤)).Modules n).obj
      ((derivedPullback B.isoSpec.inv).obj E)).IsQuasicoherent := fun n =>
    isQuasicoherent_homology_derivedPullback_of_preservesFiniteLimits B.isoSpec.inv E n (hE n)
  have h₂ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(A, ⊤)).Modules n).obj
      ((derivedPullback (Spec.map g.appTop)).obj
        ((derivedPullback B.isoSpec.inv).obj E))).IsQuasicoherent := fun n =>
    isQuasicoherent_homology_derivedPullback_specMap (hess _) g.appTop _ h₁ n
  have eiso : (derivedPullback g).obj E ≅
      (derivedPullback A.isoSpec.hom).obj
        ((derivedPullback (Spec.map g.appTop)).obj
          ((derivedPullback B.isoSpec.inv).obj E)) :=
    (eqToIso (congrArg (fun q : A ⟶ B => (derivedPullback q).obj E) hcomp)).symm ≪≫
      ((derivedPullbackCompIso A.isoSpec.hom
        (Spec.map g.appTop ≫ B.isoSpec.inv)).app E).symm ≪≫
      (derivedPullback A.isoSpec.hom).mapIso
        ((derivedPullbackCompIso (Spec.map g.appTop) B.isoSpec.inv).app E).symm
  exact isQuasicoherent_homology_of_iso eiso i
    (isQuasicoherent_homology_derivedPullback_of_preservesFiniteLimits A.isoSpec.hom
      ((derivedPullback (Spec.map g.appTop)).obj ((derivedPullback B.isoSpec.inv).obj E)) i (h₂ i))

/-! ### The general case -/

/-- **Tag 08DW part (1), locally on `X`.** For an affine open `U` of `X` contained in the
preimage of an affine open `V` of `Y`, the restriction to `U` of the `i`-th cohomology of
`Lf^*E` is quasi-coherent.

`U.ι ≫ f` factors as `g ≫ V.ι` with `g : U ⟶ V` a morphism of affine schemes, the derived
pullbacks are composed by `derivedPullbackCompIso`, the open immersion `V.ι` is handled by
`isQuasicoherent_homology_derivedPullback_of_preservesFiniteLimits`, the morphism `g` by
`isQuasicoherent_homology_derivedPullback_of_isAffine`, and the restriction commutes with the
cohomology by `homologyDerivedPullbackIso` because `U.ι` has exact pullback. -/
theorem isQuasicoherent_pullback_homology_derivedPullback_of_isAffineOpen
    (hess : ∀ R : CommRingCat.{u}, (derivedTilde R).EssSurj)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory Y.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (i : ℤ) :
    ((Scheme.Modules.pullback U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPullback f).obj E))).IsQuasicoherent := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have := preservesFiniteLimits_pullback_of_isOpenImmersion U.ι
  have := preservesFiniteLimits_pullback_of_isOpenImmersion V.ι
  have h₁ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor V.toScheme.Modules n).obj
      ((derivedPullback V.ι).obj E)).IsQuasicoherent := fun n =>
    isQuasicoherent_homology_derivedPullback_of_preservesFiniteLimits V.ι E n (hE n)
  have eiso : (derivedPullback U.ι).obj ((derivedPullback f).obj E) ≅
      (derivedPullback (f.resLE V U hUV)).obj ((derivedPullback V.ι).obj E) :=
    (derivedPullbackCompIso U.ι f).app E ≪≫
      (eqToIso (congrArg (fun q : U.toScheme ⟶ Y => (derivedPullback q).obj E)
        (Scheme.Hom.resLE_comp_ι f hUV))).symm ≪≫
      ((derivedPullbackCompIso (f.resLE V U hUV) V.ι).app E).symm
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    (homologyDerivedPullbackIso U.ι ((derivedPullback f).obj E) i).symm
    (isQuasicoherent_homology_of_iso eiso i
      (isQuasicoherent_homology_derivedPullback_of_isAffine hess (f.resLE V U hUV)
        ((derivedPullback V.ι).obj E) h₁ i))

/-- **[Stacks, Tag 08DW] part (1): derived pullback preserves quasi-coherence of cohomology**,
given essential surjectivity of derived sheafification ([Stacks, Tag 06Z0]).

Let `f : X ⟶ Y` be an arbitrary morphism of schemes and let `K` be a complex of `𝒪_Y`-modules
with quasi-coherent cohomology. Then every cohomology sheaf of `Lf^*K` is quasi-coherent.

This is exactly the hypothesis `hpull` of `Stacks.Duality.quasiCoherentDerivedPullback`, of
`Stacks.Duality.quasiCoherentDerivedAdjunction` and of
`isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactDerivedPullback` in the namespace
`Stacks.Duality.DerivedPushforward`, so an unconditional Tag 06Z0 discharges all three by
`exact`. -/
theorem isQuasicoherent_homology_derivedPullback
    (hess : ∀ R : CommRingCat.{u}, (derivedTilde R).EssSurj)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : quasiCoherentDerivedCategory Y) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).IsQuasicoherent := by
  let I := {W : X.affineOpens // ∃ V : Y.affineOpens, (W : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens)}
  let U : I → X.Opens := fun w => (w.1 : X.Opens)
  have hcov : TopologicalSpace.IsOpenCover U := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
    rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
    obtain ⟨V, hV, hfxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := f.base x) (U := ⊤) (by simp)
    obtain ⟨W, hW, hxW, hWle⟩ :=
      exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ V) hfxV
    exact ⟨⟨⟨W, hW⟩, ⟨⟨V, hV⟩, hWle⟩⟩, hxW⟩
  refine Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations _ U hcov
    fun w => ?_
  have hqc := isQuasicoherent_pullback_homology_derivedPullback_of_isAffineOpen hess f K.obj
    K.property w.1.2 w.2.choose.2 w.2.choose_spec i
  have : (((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).restrict (U w).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U w).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (U w).ι).app _).symm hqc
  exact (Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec
    w.1.2.isoSpec _).some

/-! ### [Stacks, Tag 08DW] part (1), with no hypothesis -/

/-- **[Stacks, Tag 08DW] part (1): `Lf^*` sends `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_X)`.** For an
arbitrary morphism of schemes `f : X ⟶ Y` and a complex `K` of `𝒪_Y`-modules all of whose
cohomology sheaves are quasi-coherent, every cohomology sheaf of `Lf^*K` is quasi-coherent.

This is `Stacks.Duality.isQuasicoherent_homology_derivedPullback`, with `hess` found by instance
search from `AlgebraicGeometry.derivedTilde_isEquivalence`. -/
@[stacks 08DW "part (1): derived pullback preserves quasi-coherence of cohomology"]
theorem isQuasicoherent_homology_derivedPullback' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : quasiCoherentDerivedCategory Y) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedPullback (fun _ => inferInstance) f K i

/-- **[Stacks, Tag 08DW] part (1), as a functor.** Derived pullback along a morphism of schemes
restricts to a functor `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` between the derived categories of complexes
with quasi-coherent cohomology.

This is `Stacks.Duality.quasiCoherentDerivedPullback` at
`Stacks.Duality.isQuasicoherent_homology_derivedPullback'`. -/
@[stacks 08DW "part (1): the restriction D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X) of derived pullback"]
abbrev quasiCoherentDerivedPullback' {X Y : Scheme.{u}} (f : X ⟶ Y) :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)

/-! ### [Stacks, Tag 08DW] part (1) at an arbitrary model -/

/-- **[Stacks, Tag 08DW] part (1) with no derived category in the statement.** Let `f : X ⟶ Y` be
a morphism of schemes and let `P` be a K-flat complex of `𝒪_Y`-modules — no boundedness is
assumed — whose cohomology sheaves are all quasi-coherent. Then the cohomology sheaves of the
degreewise pullback `f^*P` are quasi-coherent.

This is `Stacks.Duality.isQuasicoherent_homology_derivedPullback'` read at the class of `P`,
which `Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat` identifies with the class of `f^*P`.
Separating the statement from the derived category is what lets it be read back at a model other
than the locally small one; see the module documentation. -/
theorem isQuasicoherent_homology_modulePullback_of_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toRingedSpace P)
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherent) (i : ℤ) :
    ((((modulePullback f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i).IsQuasicoherent := by
  have hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor Y.Modules j).obj
      (DerivedCategory.Q.obj P)).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors Y.Modules j).app P).symm (hPq j)
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules i).app _) ?_
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules i).mapIso
      (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom P hP))
    (isQuasicoherent_homology_derivedPullback' f ⟨DerivedCategory.Q.obj P, hQ⟩ i)

/-- **[Stacks, Tag 08DW] part (1) at an arbitrary model of the two derived categories: `Lf^*`
sends `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_X)`.** For an arbitrary morphism of schemes `f : X ⟶ Y` and
an object `E` of `D(𝒪_Y)` all of whose cohomology sheaves are quasi-coherent, every cohomology
sheaf of `Lf^*E` is quasi-coherent.

The model of the two derived categories is a free `[HasDerivedCategory.{w}]` binder, so this
serves the locally small model of `Stacks.Duality.isQuasicoherent_homology_derivedPullback'` and
`CategoryTheory.HasDerivedCategory.standard` alike. By [Stacks, Tag 06YF] the object `E` is the
class of a K-flat complex `P`, at that model `Lf^*E` is the class of `f^*P` by
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`, and the cohomology sheaves of `f^*P` are
quasi-coherent by `isQuasicoherent_homology_modulePullback_of_kFlat`. -/
@[stacks 08DW "part (1) at an arbitrary model of the two derived categories"]
theorem isQuasicoherent_homology_derivedPullback_anyModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).obj E).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        i).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj E)).IsQuasicoherent := by
  obtain ⟨P, p, hP, -, hp, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    Y.toRingedSpace (DerivedCategory.Q.objPreimage E)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) p).2 hp
  have eE : (DerivedCategory.Q.obj P :
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) ≅ E :=
    @asIso _ _ _ _ (DerivedCategory.Q.map p) hiso ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).app P)
      ((SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).mapIso eE).symm (hE j))
  refine (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).mapIso
      ((Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom P hP).symm ≪≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).mapIso eE)) ?_
  exact (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).app _).symm
    (isQuasicoherent_homology_modulePullback_of_kFlat f P hP hPq i)

end Stacks.Duality

/-! ### [Stacks, Tag 08DW] part (2)

Part (2) is `AlgebraicGeometry.affinePullbackComparison`, the affine comparison square
`Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`, together with its canonical normalisation
`AlgebraicGeometry.affinePullbackComparison_fac`; both are proved, unconditionally, in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean`. They are
given the tag here because this is the first module in which part (1) of the tag is also
available, and the repository attaches a tag only once its whole statement is covered. -/

add_to_stacks 08DW "part (2): the affine comparison square Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~"
  AlgebraicGeometry.affinePullbackComparison

add_to_stacks 08DW "part (2): the canonical normalisation of the affine comparison square"
  AlgebraicGeometry.affinePullbackComparison_fac

end
