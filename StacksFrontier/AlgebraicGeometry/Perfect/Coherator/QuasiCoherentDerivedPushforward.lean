module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DirectSums
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect

/-!
# Quasi-coherence of the unbounded derived direct image is affine-local on the base

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. Whether the
unbounded derived direct image `Rf_*` carries complexes with quasi-coherent cohomology to
complexes with quasi-coherent cohomology may be tested on an affine open cover of the target.

Quasi-coherence of a module on `S` is affine-local, so it suffices to restrict to an affine open
`V ⊆ S`. There the morphism `f` restricts to a quasi-compact and quasi-separated morphism whose
target is quasi-compact and quasi-separated, and derived direct image commutes with restriction
to an open because the square of ringed spaces is a pullback with open immersions on the sides.

## Main definitions

* `AlgebraicGeometry.PreservesQuasicoherentOnCompactTarget`: the assertion that `Rf_*` preserves
  quasi-coherent cohomology whenever the target is quasi-compact and quasi-separated.
* `AlgebraicGeometry.PreservesQuasicoherentOnAffineTarget`: the same assertion for an affine
  target, which is what the reduction below consumes.

## Main results

* `AlgebraicGeometry.PreservesQuasicoherentOnAffineTarget.of_compactTarget`: the affine-target
  case is a consequence of the quasi-compact and quasi-separated-target case.
* `AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_affineTarget`: preservation of
  quasi-coherent cohomology by `Rf_*` for an arbitrary quasi-compact and quasi-separated
  morphism follows from the case of an affine target.
* `AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_compactTarget`: the same reduction
  reading its hypothesis in the quasi-compact and quasi-separated-target form.
* `AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_isAffineHom`: **[Stacks, Tag 08D5]
  part (1) for an affine morphism**, with no hypothesis on the target and no appeal to the
  reduction.

## Implementation notes

The derived direct image is `AlgebraicGeometry.RingedSpace.derivedPushforward`, the total right
derived functor of degreewise pushforward on the underlying ringed spaces; complexes with
quasi-coherent cohomology are the objects of
`AlgebraicGeometry.QuasicoherentDerivedCategory`, whose defining object property is the
conclusion.

The hypothesis is stated for every quasi-compact and quasi-separated morphism with affine
target, because the reduction applies it to the restriction of `f` over an affine open of the
target rather than to `f` itself.

The category of `𝒪_X`-modules on a scheme has two definitionally equal but syntactically
distinct spellings, `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (structureSheafRing X.toSheafedSpace)`; the derived-category
machinery is stated in the second and quasi-coherence in the first, so each comparison between
them is made explicit.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.ClosedSupportPerfect (pullbackOpenRestrictionIso
  derivedRestrictionAlongOpen_isRightDerived)
open Stacks.Cohomology.HigherDirectImage (moduleRestriction)
open StacksDraft.PseudoCoherence (mapDerivedCategoryCompHomologyFunctorIso)

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- A pullback square of schemes along an open immersion remains a pullback square of the
underlying sheafed spaces. -/
private lemma isPullback_toShHom
    {X Y X' Y' : Scheme.{u}} (i : X' ⟶ X) (g : X' ⟶ Y')
    (f : X ⟶ Y) (j : Y' ⟶ Y) [IsOpenImmersion j]
    (h : IsPullback i g f j) :
    IsPullback i.toLRSHom.toShHom g.toLRSHom.toShHom
      f.toLRSHom.toShHom j.toLRSHom.toShHom := by
  have hL : IsPullback i.toLRSHom g.toLRSHom f.toLRSHom j.toLRSHom :=
    have : PreservesLimit (cospan f j) Scheme.forgetToLocallyRingedSpace := inferInstance
    h.map Scheme.forgetToLocallyRingedSpace
  have : PreservesLimit (cospan f.toLRSHom j.toLRSHom)
      LocallyRingedSpace.forgetToSheafedSpace :=
    LocallyRingedSpace.IsOpenImmersion.forget_preservesPullback_of_right j.toLRSHom f.toLRSHom
  exact hL.map LocallyRingedSpace.forgetToSheafedSpace

/-- The statement that `Rf_*` preserves quasi-coherent cohomology, for every quasi-compact and
quasi-separated morphism of schemes whose target is quasi-compact and quasi-separated. -/
public abbrev PreservesQuasicoherentOnCompactTarget : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), QuasiCompact f → QuasiSeparated f →
    CompactSpace S → QuasiSeparatedSpace S →
    ∀ E : QuasicoherentDerivedCategory X,
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj)

/-- The statement that `Rf_*` preserves quasi-coherent cohomology, for every quasi-compact and
quasi-separated morphism of schemes whose target is affine.

This is the form the reduction below actually consumes, and it is a weaker hypothesis than
`PreservesQuasicoherentOnCompactTarget`: the reduction restricts over an affine open of the
target, so the morphism it applies the hypothesis to has affine — not merely quasi-compact and
quasi-separated — target. -/
public abbrev PreservesQuasicoherentOnAffineTarget : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), QuasiCompact f → QuasiSeparated f → IsAffine S →
    ∀ E : QuasicoherentDerivedCategory X,
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj)

/-- An affine scheme is quasi-compact and quasi-separated, so the quasi-compact and
quasi-separated target case subsumes the affine target case. -/
public theorem PreservesQuasicoherentOnAffineTarget.of_compactTarget
    (hbase : PreservesQuasicoherentOnCompactTarget.{u}) :
    PreservesQuasicoherentOnAffineTarget.{u} := by
  intro X S f hqc hqs hS E
  have : IsAffine S := hS
  exact hbase f hqc hqs (Scheme.compactSpace_of_isAffine S) inferInstance E

/-- Pullback of modules along the inclusion of an open subscheme preserves finite limits. -/
private instance preservesFiniteLimits_modulePullback_ι {X : Scheme.{u}} (W : X.Opens) :
    PreservesFiniteLimits (modulePullback W.ι.toLRSHom.toShHom) :=
  inferInstanceAs (PreservesFiniteLimits
    (modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)))

/-- Pullback of modules along the inclusion of an open subscheme preserves finite colimits. -/
private instance preservesFiniteColimits_modulePullback_ι {X : Scheme.{u}} (W : X.Opens) :
    PreservesFiniteColimits (modulePullback W.ι.toLRSHom.toShHom) :=
  inferInstanceAs (PreservesFiniteColimits
    (modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)))

/-- Restricting a complex with quasi-coherent cohomology to an open subscheme keeps its
cohomology quasi-coherent. -/
private lemma isQuasicoherent_homology_mapDerivedCategory_restrict {X : Scheme.{u}} (W : X.Opens)
    (E : QuasicoherentDerivedCategory X) (k : ℤ) :
    ((DerivedCategory.homologyFunctor W.toScheme.Modules k).obj
      ((modulePullback W.ι.toLRSHom.toShHom).mapDerivedCategory.obj E.obj)).IsQuasicoherent := by
  have : ((DerivedCategory.homologyFunctor X.Modules k).obj E.obj).IsQuasicoherent :=
    E.property k
  have hrest : ((Scheme.Modules.restrictFunctor W.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules k).obj E.obj)).IsQuasicoherent :=
    inferInstance
  have hlocal : ((moduleRestriction X.toRingedSpace W).obj
      ((DerivedCategory.homologyFunctor X.Modules k).obj E.obj)).IsQuasicoherent := by
    rwa [← Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction X W]
  exact (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
    ((mapDerivedCategoryCompHomologyFunctorIso (modulePullback W.ι.toLRSHom.toShHom) k).app
      E.obj).symm
    ((SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      ((pullbackOpenRestrictionIso X.toRingedSpace W).app _).symm hlocal)

/-- Quasi-coherence of the cohomology of `Rf_*E` after restriction to an affine open of the
target. -/
private theorem isQuasicoherent_derivedPushforward_restrict_affine
    (hbase : PreservesQuasicoherentOnAffineTarget.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (E : QuasicoherentDerivedCategory X) (V : S.affineOpens) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor V.1.ι).obj
      ((DerivedCategory.homologyFunctor S.Modules n).obj
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj)))).IsQuasicoherent := by
  let U : S.Opens := V.1
  let W : X.Opens := f ⁻¹ᵁ U
  let X' : Scheme := W.toScheme
  let S' : Scheme := U.toScheme
  let i : X' ⟶ X := W.ι
  let j : S' ⟶ S := U.ι
  let g : X' ⟶ S' := f ∣_ U
  have hsquare : IsPullback i g f j := (isPullback_morphismRestrict f U).flip
  let fR := f.toLRSHom.toShHom
  let gR := g.toLRSHom.toShHom
  let iR := i.toLRSHom.toShHom
  let jR := j.toLRSHom.toShHom
  let Fi := modulePullback iR
  let Fj := modulePullback jR
  let Ri := Fi.mapDerivedCategory
  let Rj := Fj.mapDerivedCategory
  let αi := Fi.mapDerivedCategoryFactorsh.inv
  let αj := Fj.mapDerivedCategoryFactorsh.inv
  let Df := RingedSpace.derivedPushforward fR
  let eBC := @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _ fR iR jR gR _ _
    (isPullback_toShHom i g f j hsquare)
    _ _ _ _ Df (RingedSpace.derivedPushforward gR) Ri Rj
    (RingedSpace.derivedPushforwardUnit fR) (RingedSpace.derivedPushforwardUnit gR) αi αj
    (RingedSpace.derivedPushforward_isRightDerivedFunctor fR)
    (RingedSpace.derivedPushforward_isRightDerivedFunctor gR)
    (derivedRestrictionAlongOpen_isRightDerived X.toRingedSpace W)
    (derivedRestrictionAlongOpen_isRightDerived S.toRingedSpace U)
  let E' : QuasicoherentDerivedCategory X' :=
    ⟨Ri.obj E.obj, isQuasicoherent_homology_mapDerivedCategory_restrict W E⟩
  have : IsAffine S' := inferInstance
  have : CompactSpace S' := Scheme.compactSpace_of_isAffine S'
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated g
  have htarget : ((DerivedCategory.homologyFunctor S'.Modules n).obj
      (Rj.obj (Df.obj E.obj))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S'.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor S'.Modules n).mapIso (eBC.app E.obj)).symm
      (hbase g inferInstance inferInstance inferInstance E' n)
  rw [show V.1 = U from rfl, Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction S U]
  exact (SheafOfModules.isQuasicoherent S'.ringCatSheaf).prop_of_iso
    (((mapDerivedCategoryCompHomologyFunctorIso Fj n).app (Df.obj E.obj)).trans
      ((pullbackOpenRestrictionIso S.toRingedSpace U).app _)) htarget

/-- Preservation of quasi-coherent cohomology by the unbounded derived direct image is
affine-local on the target: if it holds for every quasi-compact and quasi-separated morphism
with affine target, it holds for every quasi-compact and quasi-separated morphism of
schemes. -/
public theorem isQuasicoherent_derivedPushforward_of_affineTarget
    (hbase : PreservesQuasicoherentOnAffineTarget.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (E : QuasicoherentDerivedCategory X) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj) := by
  intro n
  exact isQuasicoherent_of_restrict_isAffineOpen _ fun U hU =>
    isQuasicoherent_derivedPushforward_restrict_affine hbase f E ⟨U, hU⟩ n

/-- The same reduction from the quasi-compact and quasi-separated-target case: an affine scheme
is quasi-compact and quasi-separated, so `PreservesQuasicoherentOnCompactTarget` subsumes the
hypothesis of `AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_affineTarget`. -/
public theorem isQuasicoherent_derivedPushforward_of_compactTarget
    (hbase : PreservesQuasicoherentOnCompactTarget.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (E : QuasicoherentDerivedCategory X) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj) :=
  isQuasicoherent_derivedPushforward_of_affineTarget
    (PreservesQuasicoherentOnAffineTarget.of_compactTarget hbase) f E

/-- **[Stacks, Tag 08D5] part (1) for an affine morphism.** For an affine morphism of schemes the
unbounded derived direct image carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)`, with no hypothesis on
the target and so with no appeal to the affine-local reduction above.

This is `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`
restated for `AlgebraicGeometry.RingedSpace.derivedPushforward` and for the object property
defining `AlgebraicGeometry.QuasicoherentDerivedCategory`; the two spellings of the derived direct
image are the same total right derived functor of degreewise pushforward, and the derived
categories on both sides are at `CategoryTheory.HasDerivedCategory.standard`. -/
public theorem isQuasicoherent_derivedPushforward_of_isAffineHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] (E : QuasicoherentDerivedCategory X) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj) := by
  intro n
  exact isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom f E.obj E.property n

end AlgebraicGeometry

end
