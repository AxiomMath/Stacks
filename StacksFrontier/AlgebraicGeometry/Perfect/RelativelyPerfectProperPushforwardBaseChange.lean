module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectDirectImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.OpenCover
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardNoetherian
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeIsIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfectness of the derived direct image of a relatively perfect object

Let `f : X ⟶ S` be flat, proper and of finite presentation and `E` an `S`-perfect object of
`D(𝒪_X)`. Then `Rf_*E` is perfect and its formation commutes with base change
([Stacks, Tag 0DJT]). The perfectness is reduced to a Noetherian base: over an affine base, `f`
and `E` come from a Noetherian model, over which `Rf_*` of the model is perfect, and its formation
commutes with base change ([Stacks, Tag 08IB]).

## Main results

* `isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap`: [Stacks, Tag 0DJT].
* `isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat`: its perfectness clause.
* `isPerfect_derivedPushforward_iff_standard`: perfectness of `Rf_*E` does not depend on the
  model of the derived categories.

All are in the namespace `Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward`.

## Implementation notes

Relative perfectness and the Noetherian model are read at the standard model (as in
`AlgebraicGeometry.exists_isPerfectRelativeTo_noetherianModel`), the base change map at the
locally small model; the private steps below move between the two through
`isPerfect_derivedPushforward_iff_standard` and
`StacksDraft.DerivedModel.derivedPullbackModelIso`. The base change input is the invertibility
of `Stacks.Duality.quasiCoherentDerivedBaseChange` along the flat Noetherian model
([Stacks, Tag 08IB] at the locally small model); the base change clause of the tag is
[Stacks, Tag 08IB] at the standard model,
`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_torIndependent`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.PerfectComplexTriangles

/-- **Perfectness of `Rf_*E` does not depend on the model.** `Rf_*` at the standard model and at
the locally small model of an object `E` are both represented by `f_*I` for a K-injective
resolution `I` of a complex representing `E`. -/
theorem isPerfect_derivedPushforward_iff_standard {X S : Scheme.{u}} (f : X ⟶ S)
    (E : DerivedCategory X.Modules) :
    @IsPerfect S.toRingedSpace (HasDerivedCategory.standard S.Modules)
        ((derivedPushforwardModules f).obj E) ↔
      IsPerfect (X := S.toRingedSpace) ((Stacks.Duality.derivedPushforward f).obj E) := by
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eQs : @Iso (@DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) _
      ((@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard X.Modules)).obj K) E :=
    (Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.mapIso eQ
  obtain ⟨I, s, hI, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X K
  let eStd := (derivedPushforwardModules f).mapIso
      (eQs.symm ≪≫ ((@DerivedCategory.quotientCompQhIso X.Modules _ _
        (HasDerivedCategory.standard X.Modules)).app K).symm) ≪≫
    @Stacks.Duality.derivedPushforwardObjIso X S f (HasDerivedCategory.standard X.Modules)
      (HasDerivedCategory.standard S.Modules) K I s hI hs
  let eLS := (Stacks.Duality.derivedPushforward f).mapIso
      (eQ.symm ≪≫ ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm) ≪≫
    Stacks.Duality.derivedPushforwardObjIso f s hI hs
  exact ⟨fun h => isPerfect_of_iso eLS.symm
      (isPerfect_Q_transfer (HasDerivedCategory.standard S.Modules)
        (Scheme.Modules.hasDerivedCategory S) _
        (@isPerfect_of_iso S.toRingedSpace (HasDerivedCategory.standard S.Modules) _ _ eStd h)),
    fun h => @isPerfect_of_iso S.toRingedSpace (HasDerivedCategory.standard S.Modules) _ _ eStd.symm
      (isPerfect_Q_transfer (Scheme.Modules.hasDerivedCategory S)
        (HasDerivedCategory.standard S.Modules) _ (isPerfect_of_iso eLS h))⟩

section BaseChange

open Stacks.Duality

/-- Perfectness of `Rf'_*E'` passes to `Rf_*E` for `E ≅ L(g')^*E'` along a cartesian square of
quasi-compact quasi-separated schemes with `f'` flat: the base change map is invertible there
([Stacks, Tag 08IB]). -/
private theorem isPerfect_derivedPushforward_of_baseChange {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S ⟶ S') (g' : X ⟶ X') (sq : IsPullback g' f f' g)
    [CompactSpace S] [CompactSpace S'] [QuasiSeparatedSpace S']
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] [CompactSpace X'] [Flat f']
    (E : DerivedCategory X.Modules) (E' : DerivedCategory X'.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X'.Modules i).obj E').IsQuasicoherent)
    (hN : IsPerfect (X := S'.toRingedSpace) ((derivedPushforward f').obj E'))
    (eE : (derivedPullback g').obj E' ≅ E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforward f).obj E) := by
  let T := quasiCoherentDerivedBaseChange g' f f' g
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
    (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g')
    sq.w
  have : IsIso T := isIso_quasiCoherentDerivedBaseChange_natTrans _ _ _ _ sq
    (torIndependent_of_flat_left f' g)
  exact isPerfect_of_iso ((ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := S.Modules)
      (SheafOfModules.isQuasicoherent S.ringCatSheaf))).mapIso
      (asIso (NatTrans.app T ⟨E', hqc⟩)) ≪≫ (derivedPushforward f).mapIso eE)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (hX := Scheme.Modules.hasDerivedCategory S)
      (hY := Scheme.Modules.hasDerivedCategory S') g.toLRSHom.toShHom _ hN)

/-- Perfectness of `Rf_*E` is local on the base: it suffices that `R(f|_W)_*(E|_{f⁻¹W})` is perfect
for the affine opens `W` of `S`. -/
private theorem isPerfect_derivedPushforward_of_isAffineOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (E : DerivedCategory X.Modules)
    (h : ∀ W : S.Opens, IsAffineOpen W → IsPerfect (X := W.toScheme.toRingedSpace)
      ((derivedPushforward (f ∣_ W)).obj
        ((OpenImmersion.derivedRestrict (f ⁻¹ᵁ W).ι).obj E))) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforward f).obj E) := by
  refine Stacks.Duality.OpenImmersion.isPerfect_of_forall_exists_isPerfect_derivedRestrict _
    fun y => ?_
  obtain ⟨W₀, hW, hyW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show y ∈ (⊤ : S.Opens) from trivial)
  let W : S.Opens := W₀
  exact ⟨W, W.ι, inferInstance, ⟨y, hyW⟩, rfl, isPerfect_of_iso
    (QcqsGeneration.baseChangeIso f (f ⁻¹ᵁ W).ι W.ι (f ∣_ W)
      (isPullback_morphismRestrict f W).flip E).symm (h W hW)⟩

/-- Restriction along an open immersion, compared with derived pullback at the standard model. -/
def derivedRestrictIsoStandardPullback {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i]
    (E : DerivedCategory Z.Modules) :=
  (derivedRestrictIsoDerivedPullback i).app E ≪≫
    ((StacksDraft.DerivedModel.derivedPullbackModelIso i.toLRSHom.toShHom).app E).symm

/-- Perfectness of `Rg_*` of an object, from perfectness at the standard model of `Rg_*` of an
isomorphic object. -/
private theorem isPerfect_derivedPushforward_of_iso_standard {U W : Scheme.{u}} (g : U ⟶ W)
    {A B : DerivedCategory U.Modules} (e : A ≅ B)
    (h : @IsPerfect W.toRingedSpace (HasDerivedCategory.standard W.Modules)
      ((derivedPushforwardModules g).obj B)) :
    IsPerfect (X := W.toRingedSpace) ((derivedPushforward g).obj A) :=
  isPerfect_of_iso ((derivedPushforward g).mapIso e.symm)
    ((isPerfect_derivedPushforward_iff_standard g B).1 h)

end BaseChange

section Affine

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Duality in
/-- The affine case of the perfectness clause of [Stacks, Tag 0DJT], from the base change property
of the Noetherian model: `f` and `E` are the base change of a flat proper `f'` over a Noetherian
base and of an `S'`-perfect `E'`, `Rf'_*E'` is perfect, and `Rf_*E` is its derived pullback. -/
@[sga "5 III 6.2" "special case"]
private theorem isPerfect_derivedPushforward_of_isAffine_aux {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E) := by
  obtain ⟨S', X', _, f', _, _, _, g, g', sq, E', hE', ⟨e⟩⟩ :=
    exists_isPerfectRelativeTo_noetherianModel f E hE
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparated g' := MorphismProperty.of_isPullback sq.flip inferInstance
  exact (isPerfect_derivedPushforward_iff_standard f E).2
    (isPerfect_derivedPushforward_of_baseChange f f' g g' sq E E'
      (fun i => (PerfectApproximation.isQuasicoherent_homology_standard_iff E' i).1
        (isQuasicoherentDerived_of_isPseudoCoherent X' E' hE'.1 i))
      ((isPerfect_derivedPushforward_iff_standard f' E').1
        (isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_isNoetherian f'
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) (fun _ => rfl) E'
          hE'))
      (((StacksDraft.DerivedModel.derivedPullbackModelIso g'.toLRSHom.toShHom).app E').symm ≪≫
        (Stacks.Injectives.grothendieckModelEquiv X.Modules).functor.mapIso e))

/-- The perfectness clause of [Stacks, Tag 0DJT] over an arbitrary base, from the base change
property over its affine opens. -/
@[sga "5 III 6.2" "special case"]
private theorem isPerfect_derivedPushforward_aux {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E) := by
  refine (isPerfect_derivedPushforward_iff_standard f E).2
    (isPerfect_derivedPushforward_of_isAffineOpen f E fun W hW => ?_)
  have : IsAffine W.toScheme := hW
  let ι := (f ⁻¹ᵁ W).ι
  have hpb := (isPullback_morphismRestrict f W).flip
  have : Flat (f ∣_ W) := MorphismProperty.of_isPullback hpb ‹Flat f›
  have : IsProper (f ∣_ W) := MorphismProperty.of_isPullback hpb ‹IsProper f›
  have : LocallyOfFinitePresentation (f ∣_ W) :=
    MorphismProperty.of_isPullback hpb ‹LocallyOfFinitePresentation f›
  have : CompactSpace (f ⁻¹ᵁ W).toScheme := QuasiCompact.compactSpace_of_compactSpace (f ∣_ W)
  let EW := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    ι.toLRSHom.toShHom).obj E
  have hEW : (f ∣_ W).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) EW :=
    (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff (f ∣_ W) W.ι (morphismRestrict_ι f W) EW).1
      (Scheme.Hom.isPerfectRelativeTo_opens_ι f (f ⁻¹ᵁ W) E hE)
  exact isPerfect_derivedPushforward_of_iso_standard (f ∣_ W)
    (derivedRestrictIsoStandardPullback ι E) (isPerfect_derivedPushforward_of_isAffine_aux _ EW hEW)

/-- **The perfectness clause of [Stacks, Tag 0DJT].** Let `f : X ⟶ S` be flat, proper and of
finite presentation and let `E ∈ D(𝒪_X)` be `S`-perfect. Then `Rf_*E` is a perfect object of
`D(𝒪_S)`. -/
alias isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat :=
  isPerfect_derivedPushforward_aux

/-- **[Stacks, Tag 0DJT].** Let `f : X ⟶ S` be a morphism of schemes which is flat, proper and of
finite presentation, and let `E ∈ D(𝒪_X)` be `S`-perfect. Then `Rf_*E` is a perfect object of
`D(𝒪_S)` and its formation commutes with arbitrary base change: for every cartesian square
`X' = X ×_S S'` the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an
isomorphism. -/
@[stacks 0DJT "f flat, proper and locally of finite presentation (finite presentation, as \
IsProper gives quasi-compact and quasi-separated) over an arbitrary base, E S-perfect: Rf_*E is \
perfect, and for every cartesian square X' = X ×_S S' the base change map \
Lg^*Rf_*E → Rf'_*L(g')^*E of Tag 08HY is an isomorphism"]
theorem isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
          E) :=
  ⟨isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat f E hE,
    fun g _ _ sq => isIso_derivedBaseChangeMap_of_torIndependent sq
      (torIndependent_of_flat_left f g) E
      (isQuasicoherentDerived_of_isPseudoCoherent X E hE.1)⟩

end Affine

end Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

end
