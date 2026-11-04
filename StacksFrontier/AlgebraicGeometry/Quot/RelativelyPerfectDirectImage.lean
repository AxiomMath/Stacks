module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimitHeld
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.RetractOfAPerfectObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperMorphismSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# Perfect direct images of relatively perfect objects (towards Stacks 0DKX)

Let `f : X ⟶ Y` be a flat, proper, finitely presented morphism of algebraic spaces over a
scheme `S` and let `E ∈ D(𝒪_X)` be `Y`-perfect (Stacks 0DKN). Stacks 0DKX says that `Rf_*E` is
a perfect object of `D(𝒪_Y)` and that its formation commutes with arbitrary base change.

The source's proof is:

1. the base change assertion is Stacks 0A1K with `𝒢^• = 𝒪_X` (flat base change for a
   quasi-compact, quasi-separated flat morphism and `E ∈ D_QCoh(𝒪_X)`);
2. perfectness is étale local on `Y`, so `Y = Spec(R)` may be assumed; write `R = colim Rᵢ`
   with `Rᵢ` Noetherian and descend `X` to a proper flat `Xᵢ ⟶ Spec(Rᵢ)`
   (Stacks 07SK, 08K1, 08K0);
3. by Stacks 0DKW, `E` is the pullback of an `Rᵢ`-perfect `Eᵢ`;
4. Stacks 08IS applied to `Xᵢ ⟶ Spec(Rᵢ)` and `Eᵢ` makes `Rfᵢ_*Eᵢ` perfect, and the base change
   of step 1 identifies its pullback with `Rf_*E`.

Stacks 0A1K, 08IS and 0DKW are not yet proved here. Each is stated here as a proposition and
used as a labelled hypothesis. **Nothing here is registered.**

## Main definitions

Inputs not yet proved here:

* `AlgebraicGeometry.Space.FlatDerivedBaseChange`: Stacks 0A1K at `𝒢^• = 𝒪_X`, the form of
  `isIso_smallEtaleDerivedBaseChangeMap_of_isFlat`.
* `AlgebraicGeometry.Space.ProperSupportPerfectDirectImage`: Stacks 08IS, the form of
  `isPerfect_derivedModulePushforward_of_hasProperSupport`.
* `AlgebraicGeometry.Space.RelativelyPerfectColimitHolds`: Stacks 0DKW, the form of
  `AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectColimit`.

Internal steps:

* `AlgebraicGeometry.Space.NoetherianStageHypotheses`: at a Noetherian target, a `Y`-perfect
  object along a proper flat finitely presented morphism satisfies the hypotheses of Stacks 08IS.
  Proved: `AlgebraicGeometry.Space.noetherianStageHypotheses`.
* `AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent`: steps 2 and 3 of the source's
  proof, the étale localisation on `Y` and the limit argument, with the Situations 0DKU taken over
  `Spec ℤ`. Proved in
  `StacksFrontier/AlgebraicGeometry/Quot/RelativelyPerfectDirectImageReduction.lean` over `Spec ℤ`
  from Stacks 08K1, and over any base from that and the change of base of Stacks 04SG.

## Main results

* `AlgebraicGeometry.Space.noetherianStageHypotheses`: the hypotheses of Stacks 08IS hold at a
  Noetherian stage (unconditional).
* `AlgebraicGeometry.Space.derivedModulePushforwardIsoSpaceDerivedPushforward` and
  `AlgebraicGeometry.Space.derivedModulePushforwardTotalRightDerivedIso`: the three models of
  `Rf_*` in use agree (unconditional).
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap_of_isPerfectRelativeTo`:
  the base change assertion of Stacks 0DKX, from Stacks 0A1K.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isPerfect_limitPushforward_of`: the
  perfectness assertion at the limit of a Noetherian proper Situation 0DKU, from Stacks 0A1K,
  08IS and 0DKW.
* `AlgebraicGeometry.Space.isPerfect_spaceDerivedPushforward_of_isPerfectRelativeTo`: the
  perfectness assertion of Stacks 0DKX.
* `AlgebraicGeometry.Space.isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo`: Stacks 0DKX,
  both assertions, from the pending hypotheses above.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isPerfect_limitPushforward_of_isNoetherian`,
  `AlgebraicGeometry.Space.isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_reduction` and
  `AlgebraicGeometry.Space.relativelyPerfectPushforwardBaseChange_of_reduction`: the same, with
  `noetherianStageHypotheses` discharging `hstage`.
* `AlgebraicGeometry.Space.relativelyPerfectPushforwardBaseChange_of`: the 0DKX input
  `AlgebraicGeometry.Space.RelativelyPerfectPushforwardBaseChange` of the proof of Stacks 0DKY.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The models of `Rf_*` -/

section Models

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The derived direct image of the morphism of small étale ringed topoi and the derived direct
image `AlgebraicGeometry.Space.spaceDerivedPushforward` at the standard model are isomorphic:
both are right derived functors of the degreewise direct image, and the two spellings of the
degreewise direct image agree (`mapHomotopyCategory_modulePushforward_comp_Qh_eq`). -/
def derivedModulePushforwardIsoSpaceDerivedPushforward :
    derivedModulePushforward B S hS f ≅ spaceDerivedPushforward B S hS f :=
  Functor.rightDerivedNatIso _ _ (derivedModulePushforwardUnit B S hS f)
    (spaceDerivedPushforwardUnit B S hS f)
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) (Iso.refl _)

/-- The derived direct image of the morphism of small étale ringed topoi and the total right
derived functor `Stacks.DerivedFunctor.totalRightDerived` of the direct image of modules, the
spelling in which Stacks 08IS is stated, are isomorphic: both are right derived functors of the
degreewise direct image. -/
def derivedModulePushforwardTotalRightDerivedIso :
    derivedModulePushforward B S hS f ≅
      Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) :=
  Functor.rightDerivedNatIso _ _ (derivedModulePushforwardUnit B S hS f)
    (Functor.totalRightDerivedUnit (Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f))
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) (Iso.refl _)

end Models

/-! ### Inputs not yet proved here -/

section Held

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

/-- **Stacks 0A1K at `𝒢^• = 𝒪_X`** (not yet proved here), as a proposition, in exactly
the form of `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat`: for a
cartesian square of algebraic spaces with `f` quasi-compact, quasi-separated and flat, and
`E ∈ D_QCoh(𝒪_X)`, the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of Stacks 07A7 is an
isomorphism. This is the case of Stacks 0A1K that the proof of Stacks 0DKX uses. -/
def FlatDerivedBaseChange : Prop :=
  ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g), IsQuasiCompact B S hS f.hom →
    IsQuasiSeparated B S hS f.hom → IsFlat B S hS f.hom →
    ∀ E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)),
      QcohDerived B S hS X E →
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E)

attribute [local instance] pointTopology in
/-- **Stacks 08IS** (not yet proved here), as a proposition, in exactly the form of
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_hasProperSupport`: for
`f : X ⟶ Y` locally of
finite type and quasi-separated with `Y` Noetherian, an `E ∈ D^b_{Coh}(𝒪_X)` whose cohomology
sheaves have support proper over `Y` and which has finite Tor dimension over `f⁻¹𝒪_Y` has perfect
`Rf_*E`. -/
def ProperSupportPerfectDirectImage : Prop :=
  ∀ (hTop : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom), IsQuasiSeparated B S hS f.hom →
    IsNoetherian B S hS hTop Y.1 →
    ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) E →
      (∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
        ((SheafOfModules.toSheaf _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) →
      ∀ T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
        (inverseImageRingedSite B S hS f),
      Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension.{u + 1, u, u, u + 1} T
        ((derivedScalarRestriction B S hS f).obj E) →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E)

end Held

/-- **Stacks 0DKW** (not yet proved here), as a proposition: every
Situation 0DKU satisfies
`AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectColimit`. -/
def RelativelyPerfectColimitHolds : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
    (D : RelativeDescentSituation B S hS hZ I), D.RelativelyPerfectColimit

/-! ### Internal steps, pending -/

attribute [local instance] pointTopology in
/-- **The hypotheses of Stacks 08IS at a Noetherian stage** (internal, pending), as a
proposition: for a proper, flat, finitely presented `f : X ⟶ Y` with `Y` Noetherian, a
`Y`-perfect `E ∈ D(𝒪_X)` lies in `D^b_{Coh}(𝒪_X)`, its cohomology sheaves have support proper
over `Y`, and it has finite Tor dimension over `f⁻¹𝒪_Y`, measured against the canonical derived
tensor product of Stacks 06YU. In the source this is the sentence "applying Lemma 08IS to
`Xᵢ ⟶ Spec(Rᵢ)` and `Eᵢ`": pseudo-coherence on a Noetherian space is coherence of the cohomology
sheaves bounded above, the Tor clause of relative perfectness on the quasi-compact `X` bounds `E`
below and gives finite Tor dimension, and every closed subset of `X` is proper over `Y`. -/
def NoetherianStageHypotheses : Prop :=
  ∀ (hTop : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsProper B S hS f.hom → ∀ (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom), IsNoetherian B S hS hTop Y.1 →
    ∀ E : derivedModules B S hS X, IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) E ∧
        (∀ (hf : IsLocallyOfFiniteType B S hS f.hom) (i : ℤ), HasProperSupport B S hS X.2 Y.2
          f.hom hf ((SheafOfModules.toSheaf _).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) ∧
        Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension.{u + 1, u, u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct (inverseImageRingedSite B S hS f))
          ((derivedScalarRestriction B S hS f).obj E)

/-- **The étale localisation and the limit argument of the proof of Stacks 0DKX** (internal),
as a proposition. To prove that `Rf_*E` is perfect for a proper, flat, finitely presented
`f : X ⟶ Y` of algebraic spaces over `S` and a `Y`-perfect `E`, it suffices to know the same at
the limit of every Situation 0DKU over the final scheme `Spec ℤ` whose limit is a limit of schemes
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`), whose stages are Noetherian
and whose base changes are proper.

In the source: perfectness is étale local on `Y`, so `Y = Spec(R)`; with `R = colim Rᵢ` over the
finite type `ℤ`-subalgebras, `X ⟶ Y` descends to a finitely presented `X₀ ⟶ Spec(R₀)`
(Stacks 07SK), flat (Stacks 08K0) and proper (Stacks 08K1) after enlarging the index, which is a
Situation 0DKU with limit `X ⟶ Y`; its limit is the limit of the affine schemes `Spec(Rᵢ)`, a
limit of schemes.

The Situations are taken over `Spec ℤ` and not over `S`: the stages `Spec(Rᵢ)` are not schemes
over `S`. Over the same `S` the proposition would be too strong: when `S` has a local ring which
is not Noetherian, no Situation over `S` with Noetherian stages has `S` itself as its limit, since
`S ⟶ Yᵢ ⟶ S` would make that local ring a retract of a Noetherian local ring. The passage from
`S` to `Spec ℤ` is the change of base of Stacks 04SG. -/
def PerfectnessReducesToNoetherianDescent : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (E : derivedModules B S hS X), IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
        (D : RelativeDescentSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal I),
        D.IsSchemeLimit →
        (∀ i : D.LaterIndex,
          IsNoetherian B _ B.contains_terminal B.contains_terminal (D.stageTarget i).1) →
        (∀ i : D.LaterIndex, IsProper B _ B.contains_terminal (D.stageStructure i).hom) →
        ∀ E' : derivedModules B _ B.contains_terminal D.limitSource, D.IsLimitPerfect E' →
          (smallEtaleRingedSite B _ B.contains_terminal D.limitTarget.1
            D.limitTarget.2).IsPerfect
            ((derivedModulePushforward B _ B.contains_terminal D.limitStructure).obj E')) →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((derivedModulePushforward B S hS f).obj E)

attribute [local instance] pointTopology in
/-- **The hypotheses of Stacks 08IS at a Noetherian stage.** For a proper, flat, finitely
presented `f : X ⟶ Y` with `Y` Noetherian, a `Y`-perfect `E ∈ D(𝒪_X)` lies in
`D^b_{Coh}(𝒪_X)`, its cohomology sheaves have support proper over `Y`, and it has finite Tor
dimension over `f⁻¹𝒪_Y` for the canonical derived tensor product of Stacks 06YU.

`X` is Noetherian (Stacks 04ZL). Pseudo-coherence gives coherent, bounded above cohomology
(Stacks 08IK) which is quasi-coherent (Stacks 08JL), and the Tor clause on the quasi-compact `X`
bounds `E` (`AlgebraicGeometry.Space.isBounded_of_isPerfectRelativeTo`). A coherent module has
closed support (Stacks 07TZ), and every closed subset of `|X|` is proper over `Y` since `f` is
proper. For the Tor dimension, an affine étale chart covers `X` and is quasi-compact, so finitely
many members of a covering of it carry one Tor interval, and Tor amplitude in a fixed interval
descends along that covering family of the final object (Stacks 08FZ). -/
theorem noetherianStageHypotheses : NoetherianStageHypotheses B S hS := by
  intro hTop X Y f hprop hflat hfp hY E hE
  have hXN : IsNoetherian B S hS hTop X.1 :=
    isNoetherian_of_isFinitePresentation B S hS hTop f.hom X.2 Y.2 hfp hY
  have hbd : DerivedCategoryB.IsBounded E :=
    isBounded_of_isPerfectRelativeTo B S hS f hXN.1 hflat hfp.1 _ E hE
  have hcoh := (isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherent_of_isNoetherian
    B S hS X.1 X.2 hTop hXN E hE.1).2
  have hqc := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE.1
  refine ⟨⟨hbd, fun i => ?_⟩, fun hf i => ?_, ?_⟩
  · have := hqc i
    have := hcoh i
    exact IsCoherent.mk
  · have := hcoh i
    have := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E)
    exact hasProperSupport_toSheaf_of_isProper B S hS X.2 Y.2 f.hom hf hprop _
  · obtain ⟨U, hUaff, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS X.1 X.2 hXN.1
    open Stacks.SheafOfModules.DerivedTensorProduct in
    obtain ⟨ι, -, V, g, a, b, hg, hamp⟩ :=
      exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension
        _ _ hE.2 U (isQuasiCompactObject_of_isAffine B S hS X.1 U hUaff)
    have hV : (inverseImageRingedSite B S hS f).J.CoversTop
        (fun p : (_ : PUnit.{u + 2}) × ι => V p.2) :=
      Stacks.Sites.coversTop_bind hcov (fun _ => g) fun _ => hg
    have := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
    exact ⟨a, b, Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_coversTop
      (inverseImageRingedSite B S hS f) _ (canonicalSliceDerivedTensorProduct B S hS f) hV _ a b
      fun p => hamp p.2⟩

/-! ### The base change assertion -/

section BaseChange

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0DKX, base change** (unregistered: from Stacks 0A1K, not yet proved here). For a
cartesian square with `f` flat, proper and of finite presentation and a `Y`-perfect `E`, the
base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of Stacks 07A7 is an isomorphism. As in the source,
this is Stacks 0A1K with `𝒢^• = 𝒪_X`: `f` is quasi-compact and quasi-separated, being proper, and
`E` lies in `D_QCoh(𝒪_X)`, being pseudo-coherent (Stacks 08JL).

* `h0A1K`: Stacks 0A1K, not yet proved here. -/
theorem isIso_smallEtaleDerivedModuleBaseChangeMap_of_isPerfectRelativeTo
    (h0A1K : FlatDerivedBaseChange B S hS)
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) :=
  h0A1K sq (isQuasiCompact_of_universallyClosed B S hS X.2 Y.2 f.hom hproper.universallyClosed)
    (isQuasiSeparated_of_isSeparated B S hS hproper.isSeparated) hflat E
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE.1)

end BaseChange

/-! ### Perfectness at the limit of a Noetherian proper Situation 0DKU -/

namespace RelativeDescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation B S hS hZ I)

/-- The base changes of a Situation 0DKU are of finite presentation once they are proper. -/
theorem isFinitePresentation_stageStructure (i : D.LaterIndex)
    (hp : IsProper B S hS (D.stageStructure i).hom) :
    IsFinitePresentation B S hS (D.stageStructure i).hom :=
  ⟨D.isLocallyOfFinitePresentation_stageStructure i,
    isQuasiCompact_of_universallyClosed B S hS (D.stageSource i).2 (D.stageTarget i).2 _
      hp.universallyClosed,
    isQuasiSeparated_of_isSeparated B S hS hp.isSeparated⟩

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

/-- **Stacks 0DKX, perfectness, at the limit of a Noetherian proper Situation 0DKU**
(unregistered). If the limit is a limit of schemes, the stages `Yᵢ` are Noetherian and the base
changes `Xᵢ ⟶ Yᵢ` are proper, then for a `Y`-perfect `E` on the limit `X` the direct image
`Rf_*E` is perfect. As in the source:
`E` is the pullback of a `Yᵢ`-perfect `Eᵢ` (Stacks 0DKW), `Rfᵢ_*Eᵢ` is perfect (Stacks 08IS), its
pullback to `Y` is perfect (Stacks 08H6) and is `Rf_*E` by the base change assertion.

* `h0A1K`: Stacks 0A1K, not yet proved here.
* `h08IS`: Stacks 08IS, not yet proved here.
* `h0DKW`: Stacks 0DKW for `D`, not yet proved here.
* `hstage`: internal, pending (`AlgebraicGeometry.Space.NoetherianStageHypotheses`). -/
theorem isPerfect_limitPushforward_of (h0A1K : FlatDerivedBaseChange B S hS)
    (h08IS : ProperSupportPerfectDirectImage B S hS) (h0DKW : D.RelativelyPerfectColimit)
    (hD : D.IsSchemeLimit) (hstage : NoetherianStageHypotheses B S hS)
    (hnoeth : ∀ i : D.LaterIndex, IsNoetherian B S hS hZ (D.stageTarget i).1)
    (hprop : ∀ i : D.LaterIndex, IsProper B S hS (D.stageStructure i).hom)
    (E : derivedModules B S hS D.limitSource) (hE : D.IsLimitPerfect E) :
    (smallEtaleRingedSite B S hS D.limitTarget.1 D.limitTarget.2).IsPerfect
      ((derivedModulePushforward B S hS D.limitStructure).obj E) := by
  obtain ⟨i, Eᵢ, hEᵢ, ⟨e⟩⟩ := (h0DKW hD).2.2.1 E hE
  have hfp := D.isFinitePresentation_stageStructure i (hprop i)
  have hlft : IsLocallyOfFiniteType B S hS (D.stageStructure i).hom :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1
  obtain ⟨hb, hsupp, htor⟩ := hstage hZ (D.stageStructure i) (hprop i)
    (D.isFlat_stageStructure i) hfp (hnoeth i) Eᵢ hEᵢ
  have hperf := h08IS hZ (D.stageStructure i) hlft hfp.2.2 (hnoeth i) Eᵢ hb (hsupp hlft) _ htor
  have hperf' := RingedSite.isPerfect_of_iso _ hperf
    ((derivedModulePushforwardTotalRightDerivedIso B S hS (D.stageStructure i)).app Eᵢ).symm
  have hpull := isPerfect_smallEtaleDerivedModulePullback (D.targetProjection i) _ hperf'
  have hbc := isIso_smallEtaleDerivedModuleBaseChangeMap_of_isPerfectRelativeTo B S hS h0A1K
    (D.isPullback_sourceProjection i) (hprop i) (D.isFlat_stageStructure i) hfp Eᵢ
    hEᵢ
  exact RingedSite.isPerfect_of_iso _ hpull (@asIso _ _ _ _ _ hbc ≪≫
    (derivedModulePushforward B S hS D.limitStructure).mapIso e)

/-- **Stacks 0DKX, perfectness, at the limit of a Noetherian proper Situation 0DKU**
(unregistered), with the hypotheses of Stacks 08IS at the stages proved
(`AlgebraicGeometry.Space.noetherianStageHypotheses`).

* `h0A1K`: Stacks 0A1K, not yet proved here.
* `h08IS`: Stacks 08IS, not yet proved here.
* `h0DKW`: Stacks 0DKW for `D`, not yet proved here. -/
theorem isPerfect_limitPushforward_of_isNoetherian (h0A1K : FlatDerivedBaseChange B S hS)
    (h08IS : ProperSupportPerfectDirectImage B S hS) (h0DKW : D.RelativelyPerfectColimit)
    (hD : D.IsSchemeLimit)
    (hnoeth : ∀ i : D.LaterIndex, IsNoetherian B S hS hZ (D.stageTarget i).1)
    (hprop : ∀ i : D.LaterIndex, IsProper B S hS (D.stageStructure i).hom)
    (E : derivedModules B S hS D.limitSource) (hE : D.IsLimitPerfect E) :
    (smallEtaleRingedSite B S hS D.limitTarget.1 D.limitTarget.2).IsPerfect
      ((derivedModulePushforward B S hS D.limitStructure).obj E) :=
  D.isPerfect_limitPushforward_of h0A1K h08IS h0DKW hD (noetherianStageHypotheses B S hS) hnoeth
    hprop E hE

end RelativeDescentSituation

/-! ### The perfectness assertion -/

section Perfectness

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0DKX, perfectness** (unregistered). For a flat, proper, finitely presented
`f : X ⟶ Y` of algebraic spaces and a `Y`-perfect `E ∈ D(𝒪_X)`, `Rf_*E` is a perfect object of
`D(𝒪_Y)`.

* `h0A1K`: Stacks 0A1K at every base scheme, not yet proved here.
* `h08IS`: Stacks 08IS at every base scheme, not yet proved here.
* `h0DKW`: Stacks 0DKW at every base scheme, not yet proved here.
* `hstage`, `hred`: internal, pending (`AlgebraicGeometry.Space.NoetherianStageHypotheses`,
  `AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent`). -/
theorem isPerfect_derivedModulePushforward_of_isPerfectRelativeTo
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (hstage : ∀ {T : Scheme.{u}} (hT : B.Contains T), NoetherianStageHypotheses B T hT)
    (hred : PerfectnessReducesToNoetherianDescent B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((derivedModulePushforward B S hS f).obj E) :=
  hred f hproper hflat hfp E hE fun I _ _ D hD hnoeth hprop E' hE' =>
    D.isPerfect_limitPushforward_of (h0A1K _) (h08IS _)
      (h0DKW _ B.contains_terminal I D) hD (hstage _) hnoeth hprop E' hE'

/-- **Stacks 0DKX, perfectness, for `spaceDerivedPushforward`** (unregistered): the same
statement for the model `AlgebraicGeometry.Space.spaceDerivedPushforward` of `Rf_*`. Same
pending hypotheses as
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_isPerfectRelativeTo`. -/
theorem isPerfect_spaceDerivedPushforward_of_isPerfectRelativeTo
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (hstage : ∀ {T : Scheme.{u}} (hT : B.Contains T), NoetherianStageHypotheses B T hT)
    (hred : PerfectnessReducesToNoetherianDescent B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) :=
  RingedSite.isPerfect_of_iso _
    (isPerfect_derivedModulePushforward_of_isPerfectRelativeTo B S hS h0A1K h08IS h0DKW hstage
      hred f hproper hflat hfp E hE)
    ((derivedModulePushforwardIsoSpaceDerivedPushforward B S hS f).app E)

/-! ### Stacks 0DKX -/

/-- **Stacks 0DKX** (unregistered). Let `f : X ⟶ Y` be a flat, proper, finitely presented
morphism of algebraic spaces and `E ∈ D(𝒪_X)` a `Y`-perfect object. Then `Rf_*E` is a perfect
object of `D(𝒪_Y)` and its formation commutes with arbitrary base change: for every cartesian
square `X' = X ×_Y Y'` the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of Stacks 07A7 is an
isomorphism.

* `h0A1K`: Stacks 0A1K at every base scheme, not yet proved here.
* `h08IS`: Stacks 08IS at every base scheme, not yet proved here.
* `h0DKW`: Stacks 0DKW at every base scheme, not yet proved here.
* `hstage`, `hred`: internal, pending (`AlgebraicGeometry.Space.NoetherianStageHypotheses`,
  `AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent`). -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (hstage : ∀ {T : Scheme.{u}} (hT : B.Contains T), NoetherianStageHypotheses B T hT)
    (hred : PerfectnessReducesToNoetherianDescent B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  ⟨isPerfect_spaceDerivedPushforward_of_isPerfectRelativeTo B S hS h0A1K h08IS h0DKW hstage hred
      f hproper hflat hfp E hE,
    fun _ _ _ hpb => isIso_smallEtaleDerivedModuleBaseChangeMap_of_isPerfectRelativeTo B S hS
      (h0A1K hS) hpb hproper hflat hfp E hE⟩

/-- **The 0DKX input of the proof of Stacks 0DKY**,
`AlgebraicGeometry.Space.RelativelyPerfectPushforwardBaseChange`, from Stacks 0DKX
(`AlgebraicGeometry.Space.isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo`). Same pending
hypotheses. -/
theorem relativelyPerfectPushforwardBaseChange_of
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (hstage : ∀ {T : Scheme.{u}} (hT : B.Contains T), NoetherianStageHypotheses B T hT)
    (hred : PerfectnessReducesToNoetherianDescent B S hS) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  fun f hproper hflat hfp E hE =>
    isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo B S hS h0A1K h08IS h0DKW hstage hred
      f hproper hflat hfp E hE

/-- **Stacks 0DKX** (unregistered), with the hypotheses of Stacks 08IS at a Noetherian stage
proved (`AlgebraicGeometry.Space.noetherianStageHypotheses`): the form of
`AlgebraicGeometry.Space.isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo` without `hstage`.

* `h0A1K`: Stacks 0A1K at every base scheme, not yet proved here.
* `h08IS`: Stacks 08IS at every base scheme, not yet proved here.
* `h0DKW`: Stacks 0DKW at every base scheme, not yet proved here.
* `hred`: internal, pending (`AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent`). -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_reduction
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (hred : PerfectnessReducesToNoetherianDescent B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo B S hS h0A1K h08IS h0DKW
    (fun hT => noetherianStageHypotheses B _ hT) hred f hproper hflat hfp E hE

/-- **The 0DKX input of the proof of Stacks 0DKY**,
`AlgebraicGeometry.Space.RelativelyPerfectPushforwardBaseChange`, without `hstage`
(`AlgebraicGeometry.Space.noetherianStageHypotheses`). Pending: `h0A1K`, `h08IS`, `h0DKW` (held
elsewhere) and `hred` (internal). -/
theorem relativelyPerfectPushforwardBaseChange_of_reduction
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (hred : PerfectnessReducesToNoetherianDescent B S hS) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of B S hS h0A1K h08IS h0DKW
    (fun hT => noetherianStageHypotheses B _ hT) hred

end Perfectness

end AlgebraicGeometry.Space

end
