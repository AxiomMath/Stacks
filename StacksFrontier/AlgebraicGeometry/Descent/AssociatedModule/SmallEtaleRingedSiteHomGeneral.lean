module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a morphism of ringed sites

Stacks 08H7 is the morphism `ε` of Equation 75.4.0.1, already packaged as an
`AlgebraicGeometry.RingedToposSiteHom` by
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`.  That packaging records only continuity
of the underlying functor.  This module supplies the *site* condition for `ε` and repackages it
as an `AlgebraicGeometry.RingedSite.HomGeneral`, which is the form that carries a morphism of
topoi.

Two universes are in play and they do not agree.  The small étale site of `S` has objects in
`Type (u + 1)` and morphisms in `Type u`, so `AlgebraicGeometry.smallEtaleRingedSite` is a
`RingedSite.{u + 1, u, u}`, whereas the small Zariski site, presented by the opens of the
underlying space, is a `RingedSite.{u, u, u}`.  `AlgebraicGeometry.RingedSite.Hom` requires the
objects and morphisms of both sites to share one universe and so cannot hold `ε`;
`AlgebraicGeometry.RingedSite.HomGeneral` asks only that the two sections universes agree, and
they do, both being `u`.

The site condition has to be read at the universe of the structure rings, which is the universe
at which a ringed topos declares its underlying topos.  Mathlib's criterion for it
(`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback`, Stacks 00X5) is available only
for two genuinely small sites in one universe, and the small étale site is not one.  The small
étale site is however essentially small at `u`
(`AlgebraicGeometry.SmallEtale.essentiallySmall`), so the criterion applies after transporting
the target to a small model at `Type u`, and the left adjoint it produces is carried back by
conjugation with the restriction equivalence.  Only the target needs transporting: the small
Zariski site is presented by `S.Opens`, which is already small at `u`.

This is the transport of `AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites_ringUniverse`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RingedSiteHom.lean`), run
for `ε` rather than for small étale base change, and with one side rather than two.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom`: `ε` as a morphism of ringed sites in
  the sense of Stacks 03AD, part (2), at independent object universes.
* `AlgebraicGeometry.SmallEtale.toZariskiToposHom`: the morphism of topoi underlying `ε`.

## Main results

* `AlgebraicGeometry.SmallEtale.opensToSmallEtale_isMorphismOfSites`: the inclusion of the small
  Zariski site of `S` into its small étale site defines a morphism of sites, for sheaves of sets
  valued in the universe of the sections of the structure sheaves.
* `AlgebraicGeometry.SmallEtale.hasWeakSheafify_ringedTopos_J` and
  `AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_ringedTopos_J`: the existing
  sheafification instances of the small étale site, restated at the `(ringedTopos B S hS).J`
  spelling, which is what the pullback of modules asks for.
* `AlgebraicGeometry.SmallEtale.pullbackToposGeneral_toZariskiRingedToposHom`: the pullback of
  sheaves of modules along `ε`, at independent universes, is the associated-module functor.

## What this unblocks

`AlgebraicGeometry.SmallEtale.toZariskiToposHom` is a `CategoryTheory.MorphismOfTopoi` for `ε`.
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean`
carries exactness of `ε^*` — the second assertion of Stacks 08H8 — as the explicit hypothesis
`[PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]`, and records that the obstruction to
discharging it is that the geometric factor of
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` needs a morphism of topoi
for `ε`, which was not available.  It is available here.

What is left of that hypothesis is exactly two comparisons, and neither is done in this module;
no `@[stacks 08H8]` attribute is claimed.  The morphism of ringed *topoi* that the criterion
consumes is already a construction and not an existential —
`AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom`
(`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/IsLocallyRingedCriterion.lean`),
the witness of `HomGeneral.exists_associatedRingedToposHom` made into a `def` — and
`pullbackModules_exact_of_isFlatMap` applies to it at `ε` once the two instances above are in
scope.  Its flatness input is `IsFlatMapULift` of
`(toZariskiRingedSiteHom B S hS).toRingedToposHom.fSharpInverseImage`, a map
`ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}` whose source is the *topos* inverse image
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor`; the library's flatness
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap` (Stacks 0GNA) is for the
same map with the source spelled `AlgebraicGeometry.SmallEtale.inverseImageCommRing`, the
sheaf pullback of commutative rings along the site functor.  The two sources are not
definitionally equal; they are both left adjoints of the same pushforward, so they are
identified by `CategoryTheory.Adjunction.leftAdjointUniq` through
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, and the two structure maps correspond
under that identification because each is the transpose of
`AlgebraicGeometry.SmallEtale.commRingStructureMap`.  The second comparison then identifies
`Stacks.Sheaves.RingedToposModules.pullbackModules` of that morphism of ringed topoi with
`AlgebraicGeometry.SmallEtale.associatedModule`, which is the `HomGeneral` analogue of
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Conjugating a left adjoint along an equivalence on the target -/

section Conjugate

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Conjugating a left adjoint by an equivalence on one side: if `P₀ ⊣ W ⋙ R` with `W` an
equivalence, then `P₀ ⋙ W` is a left adjoint of `R`.

This is the one-sided case of the conjugation used for small étale base change in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RingedSiteHom.lean`, which
transports both sites; here the source site is already small, so only the target is
transported. -/
private def adjunctionOfConjugateTarget
    {A : Type u₁} [Category.{v₁} A] {B₀ : Type u₂} [Category.{v₂} B₀]
    {E : Type u₃} [Category.{v₃} E]
    (W : B₀ ⥤ E) (R : E ⥤ A) (P₀ : A ⥤ B₀) [W.IsEquivalence] (adj₀ : P₀ ⊣ W ⋙ R) :
    P₀ ⋙ W ⊣ R :=
  (adj₀.comp W.asEquivalence.toAdjunction).ofNatIsoRight
    (W.asEquivalence.invFunIdAssoc R)

end Conjugate

/-! ### The site condition for `ε` at the universe of the structure rings -/

/-- The small étale topology of `S`, transported to a small model of the small étale site at the
universe of the structure rings. -/
private abbrev epsilonSmallModelTopology :
    GrothendieckTopology (SmallModel.{u} (SmallEtale B S hS)) :=
  (equivSmallModel.{u} (SmallEtale B S hS)).inverse.inducedTopology (topology B S hS)

/-- The inclusion of the small Zariski site, followed by the comparison of the small étale site
with its small model.  Both sides of this functor are genuinely small at `u`. -/
private abbrev opensToSmallModelEtale :
    S.Opens ⥤ SmallModel.{u} (SmallEtale B S hS) :=
  opensToSmallEtale B S hS ⋙ (equivSmallModel.{u} (SmallEtale B S hS)).functor

private instance isContinuous_opensToSmallModelEtale :
    (opensToSmallModelEtale B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (epsilonSmallModelTopology B S hS) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS) _

/-- The comma categories indexing the right Kan extension along the comparison of the small
étale site with its small model have limits of sets in universe `u`, being essentially small
at `u`.  This is what makes restriction along that comparison an equivalence at `Type u`. -/
private instance hasLimitsOfShape_structuredArrow_epsilon_functor_op
    (W : (SmallModel.{u} (SmallEtale B S hS))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (SmallEtale B S hS)).functor.op) (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (equivSmallModel.{u} (SmallEtale B S hS)).functor.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Restriction of sheaves of sets along the comparison of the small étale site with its small
model.  It is an equivalence, the comparison being a dense subsite inclusion. -/
private abbrev epsilonSmallModelRestrict :
    Sheaf (epsilonSmallModelTopology B S hS) (Type u) ⥤ Sheaf (topology B S hS) (Type u) :=
  (equivSmallModel.{u} (SmallEtale B S hS)).functor.sheafPushforwardContinuous
    (Type u) (topology B S hS) (epsilonSmallModelTopology B S hS)

/-- The direct image of `ε` on sheaves of sets valued in the universe of the structure rings. -/
private abbrev epsilonDirectImage :
    Sheaf (topology B S hS) (Type u) ⥤ Sheaf (Opens.grothendieckTopology ↥S) (Type u) :=
  (opensToSmallEtale B S hS).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology ↥S) (topology B S hS)

/-- The inverse image of the transported inclusion, on the small model. -/
private abbrev epsilonSmallModelPullback :
    Sheaf (Opens.grothendieckTopology ↥S) (Type u) ⥤
      Sheaf (epsilonSmallModelTopology B S hS) (Type u) :=
  (opensToSmallModelEtale B S hS).sheafPullback (Type u)
    (Opens.grothendieckTopology ↥S) (epsilonSmallModelTopology B S hS)

/-- The direct image of the transported inclusion is the direct image of `ε`, precomposed with
restriction along the comparison with the small model.  This holds by `rfl`, both sides being
the direct image of the same composite functor. -/
private theorem sheafPushforwardContinuous_opensToSmallModelEtale :
    (epsilonSmallModelRestrict B S hS) ⋙ (epsilonDirectImage B S hS) =
      (opensToSmallModelEtale B S hS).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ↥S) (epsilonSmallModelTopology B S hS) := rfl

/-- **The inclusion of the small Zariski site of `S` into its small étale site defines a
morphism of sites**, for sheaves of sets valued in the universe `u` of the sections of the
structure sheaves.

This is the input `ε` needs to be a morphism of ringed sites.  The instance
`AlgebraicGeometry.SmallEtale.isContinuous_opensToSmallEtale` gives only continuity, and
`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback` (Stacks 00X5) is unavailable
directly, being stated for two sites in a single universe while the small étale site has its
objects one universe above its morphisms.

The left exact left adjoint of the direct image is the pullback along the transported inclusion
into a small model of the small étale site at `Type u`, which is left exact by Stacks 00X5 at
the universe of a genuinely small site, conjugated by the restriction equivalence along the
comparison with that small model. -/
public instance opensToSmallEtale_isMorphismOfSites :
    IsMorphismOfSites.{u} (opensToSmallEtale B S hS)
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  have _hP₀ : PreservesFiniteLimits (epsilonSmallModelPullback B S hS) :=
    Functor.preservesFiniteLimits_sheafPullback _ _ _
  have hL : PreservesFiniteLimits
      (epsilonSmallModelPullback B S hS ⋙ epsilonSmallModelRestrict B S hS) :=
    comp_preservesFiniteLimits _ _
  { __ := (inferInstance : (opensToSmallEtale B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (topology B S hS))
    hasExactLeftAdjoint :=
      ⟨epsilonSmallModelPullback B S hS ⋙ epsilonSmallModelRestrict B S hS,
        ⟨adjunctionOfConjugateTarget (epsilonSmallModelRestrict B S hS)
          (epsilonDirectImage B S hS) (epsilonSmallModelPullback B S hS)
          (((opensToSmallModelEtale B S hS).sheafAdjunctionContinuous (Type u)
              (Opens.grothendieckTopology ↥S) (epsilonSmallModelTopology B S hS)).ofNatIsoRight
            (eqToIso (sheafPushforwardContinuous_opensToSmallModelEtale B S hS).symm))⟩,
        hL⟩ }

/-! ### `ε` as a morphism of ringed sites -/

/-- **Stacks 070R, and the `ε` of Stacks 08H7 Equation 75.4.0.1**, as a morphism of ringed sites
at independent object universes: the continuous inclusion of the small Zariski site of `S` into
its small étale site, now known to define a morphism of sites at the universe of the structure
rings, together with the identification of the sections of `𝒪_S` over an open with the functions
on it.

This is the same geometric datum and the same structure map as
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`, which carries Stacks 08H7; what is added
is the site condition, and with it the morphism of topoi.  No tag is attached here: 08H7 is
registered on that declaration and this one does not restate it. -/
@[sga "4 VII 4.2.2"]
public def toZariskiRingedSiteHom :
    RingedSite.HomGeneral (smallEtaleRingedSite B S hS) S.zariskiRingedSite where
  u := opensToSmallEtale B S hS
  isMorphismOfSites := opensToSmallEtale_isMorphismOfSites B S hS
  fsharp := commRingStructureMap B S hS

/-- The underlying functor of `toZariskiRingedSiteHom` is `opensToSmallEtale`. -/
@[simp]
public theorem toZariskiRingedSiteHom_u :
    (toZariskiRingedSiteHom B S hS).u = opensToSmallEtale B S hS := rfl

/-- The structure map of `toZariskiRingedSiteHom` is `commRingStructureMap`. -/
@[simp]
public theorem toZariskiRingedSiteHom_fsharp :
    (toZariskiRingedSiteHom B S hS).fsharp = commRingStructureMap B S hS := rfl

/-- **Stacks 00XC for `ε`.** The morphism of topoi
`Sh(S_étale) ⟶ Sh(S_Zar)` underlying `ε`.

This is the `CategoryTheory.MorphismOfTopoi` whose absence
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean`
records as the obstruction to discharging the exactness assertion of Stacks 08H8. -/
@[sga "4 VII 4.2.2"]
public abbrev toZariskiToposHom :
    MorphismOfTopoi (Sheaf (smallEtaleRingedSite B S hS).J (Type u))
      (Sheaf S.zariskiRingedSite.J (Type u)) :=
  (toZariskiRingedSiteHom B S hS).toposHom

/-! ### The pullback of modules along `ε` -/

/-- The pushforward of sheaves of modules along `ε` is a right adjoint, the associated-module
functor of Stacks 03DU (4) being its left adjoint.

This is `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` read at the spelling the
pullback of Stacks 03D6 asks for.  The restatement is needed because the target of `fSharpRing`
is spelled with `Functor.sheafPushforwardContinuous`, which does not unfold at instance
transparency. -/
public instance sheafPushforward_toZariskiRingedToposHom_isRightAdjoint :
    (SheafOfModules.pushforward.{u}
      (toZariskiRingedToposHom B S hS).fSharpRing).IsRightAdjoint :=
  (associatedModuleAdjunction B S hS).isRightAdjoint

/-- Sheafification of abelian presheaves on the small étale site, at the spelling
`(ringedTopos B S hS).J` rather than `topology B S hS`.  `AlgebraicGeometry.SmallEtale.ringedTopos`
does not unfold at instance transparency, so the instance
`AlgebraicGeometry.SmallEtale.hasWeakSheafify_smallEtale` is not found at that spelling. -/
public instance hasWeakSheafify_ringedTopos_J :
    HasWeakSheafify (ringedTopos B S hS).J AddCommGrpCat.{u} :=
  (inferInstance : HasWeakSheafify (topology B S hS) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences of abelian presheaves on the small étale site, at
the `(ringedTopos B S hS).J` spelling, for the same reason as
`hasWeakSheafify_ringedTopos_J`. -/
public instance wEqualsLocallyBijective_ringedTopos_J :
    (ringedTopos B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  (inferInstance : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- **Stacks 03D6, part (2), at `ε`.** The pullback of sheaves of modules along `ε`, in the
general form of
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, is the associated-module functor
`𝓕 ↦ 𝓕^a` of Stacks 03DU (4).

This is what Remark 03FH asserts, and it holds by `rfl`: `ε`'s structure map read on sheaves of
not necessarily commutative rings is `AlgebraicGeometry.SmallEtale.structureMap`
(`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom_fSharpRing`), and both functors are
`SheafOfModules.pullback` of it.

The point of the statement is the *left* hand side.  Stacks 03D6, part (2) in the form stated for
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is not typeable at `ε` at all, requiring
both ringed topoi to be `RingedTopos.{w, w, w}` while the small étale site of a scheme is a
`RingedTopos.{u, u + 1, u}`; the general form is, and at `ε` it is the functor the development
already uses. -/
public theorem pullbackToposGeneral_toZariskiRingedToposHom :
    (toZariskiRingedToposHom B S hS).pullbackToposGeneral = associatedModule B S hS := rfl

/-! ### What the exactness of `ε^*` reduces to -/

/-- Sheafification of abelian presheaves on the small étale site, at the
`(smallEtaleRingedSite B S hS).toRingedTopos.J` spelling.  This is the spelling the
morphism of ringed topoi attached to a `RingedSite.HomGeneral` is stated at, and neither
`AlgebraicGeometry.smallEtaleRingedSite` nor `AlgebraicGeometry.RingedSite.toRingedTopos`
unfolds at instance transparency. -/
public instance hasWeakSheafify_toRingedTopos_addCommGrpCat :
    HasWeakSheafify (smallEtaleRingedSite B S hS).toRingedTopos.J AddCommGrpCat.{u} :=
  (inferInstance : HasWeakSheafify (topology B S hS) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences of abelian presheaves on the small étale site,
at the `(smallEtaleRingedSite B S hS).toRingedTopos.J` spelling. -/
public instance wEqualsLocallyBijective_toRingedTopos_addCommGrpCat :
    (smallEtaleRingedSite B S hS).toRingedTopos.J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  (inferInstance : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- **Stacks 04JC, second assertion, read at `ε`.**  The pullback of sheaves of modules along
the morphism of ringed topoi attached to `ε` is exact as soon as the inverse-image form of its
structure map is flat.

This is `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` applied to
`AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` of `ε`, and it is recorded to pin
down what the exactness assertion of Stacks 08H8 still needs.  The criterion was unavailable
before `toZariskiToposHom`, having no morphism of topoi for `ε` to consume; it is available
now, and the hypothesis `hflat` is the whole of what is left.

The hypothesis is *not* the library's flatness.  Stacks 0GNA is
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`, which asserts the same
flatness for `AlgebraicGeometry.SmallEtale.inverseImageStructureMap`, whose source is the sheaf
pullback of commutative rings along the site functor rather than the topos inverse image
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor`.  The two sources are both left
adjoints of the same pushforward and so are identified by
`CategoryTheory.Adjunction.leftAdjointUniq`; transporting flatness across that identification
is not done here, and at the small étale site it cannot go through
`AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatMap`, which asks the objects, the
morphisms and the sections to share one universe while the objects here are one universe
above. -/
public theorem exactFunctor_pullbackModules_toZariskiRingedSiteHom
    (hflat : SheafOfModules.IsFlatMapULift
      (toZariskiRingedSiteHom B S hS).toRingedToposHom.fSharpInverseImage) :
    PreservesFiniteLimits
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (smallEtaleRingedSite B S hS).toRingedTopos)
        (Y := S.zariskiRingedSite.toRingedTopos)
        (toZariskiRingedSiteHom B S hS).toRingedToposHom.toRingedToposModulesHom) :=
  ((exactFunctor_iff _).mp
    (Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
      (toZariskiRingedSiteHom B S hS).toRingedToposHom hflat)).1

end SmallEtale

end AlgebraicGeometry

end
