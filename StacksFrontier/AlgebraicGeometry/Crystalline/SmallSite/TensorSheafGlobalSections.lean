module

public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FMapGlobalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafTransitionSurjectivity

/-!
# Blocker (2) of [Stacks, Tag 07LF]: the `f`-map of the coefficient sheaf on global sections

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` affine, a sheaf of
`𝒪_{X/S}`-modules `F` on the small crystalline site `Cris(X/S)` and an `i : ℕ`.  This module
proves

`...SmallSite.HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i)`,

the abelian form of hypothesis (2) of [Stacks, Tag 07JN] for the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF], from hypotheses (1) and (2) of
[Stacks, Tag 07JN] on `F` and the standing affineness of `X`, and from nothing else.  That is
**blocker (2) of [Stacks, Tag 07LF]**.

`SmallSite/TensorSheafTransitionSurjectivity.lean` carried the question to the ambient scheme `T'`
of the target of a morphism of `Cris(X/S)` between objects over the whole of `X` whose map on
ambient schemes is a closed immersion, reduced it to the single hypothesis `happ` of
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app` —
that the `f`-map, locally surjective by
`...SmallSite.isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf`, is surjective on
global sections of `T'` — and supplied the epimorphism of sheaves of modules
`...SmallSite.epi_tensorRestrictionFMapSheaf` that the argument of
`SmallSite/FMapGlobalSurjectivity.lean` takes as its input.  The module documentation of that file
names the two steps which remained, and both are taken here.

1. **The `f`-map read over `𝒪_{T'}`, with both sides quasi-coherent.**
   `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` asks for an epimorphism of
   `AlgebraicGeometry.Scheme.Modules` with both sides quasi-coherent, while
   `...SmallSite.tensorRestrictionFMapSheaf` is a morphism of sheaves of modules over
   `...Thickening.ringRestrictionSheaf`, the restriction of `𝒪_{X/S}` to `T'`.  Restricting scalars
   along `ringRestrictionSheafIso`, the identification of that sheaf of rings with `𝒪_{T'}` whose
   components are `...SmallSite.CrystallineThickening.sectionsIso`, turns the source into a
   quasi-coherent `𝒪_{T'}`-module, and the direct image side is the scheme-theoretic pushforward of
   the source over `T`, hence quasi-coherent by [Stacks, Tag 02KG].  The `f`-map itself is
   `𝒪_{T'}`-linear, and that linearity is exactly
   `...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply`, whose bundled form is the
   commuting square of sheaves of rings
   `ringRestrictionSheafIso_inv_comp_smallRingRestrictionSheafFMap` below.  So
   `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` applies on `⊤`, the ambient scheme of
   an object over the whole of an affine `X` being affine.
2. **The sections of the crystalline sheafification over the object.**  `happ` is about sections of
   the *crystalline* sheafification, while step 1 delivers sections of a *Zariski* sheafification
   on `T'`.  `...CrystallineThickening.restrictOpenSheafifyIso` of
   `SmallSite/SheafifySections.lean` identifies the restriction to the ambient scheme of the
   crystalline sheafification with the Zariski sheafification of the restricted presheaf tensor
   product, at the coefficient universe `u + 1`; the square that the two `f`-maps have to fit into
   commutes by `...CrystallineThickening.restrictOpenSheafify_hom_ext`, both composites agreeing
   after precomposition with the crystalline sheafification unit — by
   `...SmallSite.toSheafify_comp_tensorRestrictionFMapSheaf` together with the naturality of
   `CategoryTheory.toSheafify`.  Transporting the surjectivity of step 1 across the two
   isomorphisms gives `happ`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `...CrystallineThickening.ringRestrictionSheafIso` — **the restriction of `𝒪_{X/S}` to the
  ambient scheme of an object, identified with the structure sheaf of rings of that scheme**, as an
  isomorphism of sheaves of rings whose components are
  `...CrystallineThickening.sectionsIso`.
* `ambientTensorRestrictionSheaf` and `ambientDirectImageTensorRestrictionSheaf` — the restriction
  of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to the ambient scheme of an object, and its direct image along the
  map on ambient schemes, both as sheaves of `𝒪`-modules on a scheme.
* `ambientTensorRestrictionFMap` — **the `f`-map between them, as a morphism of
  `AlgebraicGeometry.Scheme.Modules`.**
* `tensorRestrictionSheafULift`, `tensorRestrictionSheafULiftUnit` and
  `tensorRestrictionFMapULift` — the Zariski sheafification of the restricted presheaf tensor
  product, its unit and the `f`-map, all read at the coefficient universe `u + 1` of the cohomology
  of `Cris(X/S)`.
* `restrictOpenTensorSheafIso` — **the restriction to the ambient scheme of an object of the
  coefficient sheaf of [Stacks, Tag 07LF] is that Zariski sheafification.**

## Main results

* `ringRestrictionSheafIso_inv_comp_smallRingRestrictionSheafFMap` — **the commuting square of
  sheaves of rings on `T'`**: the `f`-map of the structure presheaf of `Cris(X/S)`, read through
  `ringRestrictionSheafIso` on both sides, is the comorphism of the map on ambient schemes.
* `isQuasicoherent_ambientTensorRestrictionSheaf` and
  `isQuasicoherent_ambientDirectImageTensorRestrictionSheaf` — both sides of that `f`-map are
  quasi-coherent, the first from hypothesis (1) of [Stacks, Tag 07JN], the second from it and
  [Stacks, Tag 02KG].
* `epi_ambientTensorRestrictionFMap` — it is an epimorphism, from hypothesis (2).
* `surjective_app_top_tensorRestrictionFMapSheaf` — **step 1**: it is surjective on global sections
  of the ambient scheme of the target.
* `restrictionFMap_comp_whiskerLeft_restrictOpenTensorSheafIso` — **step 2**: the square relating
  the `f`-map of the crystalline sheafification to the `f`-map of the Zariski one commutes.
* `surjective_restrictionFMap_app_top_tensorDifferentialFormsSheaf` — the hypothesis `happ` of
  `...hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app`,
  discharged.
* `hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf` — **blocker (2) of
  [Stacks, Tag 07LF]**: the abelian form of hypothesis (2) of [Stacks, Tag 07JN] for
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.
* `vanishing07LF_of_isZero_homology_sectionsComplex'` — **[Stacks, Tag 07LF] from one input**: the
  acyclicity of the complex `M(0) → M(1) → M(2) → ⋯` for the tensor sheaf.

## What is and is not proved

`hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf` is proved in full.  The
hypotheses it carries are exactly hypothesis (1) of [Stacks, Tag 07JN]
(`...SmallSite.IsLocallyQuasiCoherent F`), hypothesis (2)
(`...CohomologyRestriction.IsSurjectiveComparison F.val`) and the standing affineness
`[IsAffine S.X]` of [Stacks, Tag 07JN] and [Stacks, Tag 07LF].  **No hypothesis stands in for a
missing result.**  `IsAffine S.X` is used, and only used, to make the ambient scheme of an object
over the whole of `X` affine, through
`...SmallSite.isAffine_target_of_isIso_toX`; it is carried exactly as
`...SmallSite.hasSurjectiveWholeSpaceTransitions_abelianSheaf` carries it, and it is a hypothesis
of both tags rather than an addition.  No affineness of `S` is needed, no hypothesis on `i`, and
nothing about the crystal condition.

`vanishing07LF_of_isZero_homology_sectionsComplex'` is `Vanishing07LF S`, the statement of
[Stacks, Tag 07LF] verbatim, from **one** input: the acyclicity of the complex
`M(0) → M(1) → M(2) → ⋯` built from the tensor sheaf.  That is item 6 of the gap list of
`SmallSite/AffineCohomology.lean`, and it is not proved here or anywhere in the library: no term of
type `Crystalline.CosimplicialEnvelope` exists.

**No `@[stacks]` attribute is placed.**  [Stacks, Tag 07LF] is not proved, item 6 being open;
[Stacks, Tag 07JN] is already carried, in
`SmallSite/WholeSpaceSystemCohomology.lean`; and nothing here is a clause of [Stacks, Tag 07IP] or
of [Stacks, Tag 02KG] — these are steps inside a proof.

### Notes elsewhere that this closes or refines

The "What is and is not proved" note of `SmallSite/TensorSheafTransitionSurjectivity.lean` says
that `HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i)` "is **not** proved
here", and that "**Two things stand between that epimorphism and `happ`, and neither is proved
here**", listing the quasi-coherence of the direct image over `𝒪_{T'}` and the sections
identification, the second of which it calls "written out nowhere".  Both are now proved — the
first as `surjective_app_top_tensorRestrictionFMapSheaf`, the second as
`restrictionFMap_comp_whiskerLeft_restrictOpenTensorSheafIso` — and `happ` is discharged.  That
note's warning about *which* comparison of sheaves of rings to use was **correct and was
followed**: `ringRestrictionSheafIso` below is built from
`...CrystallineThickening.ringRestrictionIso`, whose components are
`...CrystallineThickening.sectionsIso`, and not from
`...Thickening.ringRestrictionSheafStructureIso`; with the latter the linearity datum
`...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply` does not apply.  That note also
says that "[Stacks, Tag 07LF] is not provable even with blocker (2) closed", item 6 remaining: that
is still true, and `vanishing07LF_of_isZero_homology_sectionsComplex'` is the exact form of it.

The "What still blocks [Stacks, Tag 07LF]" note of `SmallSite/TensorRestrictionVanishing.lean`
lists two things: "the `H¹` argument of `SmallSite/FMapGlobalSurjectivity.lean`, which needs an
epimorphism of sheaves of `𝒪_T`-modules with quasi-coherent kernel; this is input (2) of
[Stacks, Tag 07LF]", and the cosimplicial divided power envelope.  **The first is now closed**, and
two of its clauses were already wrong: no kernel is needed, both sides being quasi-coherent, and
the quasi-coherence of the *source* is the statement that file itself proves, as the note of
`SmallSite/TensorSheafTransitionSurjectivity.lean` had already recorded.  Only the second remains.

The "What is and is not proved" note of `SmallSite/SheafifySections.lean` says that "Input (2)
still needs the `H¹` argument of `SmallSite/FMapGlobalSurjectivity.lean`" and that "Nothing about
input (2) is proved here".  Both remain true of that file; input (2) is closed here, and the
sections identification it supplies is exactly what step 2 runs on.

The gap list of `SmallSite/AffineCohomology.lean` says that for [Stacks, Tag 07LF] the proof needs,
besides [Stacks, Tag 07JN], its items 5 and 6, item 5 being [Stacks, Tag 07KM] parts (1) and (2)
"for `F ⊗ Ω^i_{X/S}`", which "together give the two hypotheses of [Stacks, Tag 07JN]" for the
tensor sheaf.  **Item 5 is no longer a blocker**, and not because [Stacks, Tag 07KM] part (2) was
proved for the tensor sheaf: what the chain of [Stacks, Tag 07JN] consumes is the pair of abelian
predicates `...SmallSite.Vanishing07JJ` and
`...SmallSite.HasSurjectiveWholeSpaceTransitions`, the first proved in
`SmallSite/TensorRestrictionVanishing.lean` and the second here, each from hypotheses (1) and (2)
on `F` itself.  So [Stacks, Tag 07LF] rests on item 6 alone, which is what
`vanishing07LF_of_isZero_homology_sectionsComplex'` states.  No file is edited to record any of
this; the corrections are here.

## Implementation notes

**The two pushforward functors are never compared.**  The route named in the module documentation
of `SmallSite/TensorSheafTransitionSurjectivity.lean` was to identify `SheafOfModules.pushforward`
along `...CohomologyRestriction.restrictionFMap` with
`AlgebraicGeometry.Scheme.Modules.pushforward` by restriction of scalars, using that
`PresheafOfModules.pushforward` is a restriction of scalars of `PresheafOfModules.pushforward₀`.
That identification is not needed: `ambientTensorRestrictionFMap` is built with
`PresheafOfModules.homMk` from the underlying morphism of abelian presheaves of
`...SmallSite.tensorRestrictionFMapSheaf`, which is already the right morphism of abelian
presheaves, and only its `𝒪_{T'}`-linearity has to be checked.  That is the device
`...CohomologyRestriction.fmapModuleRestriction` of `SmallSite/FMapGlobalSurjectivity.lean` uses
for the same purpose, and the check is one `congrArg` over
`...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply`.  The commuting square of sheaves
of rings is recorded all the same, as
`ringRestrictionSheafIso_inv_comp_smallRingRestrictionSheafFMap`: it is the bundled form of that
semilinearity, and it is what says the two pushforwards agree.

**Both `f`-maps of the crystalline sheafification are written with
`sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)` rather than with
`(tensorDifferentialFormsSheaf F i).obj`.**  The two are equal by `rfl`
(`...SmallSite.tensorDifferentialFormsSheaf_obj`), but `rw` builds a motive which is rejected when
the sheafification is spelled the second way and
`...CohomologyRestriction.restrictOpenSheafifyIso` has produced the first: the rewrite fails with
"did not find an occurrence", the real complaint being that the motive is not type-correct at
reduced transparency.  Fixing the spelling in the statements removes the whole problem.  This is
stuck elaboration, not an obstruction.

For the same reason the sheaf condition which
`...CrystallineThickening.restrictOpenSheafify_hom_ext` consumes is introduced by a `have` with its
type written out, rather than passed as the `property` field of a pushforward of sheaves: passing
the field fixes the implicit target presheaf to the pushforward spelling, and the agreement square
then does not typecheck against the goal.

`...CohomologyRestriction.restrictionFMap` of the universe-lifted tensor presheaf is the universe
lift of the `f`-map of the tensor presheaf of modules definitionally, which is what lets
`restrictionFMap_comp_whiskerLeft_tensorRestrictionSheafULiftUnit` be a single `congrArg` of
`CategoryTheory.Functor.whiskerRight` over the module-universe square: no distribution of
`whiskerRight` over composition is needed, `AddCommGrpCat.uliftFunctor` preserving composition by
`rfl`.  The note of `SmallSite/TensorSheafTransitionSurjectivity.lean` records the same
definitional identity, used there through a `show`.

The instance-argument cliff that note records for
`CategoryTheory.Presheaf.IsLocallySurjective` is not met here: every use of that class below is at
a concrete coefficient category, so instance search has nothing undetermined to solve for, and the
local-bijectivity inputs of `...restrictOpenSheafifyIso` are supplied by `haveI` with no `@`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The restriction of `𝒪_{X/S}` as a sheaf of rings on the ambient scheme -/

namespace CrystallineThickening

/-- **The restriction of `𝒪_{X/S}` to the ambient scheme of an object of `Cris(X/S)` is the
structure sheaf of rings of that scheme**, as an isomorphism of sheaves of rings.

This is `...SmallSite.CrystallineThickening.ringRestrictionIso` read on sheaves, the forgetful
functor from sheaves to presheaves being fully faithful.  Its components are
`...SmallSite.CrystallineThickening.sectionsIso`, which is what makes
`...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply` the semilinearity datum of a
change of scalars along it; see the module documentation for why
`...Thickening.ringRestrictionSheafStructureIso` cannot be used in its place. -/
def ringRestrictionSheafIso (A : CrystallineThickening S) :
    Thickening.ringRestrictionSheaf A.obj ≅ A.obj.thickening.target.scheme.ringCatSheaf where
  hom := ⟨(ringRestrictionIso A).hom⟩
  inv := ⟨(ringRestrictionIso A).inv⟩
  hom_inv_id := Sheaf.hom_ext (ringRestrictionIso A).hom_inv_id
  inv_hom_id := Sheaf.hom_ext (ringRestrictionIso A).inv_hom_id

/-- The component of `ringRestrictionSheafIso` over an open of the ambient scheme is
`...SmallSite.CrystallineThickening.sectionsIso` there. -/
@[simp]
theorem ringRestrictionSheafIso_inv_hom_app (A : CrystallineThickening S)
    (W : A.obj.thickening.target.scheme.Opens) :
    (ringRestrictionSheafIso A).inv.hom.app (op W) = (sectionsIso A W).inv := rfl

end CrystallineThickening

/-- **The `f`-map of the structure sheaf of `Cris(X/S)` is the comorphism of the map on ambient
schemes**, as a commuting square of sheaves of rings on the ambient scheme of the target:

`𝒪_{T'} ⟶ (𝒪_{X/S})|_{T'} ⟶ f_* (𝒪_{X/S})|_T`  equals  `𝒪_{T'} ⟶ f_* 𝒪_T ⟶ f_* (𝒪_{X/S})|_T`,

the two identifications of a restriction of `𝒪_{X/S}` with a structure sheaf being
`ringRestrictionSheafIso`.  Its components are
`...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply`.

This is the bundled form of the semilinearity which makes `ambientTensorRestrictionFMap` below a
morphism of `𝒪_{T'}`-modules, and it is what says that the pushforward of sheaves of modules along
`...CohomologyRestriction.restrictionFMap` and the scheme-theoretic pushforward
`AlgebraicGeometry.Scheme.Modules.pushforward` agree after this change of scalars. -/
theorem ringRestrictionSheafIso_inv_comp_smallRingRestrictionSheafFMap
    {A B : CrystallineThickening S} (g : A ⟶ B) :
    (CrystallineThickening.ringRestrictionSheafIso B).inv ≫ smallRingRestrictionSheafFMap g =
      g.hom.targetHom.hom.toRingCatSheafHom ≫
        ((Opens.map g.hom.targetHom.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology B.obj.thickening.target.scheme)
          (Opens.grothendieckTopology A.obj.thickening.target.scheme)).map
            (CrystallineThickening.ringRestrictionSheafIso A).inv :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W => by
    obtain ⟨W⟩ := W
    exact RingCat.hom_ext (RingHom.ext fun r =>
      CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply g W r)))

/-! ### Step 1 -/

section Module

variable (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-- **The restriction to the ambient scheme of an object of the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF], as a sheaf of `𝒪_T`-modules.**  It is
`...SmallSite.tensorRestrictionSheaf` with its scalars read in the structure sheaf of the ambient
scheme rather than in the restriction of `𝒪_{X/S}`; the module is unchanged on sections, this
being a restriction of scalars along an isomorphism. -/
def ambientTensorRestrictionSheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    A.obj.thickening.target.scheme.Modules :=
  (SheafOfModules.restrictScalars (CrystallineThickening.ringRestrictionSheafIso A).inv).obj
    (tensorRestrictionSheaf A F i)

/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to the ambient scheme of an object is a
quasi-coherent `𝒪_T`-module**, for a locally quasi-coherent `F`.  This is
`...SmallSite.isQuasicoherentOnSite_tensorRestrictionSheaf` carried along
`ringRestrictionSheafIso`, quasi-coherence being preserved by restriction of scalars along an
isomorphism of sheaves of rings, and then read with Mathlib's quasi-coherence, the two notions
agreeing on the Zariski site of a scheme.

The only hypothesis carried is `hF`, hypothesis (1) of [Stacks, Tag 07JN]. -/
theorem isQuasicoherent_ambientTensorRestrictionSheaf {F : SheafOfModules.{u} (structureSheaf S)}
    (hF : IsLocallyQuasiCoherent F) (A : CrystallineThickening S) (i : ℕ) :
    (ambientTensorRestrictionSheaf A F i).IsQuasicoherent :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
    (CrystallineThickening.ringRestrictionSheafIso A).inv _
    (isQuasicoherentOnSite_tensorRestrictionSheaf hF A i)).isQuasicoherent

/-- **The direct image of `ambientTensorRestrictionSheaf` along the map on ambient schemes**, as a
sheaf of `𝒪_{T'}`-modules on the ambient scheme of the target.  Its sections over an open `W` of
`T'` are the sections of `ambientTensorRestrictionSheaf` over `f^{-1}W`. -/
def ambientDirectImageTensorRestrictionSheaf : B.obj.thickening.target.scheme.Modules :=
  (Scheme.Modules.pushforward g.hom.targetHom.hom).obj (ambientTensorRestrictionSheaf A F i)

/-- **That direct image is quasi-coherent** when the map on ambient schemes is a closed immersion:
a closed immersion is an affine morphism, and the direct image of a quasi-coherent module along an
affine morphism is quasi-coherent, which is [Stacks, Tag 02KG].

The hypotheses carried are `hF`, hypothesis (1) of [Stacks, Tag 07JN], and `hg`. -/
theorem isQuasicoherent_ambientDirectImageTensorRestrictionSheaf
    (hF : IsLocallyQuasiCoherent F) (hg : IsClosedImmersion g.hom.targetHom.hom) :
    (ambientDirectImageTensorRestrictionSheaf F i g).IsQuasicoherent :=
  have := hg
  have := isQuasicoherent_ambientTensorRestrictionSheaf hF A i
  inferInstanceAs (((Scheme.Modules.pushforward g.hom.targetHom.hom).obj
    (ambientTensorRestrictionSheaf A F i)).IsQuasicoherent)

/-- **The `f`-map of the restricted coefficient sheaf of [Stacks, Tag 07LF], as a morphism of
sheaves of `𝒪_{T'}`-modules on the ambient scheme of the target.**

Its underlying morphism of abelian presheaves is that of
`...SmallSite.tensorRestrictionFMapSheaf`, which is linear over
`...Thickening.ringRestrictionSheaf`; what has to be checked is that it is linear for the scalars
of the structure sheaf of `T'`, and that is
`...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply`, the component form of
`ringRestrictionSheafIso_inv_comp_smallRingRestrictionSheafFMap`.  This is the device
`...CohomologyRestriction.fmapModuleRestriction` uses, and it is why no comparison of the two
pushforward functors is needed; see the module documentation. -/
def ambientTensorRestrictionFMap :
    ambientTensorRestrictionSheaf B F i ⟶ ambientDirectImageTensorRestrictionSheaf F i g :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf B.obj).obj).map
      (tensorRestrictionFMapSheaf F i g).val)
    (fun W r m => by
      obtain ⟨W⟩ := W
      refine Eq.trans
        (((tensorRestrictionFMapSheaf F i g).val.app (op W)).hom.map_smul
          ((CrystallineThickening.sectionsIso B W).inv.hom r) m) ?_
      exact congrArg
        (fun s : (Thickening.ringRestrictionSheaf A.obj).obj.obj
            (op (g.hom.targetHom.hom ⁻¹ᵁ W)) =>
          s • id (α := ↥((tensorRestrictionSheaf A F i).val.obj
              (op (g.hom.targetHom.hom ⁻¹ᵁ W))))
            (((tensorRestrictionFMapSheaf F i g).val.app (op W)).hom m))
        (CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply g W r))⟩

/-- **That `f`-map is an epimorphism of sheaves of `𝒪_{T'}`-modules**, for a morphism of
`Cris(X/S)` between objects over the whole of `X` whose map on ambient schemes is a closed
immersion.  Epimorphisms of sheaves of modules are the morphisms whose underlying morphism of
abelian presheaves is locally surjective, and that morphism is the one underlying
`...SmallSite.epi_tensorRestrictionFMapSheaf`, so the change of scalars costs nothing.

The only hypothesis beyond the geometry is `hM`, hypothesis (2) of [Stacks, Tag 07JN]. -/
theorem epi_ambientTensorRestrictionFMap
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Epi (ambientTensorRestrictionFMap F i g) :=
  have := epi_tensorRestrictionFMapSheaf F i g hM hg hA hB
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (tensorRestrictionFMapSheaf F i g))

/-- **Step 1: the `f`-map of the restricted coefficient sheaf is surjective on global sections of
the ambient scheme of the target.**

Both sides are quasi-coherent `𝒪_{T'}`-modules and the map between them is an epimorphism, so
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` applies on the affine open `⊤`; the
ambient scheme of an object over the whole of an affine `X` is affine by
`...SmallSite.isAffine_target_of_isIso_toX`.  The statement is about the morphism of abelian
presheaves underlying `...SmallSite.tensorRestrictionFMapSheaf`, which is the same map of sections
in either reading.

The hypotheses carried are hypotheses (1) and (2) of [Stacks, Tag 07JN], the affineness of `X`,
that the map on ambient schemes is a closed immersion, and that both objects lie over the whole of
`X`. -/
theorem surjective_app_top_tensorRestrictionFMapSheaf [IsAffine S.X]
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Function.Surjective (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf B.obj).obj).map
        (tensorRestrictionFMapSheaf F i g).val).app
          (op (⊤ : B.obj.thickening.target.scheme.Opens)))) :=
  have := isAffine_target_of_isIso_toX B hB
  have := isQuasicoherent_ambientTensorRestrictionSheaf hF B i
  have := isQuasicoherent_ambientDirectImageTensorRestrictionSheaf F i g hF hg
  have := epi_ambientTensorRestrictionFMap F i g hM hg hA hB
  Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen B.obj.thickening.target.scheme
    (ambientTensorRestrictionFMap F i g) ⊤ (isAffineOpen_top _)

end Module

/-! ### Step 2 -/

/-- **The Zariski sheafification of the restriction to the ambient scheme of an object of the
presheaf tensor product `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, read at the coefficient universe `u + 1`** of
the cohomology of `Cris(X/S)`.  This is the abelian presheaf underlying
`...SmallSite.tensorRestrictionSheaf` with its sections pushed up one universe. -/
abbrev tensorRestrictionSheafULift (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (tensorRestrictionSheaf A F i).val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `tensorRestrictionSheafULift` is a Zariski sheaf: universe lifting of abelian groups preserves
limits of every size, so it carries sheaves to sheaves. -/
theorem isSheaf_tensorRestrictionSheafULift (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorRestrictionSheafULift A F i) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor.{u + 1, u}
    (tensorRestrictionSheaf A F i).isSheaf

/-- **The sheafification unit of `tensorRestrictionSheafULift`**: the universe lift of the Zariski
sheafification unit of the restricted presheaf tensor product.  Its source is the restriction to
the ambient scheme of `...SmallSite.tensorDifferentialFormsPresheaf`, by
`...SmallSite.restrictOpen_tensorDifferentialFormsPresheaf`. -/
def tensorRestrictionSheafULiftUnit (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ tensorDifferentialFormsPresheaf F i ⟶
      tensorRestrictionSheafULift A F i :=
  Functor.whiskerRight (toSheafify
    (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    (tensorRestriction A F i).presheaf) AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `tensorRestrictionSheafULiftUnit` is Zariski-locally injective, the unit being so and universe
lifting of the sections preserving local injectivity.  The local injectivity of the unit is taken
from `CategoryTheory.GrothendieckTopology.W_toSheafify` rather than from Mathlib's global
instances, for the reason recorded in the implementation notes of
`SmallSite/TensorRestrictionVanishing.lean`. -/
theorem isLocallyInjective_tensorRestrictionSheafULiftUnit (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorRestrictionSheafULiftUnit A F i) :=
  have := GrothendieckTopology.W.isLocallyInjective
    ((Opens.grothendieckTopology A.obj.thickening.target.scheme).W_toSheafify
      (tensorRestriction A F i).presheaf)
  Presheaf.isLocallyInjective_whiskerRight_uliftFunctor
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) _

/-- `tensorRestrictionSheafULiftUnit` is Zariski-locally surjective; see
`isLocallyInjective_tensorRestrictionSheafULiftUnit`. -/
theorem isLocallySurjective_tensorRestrictionSheafULiftUnit (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorRestrictionSheafULiftUnit A F i) :=
  have := GrothendieckTopology.W.isLocallySurjective
    ((Opens.grothendieckTopology A.obj.thickening.target.scheme).W_toSheafify
      (tensorRestriction A F i).presheaf)
  Presheaf.isLocallySurjective_whiskerRight_uliftFunctor
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) _

/-- **The restriction to the ambient scheme of an object of the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF] is the Zariski sheafification
`tensorRestrictionSheafULift` of the restricted presheaf tensor product.**

This is `...CrystallineThickening.restrictOpenSheafifyIso` of `SmallSite/SheafifySections.lean`
applied to the locally bijective morphism `tensorRestrictionSheafULiftUnit`; no hypothesis on `F`
is carried.  It is the identification which carries a statement about sections of the crystalline
sheafification to a statement about sections of a Zariski sheafification on the ambient scheme. -/
def restrictOpenTensorSheafIso (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙
        sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i) ≅
      tensorRestrictionSheafULift A F i :=
  haveI := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  haveI := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  haveI := isLocallyInjective_tensorRestrictionSheafULiftUnit A F i
  haveI := isLocallySurjective_tensorRestrictionSheafULiftUnit A F i
  CrystallineThickening.restrictOpenSheafifyIso A
    (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))
    (isSheaf_tensorRestrictionSheafULift A F i) (tensorDifferentialFormsSheaf F i).property
    (tensorRestrictionSheafULiftUnit A F i)

/-- `restrictOpenTensorSheafIso` is compatible with the two morphisms out of the restricted
presheaf tensor product: precomposing it with the restriction of the crystalline sheafification
unit gives the Zariski one.  This is the defining property of the identification. -/
theorem whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom
    (A : CrystallineThickening S) (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) ≫
        (restrictOpenTensorSheafIso A F i).hom =
      tensorRestrictionSheafULiftUnit A F i :=
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallyInjective_tensorRestrictionSheafULiftUnit A F i
  have := isLocallySurjective_tensorRestrictionSheafULiftUnit A F i
  CrystallineThickening.whiskerLeft_comp_restrictOpenSheafifyIso_hom A
    (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))
    (isSheaf_tensorRestrictionSheafULift A F i) (tensorDifferentialFormsSheaf F i).property
    (tensorRestrictionSheafULiftUnit A F i)

section Transition

variable (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-- **The `f`-map of `tensorRestrictionSheafULift`**: the universe lift of the morphism of abelian
presheaves underlying `...SmallSite.tensorRestrictionFMapSheaf`.  This is the map whose
surjectivity on global sections step 1 proves, read at the coefficient universe `u + 1`. -/
def tensorRestrictionFMapULift :
    tensorRestrictionSheafULift B F i ⟶
      (Opens.map g.hom.targetHom.hom.base).op ⋙ tensorRestrictionSheafULift A F i :=
  Functor.whiskerRight
    ((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf B.obj).obj).map
      (tensorRestrictionFMapSheaf F i g).val) AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- **The presheaf `f`-map of the restricted tensor product splits, on abelian presheaves, as the
`f`-map of the presheaf of modules followed by the direct image of the Zariski sheafification
unit.**  This is the definition of `...SmallSite.tensorRestrictionFMapPresheaf` read through the
forgetful functor to abelian presheaves, the direct image of the unit being the pushforward of
presheaves of modules along the `f`-map of the structure presheaf, which does not change the
underlying morphism of abelian presheaves. -/
theorem toPresheaf_tensorRestrictionFMapPresheaf :
    (PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
        (tensorRestrictionFMapPresheaf F i g) =
      (PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
          (CohomologyRestriction.moduleFMap (tensorDifferentialForms
            (F.val : PresheafOfModules.{u}
              (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g) ≫
        Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
          (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            (tensorRestriction A F i).presheaf) :=
  (PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map_comp
    (CohomologyRestriction.moduleFMap (tensorDifferentialForms
      (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g)
    ((PresheafOfModules.pushforward (smallRingRestrictionSheafFMap g).hom).map
      (PresheafOfModules.moduleSheafificationUnit
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (𝟙 (restrictedCommRingSheaf A).obj) (tensorRestriction A F i)))

/-- **The square of the Zariski sheafification units against the two `f`-maps commutes**, on
abelian presheaves at the module universe: the `f`-map of the restricted presheaf tensor product
followed by the direct image of the unit over the source is the unit over the target followed by
the `f`-map of the associated sheaves.  This is
`...SmallSite.toSheafify_comp_tensorRestrictionFMapSheaf` with
`toPresheaf_tensorRestrictionFMapPresheaf` substituted on its right-hand side. -/
theorem toSheafify_comp_toPresheaf_tensorRestrictionFMapSheaf :
    (PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
          (CohomologyRestriction.moduleFMap (tensorDifferentialForms
            (F.val : PresheafOfModules.{u}
              (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g) ≫
        Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
          (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            (tensorRestriction A F i).presheaf) =
      toSheafify (Opens.grothendieckTopology B.obj.thickening.target.scheme)
          (tensorRestriction B F i).presheaf ≫
        (PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf B.obj).obj).map
          (tensorRestrictionFMapSheaf F i g).val := by
  rw [toSheafify_comp_tensorRestrictionFMapSheaf, toPresheaf_tensorRestrictionFMapPresheaf]

/-- **The same square at the coefficient universe `u + 1`.**  The `f`-map of
`...SmallSite.tensorDifferentialFormsPresheaf` is the universe lift of the `f`-map of the tensor
presheaf of modules definitionally, and universe lifting of abelian groups preserves composition
definitionally, so this is one `congrArg` over
`toSheafify_comp_toPresheaf_tensorRestrictionFMapSheaf`. -/
theorem restrictionFMap_comp_whiskerLeft_tensorRestrictionSheafULiftUnit :
    CohomologyRestriction.restrictionFMap (tensorDifferentialFormsPresheaf F i) g ≫
        Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
          (tensorRestrictionSheafULiftUnit A F i) =
      tensorRestrictionSheafULiftUnit B F i ≫ tensorRestrictionFMapULift F i g :=
  congrArg (fun α : (tensorRestriction B F i).presheaf ⟶
      (Opens.map g.hom.targetHom.hom.base).op ⋙ (tensorRestrictionSheaf A F i).val.presheaf ↦
    Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{u + 1, u})
      (toSheafify_comp_toPresheaf_tensorRestrictionFMapSheaf F i g)

/-- **Step 2: the `f`-map of the crystalline sheafification is the `f`-map of the Zariski
sheafification on the ambient scheme**, under the identification `restrictOpenTensorSheafIso` at
the two objects.

Both composites agree after precomposition with the restriction of the crystalline sheafification
unit — the one by the naturality of `CategoryTheory.toSheafify` against the `f`-map together with
`restrictionFMap_comp_whiskerLeft_tensorRestrictionSheafULiftUnit`, the other by the defining
property `whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom` — and that precomposition is
injective on morphisms into a Zariski sheaf, by
`...CrystallineThickening.restrictOpenSheafify_hom_ext`.  No hypothesis on `F` or on `g` is
carried. -/
theorem restrictionFMap_comp_whiskerLeft_restrictOpenTensorSheafIso :
    CohomologyRestriction.restrictionFMap
          (sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) g ≫
        Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
          (restrictOpenTensorSheafIso A F i).hom =
      (restrictOpenTensorSheafIso B F i).hom ≫ tensorRestrictionFMapULift F i g := by
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have hZ : Presheaf.IsSheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      ((Opens.map g.hom.targetHom.hom.base).op ⋙ tensorRestrictionSheafULift A F i) :=
    (((Opens.map g.hom.targetHom.hom.base).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)).obj
        ⟨tensorRestrictionSheafULift A F i, isSheaf_tensorRestrictionSheafULift A F i⟩).property
  refine CrystallineThickening.restrictOpenSheafify_hom_ext B
    (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) hZ ?_
  have fac : Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor B).op
          (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) ≫
        CohomologyRestriction.restrictionFMap
          (sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) g =
      CohomologyRestriction.restrictionFMap (tensorDifferentialFormsPresheaf F i) g ≫
        Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
          (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
            (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))) :=
    NatTrans.ext (funext fun _ ↦
      ((toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).naturality _).symm)
  rw [← Category.assoc, ← Category.assoc, fac,
    whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom, Category.assoc,
    ← Functor.whiskerLeft_comp, whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom]
  exact restrictionFMap_comp_whiskerLeft_tensorRestrictionSheafULiftUnit F i g

/-- **The hypothesis `happ` of
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app`,
discharged**: the `f`-map of the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of
[Stacks, Tag 07LF] is surjective on global sections of the ambient scheme of the target, for a
morphism between objects over the whole of `X` whose map on ambient schemes is a closed immersion.

Step 1 gives the surjectivity for the Zariski `f`-map on the ambient scheme, step 2 identifies the
two `f`-maps over `⊤` up to the isomorphisms `restrictOpenTensorSheafIso` at the two objects, and a
surjection factoring through an injection forces the remaining factor to be onto.

The hypotheses carried are hypotheses (1) and (2) of [Stacks, Tag 07JN] and the affineness of `X`,
which is what step 1 needs. -/
theorem surjective_restrictionFMap_app_top_tensorDifferentialFormsSheaf [IsAffine S.X]
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Function.Surjective (ConcreteCategory.hom
      ((CohomologyRestriction.restrictionFMap
          (sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) g).app
        (op (⊤ : B.obj.thickening.target.scheme.Opens)))) := by
  have key := NatTrans.congr_app
    (restrictionFMap_comp_whiskerLeft_restrictOpenTensorSheafIso F i g)
    (op (⊤ : B.obj.thickening.target.scheme.Opens))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at key
  have hbij : ∀ (C : CrystallineThickening S) U,
      Function.Bijective (ConcreteCategory.hom ((restrictOpenTensorSheafIso C F i).hom.app U)) :=
    fun _ _ ↦ ConcreteCategory.bijective_of_isIso _
  have hphi : Function.Surjective (ConcreteCategory.hom
      ((tensorRestrictionFMapULift F i g).app
        (op (⊤ : B.obj.thickening.target.scheme.Opens)))) := by
    intro y
    obtain ⟨x, hx⟩ := surjective_app_top_tensorRestrictionFMapSheaf F i g hF hM hg hA hB y.down
    exact ⟨ULift.up x, ULift.ext _ _ hx⟩
  refine Function.Surjective.of_comp_left (f := ConcreteCategory.hom
    ((restrictOpenTensorSheafIso A F i).hom.app _)) ?_ (hbij A _).1
  rw [← ConcreteCategory.coe_comp, key, ConcreteCategory.coe_comp]
  exact hphi.comp (hbij B _).2

end Transition

/-- **Blocker (2) of [Stacks, Tag 07LF]: the abelian form of hypothesis (2) of
[Stacks, Tag 07JN] for the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.**

For a sheaf of `𝒪_{X/S}`-modules `F` on the small crystalline site of an affine `X` satisfying
hypotheses (1) and (2) of [Stacks, Tag 07JN], and for every `i`, the transition map

`Γ((X, T', δ'), F ⊗ Ω^i) ⟶ Γ((X, T, δ), F ⊗ Ω^i)`

is surjective along every morphism of `Cris(X/S)` between objects over the whole of `X` whose map
on ambient schemes is a closed immersion.

This is
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app`
with its hypothesis `happ` discharged by
`surjective_restrictionFMap_app_top_tensorDifferentialFormsSheaf`.  The hypotheses carried are
exactly hypotheses (1) and (2) of [Stacks, Tag 07JN] on `F` and the affineness of `X`, which is a
standing hypothesis of that proposition and of [Stacks, Tag 07LF]; nothing stands in for a missing
result.  **No tag attribute is placed**: this is a step inside the proof of [Stacks, Tag 07LF],
not a clause of a tag. -/
theorem hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf [IsAffine S.X]
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i) :=
  hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app F i hM
    fun _ _ g hg hA hB _ ↦
      surjective_restrictionFMap_app_top_tensorDifferentialFormsSheaf F i g hF hM hg hA hB

/-- **[Stacks, Tag 07LF] from one input.**  The conclusion

`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`  for `i > 0` and `j ≥ 0`

of [Stacks, Tag 07LF], in the form `...SmallSite.Vanishing07LF` states it, follows from the
acyclicity of the complex `M(0) → M(1) → M(2) → ⋯` built from the tensor sheaf, and from nothing
else.

Of the three inputs of `...SmallSite.vanishing07LF_of_isZero_homology_sectionsComplex`, the first
is `...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf` of
`SmallSite/TensorRestrictionVanishing.lean` and the second is
`hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf` above, each from hypotheses (1)
and (2) of [Stacks, Tag 07JN] alone.  The third is item 6 of the gap list of
`SmallSite/AffineCohomology.lean`, and it is open: the library has no term of type
`Crystalline.CosimplicialEnvelope`.

The affineness instances `[IsAffine S.X]` and `[IsAffine S.S.scheme]` are carried exactly as
`...SmallSite.vanishing07LF_of_isZero_homology_sectionsComplex` carries them — the system of
thickenings `...SmallSite.wholeSpaceSystem` that `M(•)` is built from needs them — and the
conclusion `...SmallSite.Vanishing07LF` quantifies over them anyway, so nothing is lost.

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved**; the point of this statement is
that exactly one input is left. -/
theorem vanishing07LF_of_isZero_homology_sectionsComplex'
    [IsAffine S.X] [IsAffine S.S.scheme]
    (hacyc : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i → ∀ j : ℕ,
        IsZero ((sectionsComplex
          (wholeSpaceSystem S (isNilpotent_prime_sections_of_isAffine S))
          (tensorDifferentialFormsSheaf F i).obj).homology j)) :
    Vanishing07LF S :=
  vanishing07LF_of_isZero_homology_sectionsComplex
    (fun _ hF _ i _ ↦ vanishing07JJ_tensorDifferentialFormsSheaf hF i)
    (fun F hF hM i _ ↦
      hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf F i hF hM)
    hacyc

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
