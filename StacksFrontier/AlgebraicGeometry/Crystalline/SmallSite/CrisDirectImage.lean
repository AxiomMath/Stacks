module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# The higher direct image `R^i f_{cris, *}` along a morphism of small crystalline topoi

Work in the situation of [Stacks, Tag 07MJ]: a morphism `(S, I, γ) ⟶ (S', I', γ')` of divided
power schemes over `ℤ_(p)` and a morphism `f : X ⟶ X'` of schemes over the closed fibres
`S₀ ⟶ S'₀`, with `p` locally nilpotent on `X` and `X'`.  The morphism of small crystalline topoi
`f_cris : (X/S)_cris ⟶ (X'/S')_cris` is
`Crystalline.GlobalCrystallineSituation.crisMorphism`, and it is valued in sheaves of **sets**.
This file carries it on sheaves of abelian groups and derives it: it builds
`f_{cris, *} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S'))`, the graded higher direct images
`R^i f_{cris, *}`, and `Rf_{cris, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(Cris(X'/S')))`.

## How the abelian direct image is built

Nothing here is new mathematics.  `f_cris` is by definition the composite
`π_{X'} ∘ f_CRIS ∘ i_X` of [Stacks, Tag 07IK], so its direct image is the composite of the three
direct images, which is exactly what
`Crystalline.GlobalCrystallineSituation.crisMorphism_pushforward` says on sheaves of sets.  The
same three functors are available at the coefficients `AddCommGrpCat.{u + 1}` instead of
`Type (u + 1)`, and the composite of those is `crisDirectImage`:

* `i_{X, *}` is `CategoryTheory.Functor.sheafPushforwardCocontinuous` along the cocontinuous
  inclusion `Cris(X/S) ⥤ CRIS(X/S)`, i.e. the right Kan extension of [Stacks, Tag 00XK];
* `f_{CRIS, *}` is the same construction along the cocontinuous change of divided power base
  `CRIS(X/S) ⥤ CRIS(X'/S')` of [Stacks, Tag 07IC];
* `π_{X', *}` is `i_{X'}^{-1}`, plain restriction along the inclusion
  `Cris(X'/S') ⥤ CRIS(X'/S')`, which is the formula `π_* = i^{-1}` of [Stacks, Tag 07IJ].

Each of the three is a right adjoint — the first by Mathlib's
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`, the second by
`CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous` ([Stacks, Tag 00XL]), the third by
`CategoryTheory.Functor.sheafAdjunctionLowerShriek` ([Stacks, Tag 00XR] (2)) — hence preserves
limits and is additive, so the composite is additive and its right derived functors exist on the
strength of the `EnoughInjectives` instance of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Cohomology.lean`.  Everything below is
unconditional: no declaration carries a hypothesis beyond the situation of [Stacks, Tag 07MJ]
itself and the choice of derived category models.

## What blocks the direct image of *modules*

[Stacks, Tag 07MP] and [Stacks, Tag 07MQ] speak of `R^i f_{cris, *}F` for `F` a crystal in
quasi-coherent `𝒪_{X/S}`-modules, and the source reads those sheaves as
`𝒪_{X'/S'}`-modules — [Stacks, Tag 07MP] has to, since "locally quasi-coherent" is a condition on
the restrictions of a *module* to the ambient schemes of the objects of `Cris(X'/S')`.  That
module-valued direct image is **not** constructed here, and the obstruction is identified
exactly; it is not the obstruction that blocks the module-valued direct image along `u_{X/S}`.

It *is* constructed downstream, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisModuleDirectImage.lean`, which
discharges the requirement isolated below one ring universe up and builds
`Crystalline.GlobalCrystallineSituation.SmallSite.crisModuleDirectImage` and
`...higherCrisModuleDirectImage` as functors between the chapter's own module categories.  The
two remarks are stated there, about those functors.  Nothing in the analysis that follows is
withdrawn: it is the analysis at `RingCat.{u}`, and it is what the downstream file's universe
raise is a response to.

*The set-valuedness of `crisMorphism` is not an obstruction.*  It is repaired by repeating the
construction at the coefficients `AddCommGrpCat.{u + 1}`, which is what `crisDirectImage` is,
exactly as `Crystalline.GlobalCrystallineSituation.SmallSite.zariskiDirectImage` repairs it for
`u_{X/S}`.

*There is no missing structure map either, and this is where `f_cris` differs from `u_{X/S}`.*
The module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiRingedComparison.lean` shows that for
`u_{X/S}` the canonical ring comparison runs the wrong way, `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X`, and that
a map the other way would split every divided power thickening in the site, which
`...SmallSite.isEmpty_ringHom_zmod_sq` refutes.  For `f_cris` the corresponding comparison is an
*identity*: both functors of sites preserve the ambient scheme of an object, so restricting the
structure sheaf along either of them gives the structure sheaf back on the nose.  That is
`changeBase_op_comp_crisRing` and `ι_op_comp_crisRing` below, both `rfl`, which together say that
the inverse image `f_cris^{-1}𝒪_{X'/S'}` *is* `𝒪_{X/S}`.  So `Stacks.SheafOfModules`
`.pushforwardCocontinuous`, which builds `f_* : Mod(𝒪_C) ⥤ Mod(𝒪_D)` from a cocontinuous functor
of sites and a map `f^♯ : 𝒪_D ⟶ {}_sw 𝒪_C`, has its `f^♯` available for both of the cocontinuous
factors, as the adjoint of an identity.

*What blocks it is the ring universe, and only that.*  The map `f^♯` lands in `{}_sw 𝒪_C`, the
right Kan extension of the structure sheaf of rings along the functor of sites, and that sheaf of
rings cannot be formed at the universes of this chapter.  For the inclusion
`ι : Cris(X/S) ⥤ CRIS(X/S)` the extension `(ι S).op.ran` applied to
`Crystalline.GlobalCrystallineSituation.SmallSite.crisRing` is computed by limits indexed by
`StructuredArrow (op A) (CrystallineThickening.ι S).op`, whose objects lie in `Type (u + 1)` and
whose morphisms in `Type u`, so
`(CrystallineThickening.ι S).op.HasPointwiseRightKanExtension (crisRing S)` needs
`CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} RingCat.{u}`, i.e. `max u (u + 1) ≤ u`, which
is false; and the same for `(changeBase S S' fS fX hf).op` and
`Crystalline.GlobalCrystallineSituation.crisRing`.  This is the *second* obstruction of
`ZariskiRingedComparison.lean`, the one that is independent of the direction of the comparison,
and for `f_cris` it is the only one.  The abelian side escapes it because its coefficients are
already `AddCommGrpCat.{u + 1}`, where `HasLimitsOfSize.{u, u + 1}` holds; that is why
`crisDirectImage` exists and a module-valued companion does not exist *at `RingCat.{u}`*.
Raising the ring coefficients to `RingCat.{u + 1}` repairs it, at the cost of replacing `𝒪_{X/S}`
by a universe lift of itself — and that cost is nil, because restriction of scalars along
`ULift.ringEquiv` is an isomorphism of categories that changes neither the sections nor the
morphisms (`Stacks.Modules.sheafRingULiftEquiv`).  `CrisModuleDirectImage.lean` takes that route
and comes back to the chapter's own `𝒪_{X/S}` at both ends.

The third factor, restriction along `Cris(X'/S') ⥤ CRIS(X'/S')`, is *not* affected: a module-valued
restriction along a continuous functor needs no Kan extension, and
`Crystalline.pAdicLevelSmallModuleRestriction` is an instance of exactly that pattern in this
repository.  So the module-valued factorization of `f_{cris, *}` fails at its first two steps and
not at its last, and it is those two that `CrisModuleDirectImage.lean` repairs.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bigDirectImage` — `i_{X, *} : Ab(Cris(X/S)) ⥤ Ab(CRIS(X/S))`.
* `smallRestriction` — `π_{X, *} = i_X^{-1} : Ab(CRIS(X/S)) ⥤ Ab(Cris(X/S))`.
* `changeBaseDirectImage` — `f_{CRIS, *} : Ab(CRIS(X/S)) ⥤ Ab(CRIS(X'/S'))`.
* `crisDirectImage` — **`f_{cris, *} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S'))`**, the composite of the
  three.
* `higherCrisDirectImage` — **`R^i f_{cris, *} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S'))`**, the
  `ℕ`-indexed right derived functor.
* `derivedCrisDirectImageFunctor` and `derivedCrisDirectImage` —
  **`Rf_{cris, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(Cris(X'/S')))`** and its form on a single sheaf.
* `higherCrisDirectImagePlus` — the `ℤ`-indexed higher direct image, the cohomology sheaves of
  `Rf_{cris, *}`.
* `HasCrisRingDirectImage` — **the checkable form of what a module-valued `f_{cris, *}` requires**:
  that the structure sheaf of rings admit a right Kan extension along each of the two cocontinuous
  functors of sites.  Stated and left open; see the discussion above and the docstring.
* `bigRingStructureMap` and `changeBaseRingStructureMap` — the maps `f^♯` that requirement yields,
  so that nothing beyond it is missing.

## Main results

* `changeBase_op_comp_crisRing` and `ι_op_comp_crisRing` — **`f_cris^{-1}𝒪_{X'/S'} = 𝒪_{X/S}`**,
  in the two stages in which `f_cris` is built, both by `rfl`.  See the discussion above.
* `crisDirectImage_obj_obj_obj` and `crisDirectImageObjObjIsoLimit` — the sections of
  `f_{cris, *}F` over an object `(U', T', δ')` of `Cris(X'/S')` are a limit of the sections of
  `i_{X, *}F` over the objects of `CRIS(X/S)` mapping to it.
* `isZero_higherCrisDirectImage_of_injective` — `R^i f_{cris, *} I = 0` for `i > 0` and `I`
  injective.
* `higherCrisDirectImageZeroIso` — `R^0 f_{cris, *} ≅ f_{cris, *}`.
* `homologyDerivedCrisDirectImageIso` — the derived and the graded higher direct images agree,
  `H^i(Rf_{cris, *} -) ≅ R^i f_{cris, *}`.

## What is and is not proved

What is proved is that `f_{cris, *}` exists on abelian sheaves, preserves limits and is additive;
that the graded `R^i f_{cris, *}` and the derived `Rf_{cris, *}` therefore exist, agree degreewise,
agree with `f_{cris, *}` in degree zero and kill injectives in positive degree; that the sections
of `f_{cris, *}F` are given by the limit formula of [Stacks, Tag 00XK]; and that the inverse image
of the structure sheaf along each stage of `f_cris` is the structure sheaf on the nose.

What is **not** proved:

* **The module-valued `R^i f_{cris, *}` is not constructed *here***, for the universe reason set
  out above; see "What blocks the direct image of modules".  It is constructed in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisModuleDirectImage.lean`, which also
  states [Stacks, Tag 07MP] and [Stacks, Tag 07MQ] about it; neither tag is stated here and no
  declaration in this file carries either attribute.
* **The displayed formula (07MK) is not proved here**: it is proved downstream, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKProof.lean`,
  which computes `Rf_{cris, *}F` on an object of `Cris(X'/S')` as `R(T ⟶ T')_*(Rτ_{U/T, *}F_U)`.  The data of that recipe — the
  situation `U/T`, the morphism `(U/T)_cris ⟶ (X/S)_cris`, the structure morphism `τ_{U/T}` and the
  pullback `F_U` — are in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/HigherDirectImage.lean`.  The limit formula `crisDirectImageObjObjIsoLimit` is the
  underived statement that is available, and it is not (07MK).  What that limit *is* in the terms
  of (07MK) is identified in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKBaseCase.lean`: the sections of
  `f_{cris, *}F` over an object `(U', T', δ')` are `Γ(Cris(U/T), F_U)`, hence the sections of
  `(T ⟶ T')_*(τ_{U/T, *}F_U)` over the whole of `T'`.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MP](https://stacks.math.columbia.edu/tag/07MP)
* [Stacks Project, Tag 07MQ](https://stacks.math.columbia.edu/tag/07MQ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-! ### Abelian sheaves on the big crystalline site -/

/-- Abelian sheaves on the big crystalline site admit sheafification at the coefficient universe
`u + 1` of the small crystalline side.  The objects of `CRIS(X/S)` form a `Type (u + 1)` and its
morphisms a `Type u`, exactly as for `Cris(X/S)`, so this is
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` at the same universes as
`Crystalline.GlobalCrystallineSituation.SmallSite.instHasSheafifyAddCommGrpCat`. -/
instance instHasSheafifyBigAddCommGrpCat : HasSheafify (topology S) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- The limits that compute the right Kan extension along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` exist at any coefficients with limits of the relevant size: they are
indexed by `StructuredArrow (op A) (CrystallineThickening.ι S).op`, whose objects lie in
`Type (u + 1)` and whose morphisms in `Type u`.  The two coefficient categories this is used at
are `AddCommGrpCat.{u + 1}`, where the Kan extension is `i_{X, *}` below, and `Type (u + 1)`,
where it is the direct image of the morphism of topoi
`...CrystallineThickening.smallToBigMorphism` of [Stacks, Tag 07IJ].

This is the instance that fails for `RingCat.{u}`, which is what keeps the module-valued direct
image out of reach; see the module documentation. -/
instance instHasPointwiseRightKanExtensionι (E : Type (u + 2)) [Category.{u + 1} E]
    [HasLimitsOfSize.{u, u + 1} E] (F : (CrystallineThickening S)ᵒᵖ ⥤ E) :
    (CrystallineThickening.ι S).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-- The colimits that compute the left Kan extension along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` exist at the coefficients `AddCommGrpCat.{u + 1}`.  They are what makes
restriction along the inclusion a right adjoint, by [Stacks, Tag 00XR] (2). -/
instance instHasPointwiseLeftKanExtensionι
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (CrystallineThickening.ι S).op.HasPointwiseLeftKanExtension F :=
  fun _ ↦ inferInstance

include hf in
/-- The limits that compute the right Kan extension along change of divided power base
`CRIS(X/S) ⥤ CRIS(X'/S')` exist at any coefficients with limits of the relevant size, the index
categories being of the same size as for the inclusion. -/
instance instHasPointwiseRightKanExtensionChangeBase (E : Type (u + 2)) [Category.{u + 1} E]
    [HasLimitsOfSize.{u, u + 1} E] (F : (Thickening S)ᵒᵖ ⥤ E) :
    (changeBase S S' fS fX hf).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-! ### `f_cris^{-1}𝒪_{X'/S'} = 𝒪_{X/S}` -/

/-- **Restricting the structure sheaf of `CRIS(X'/S')` along change of divided power base gives
the structure sheaf of `CRIS(X/S)` on the nose.**  Change of base replaces the maps `T ⟶ S` and
`U ⟶ X` of an object by their composites with `S ⟶ S'` and `X ⟶ X'` and leaves the divided power
thickening `U ↪ T` alone, and the structure sheaf of the big crystalline site depends only on
that thickening, both sides being `(U, T, δ) ↦ Γ(T, 𝒪_T)`.

This is one half of the statement that the inverse image `f_cris^{-1}𝒪_{X'/S'}` is `𝒪_{X/S}`: the
ring comparison a module-valued `f_{cris, *}` would need is an identity, unlike the one for
`u_{X/S}`.  See the module documentation. -/
theorem changeBase_op_comp_crisRing :
    (changeBase S S' fS fX hf).op ⋙ GlobalCrystallineSituation.crisRing S' =
      GlobalCrystallineSituation.crisRing S :=
  rfl

/-- **Restricting the structure sheaf of `CRIS(X/S)` along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` gives the structure sheaf of `Cris(X/S)` on the nose.**  This is the
definition of `Crystalline.GlobalCrystallineSituation.SmallSite.crisRing`, and it is the other
half of `f_cris^{-1}𝒪_{X'/S'} = 𝒪_{X/S}`. -/
theorem ι_op_comp_crisRing :
    (CrystallineThickening.ι S).op ⋙ GlobalCrystallineSituation.crisRing S = crisRing S :=
  rfl

/-- **The requirement a module-valued `f_{cris, *}` comes down to**: that the structure sheaf of
rings admit a right Kan extension along each of the two cocontinuous functors of sites out of
which `f_cris` is built, so that the presheaves of rings `i_{X, *}𝒪_{X/S}` and
`f_{CRIS, *}𝒪_{X/S}` can be formed at all.

This is the checkable form of the obstruction described in the module documentation.  It is
*stated and left open*, not proved and not expected to hold: both Kan extensions are computed by
limits in `RingCat.{u}` indexed by categories whose objects lie in `Type (u + 1)`, so each
conjunct implies an instance of
`CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} RingCat.{u}`, i.e. `max u (u + 1) ≤ u`.  The
same requirement for the abelian coefficients `AddCommGrpCat.{u + 1}` does hold, and is
`instHasPointwiseRightKanExtensionι` together with
`instHasPointwiseRightKanExtensionChangeBase`.

It is a genuine *sufficient* condition for the ring comparison, not merely a necessary one:
`bigRingStructureMap` and `changeBaseRingStructureMap` construct the maps `f^♯` that
`Stacks.SheafOfModules.pushforwardCocontinuous` consumes from the two conjuncts, with no further
input, because the inverse image of the structure sheaf along each functor of sites is the
structure sheaf on the nose.  So nothing *else* is missing. -/
def HasCrisRingDirectImage : Prop :=
  Functor.HasRightKanExtension (CrystallineThickening.ι S).op (crisRing S) ∧
    Functor.HasRightKanExtension (changeBase S S' fS fX hf).op
      (GlobalCrystallineSituation.crisRing S)

/-- **The structure map `𝒪_{X/S} ⟶ i_{X, *}𝒪_{X/S}` of presheaves of rings, granted the first
half of `HasCrisRingDirectImage`.**  It is the universal map into the right Kan extension attached
to the identity of `𝒪_{X/S}`, which is a legitimate datum precisely because restricting the big
structure sheaf along the inclusion gives the small one on the nose, `ι_op_comp_crisRing`.

This is the `f^♯` that `Stacks.SheafOfModules.pushforwardCocontinuous` needs for the first factor
of `f_{cris, *}`; compare `Crystalline.GlobalCrystallineSituation.SmallSite.ZariskiStructureMap`,
which for `u_{X/S}` is the datum that does *not* exist. -/
def bigRingStructureMap
    [Functor.HasRightKanExtension (CrystallineThickening.ι S).op (crisRing S)] :
    GlobalCrystallineSituation.crisRing S ⟶
      (CrystallineThickening.ι S).op.rightKanExtension (crisRing S) :=
  Functor.liftOfIsRightKanExtension _
    (Functor.rightKanExtensionCounit (CrystallineThickening.ι S).op (crisRing S))
    (GlobalCrystallineSituation.crisRing S) (𝟙 _)

include hf in
/-- **The structure map `𝒪_{X'/S'} ⟶ f_{CRIS, *}𝒪_{X/S}` of presheaves of rings, granted the
second half of `HasCrisRingDirectImage`.**  As for `bigRingStructureMap`, it is the universal map
into the right Kan extension attached to the identity, available because restricting the structure
sheaf of `CRIS(X'/S')` along change of divided power base gives that of `CRIS(X/S)` on the nose,
`changeBase_op_comp_crisRing`. -/
def changeBaseRingStructureMap
    [Functor.HasRightKanExtension (changeBase S S' fS fX hf).op
      (GlobalCrystallineSituation.crisRing S)] :
    GlobalCrystallineSituation.crisRing S' ⟶
      (changeBase S S' fS fX hf).op.rightKanExtension (GlobalCrystallineSituation.crisRing S) :=
  Functor.liftOfIsRightKanExtension _
    (Functor.rightKanExtensionCounit (changeBase S S' fS fX hf).op
      (GlobalCrystallineSituation.crisRing S))
    (GlobalCrystallineSituation.crisRing S') (𝟙 _)

/-! ### The three factors of `f_{cris, *}` on abelian sheaves -/

/-- **The abelian direct image `i_{X, *} : Ab(Cris(X/S)) ⥤ Ab(CRIS(X/S))`** along the inclusion of
the small crystalline site, [Stacks, Tag 07IJ].  It is the right Kan extension of
[Stacks, Tag 00XK] at the coefficients `AddCommGrpCat.{u + 1}`; the same construction at
`Type (u + 1)` is the direct image of
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.smallToBigMorphism`. -/
def bigDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1} :=
  (CrystallineThickening.ι S).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (topology S)

/-- **The restriction `π_{X, *} = i_X^{-1} : Ab(CRIS(X/S)) ⥤ Ab(Cris(X/S))`** of an abelian sheaf
on the big crystalline site to the small one.  This is the formula `π_* = i^{-1}` of
[Stacks, Tag 07IJ], carried on abelian sheaves; no sheafification is involved, the inclusion being
continuous. -/
def smallRestriction :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤ Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (CrystallineThickening.ι S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (topology S)

/-- **Restriction is left adjoint to the abelian direct image along the inclusion.**  The
inclusion `Cris(X/S) ⥤ CRIS(X/S)` is both continuous and cocontinuous, so this is Mathlib's
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`. -/
def bigDirectImageAdjunction : smallRestriction S ⊣ bigDirectImage S :=
  (CrystallineThickening.ι S).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (topology S)

/-- `i_{X, *}` commutes with every limit that exists, being a right adjoint. -/
instance preservesLimitsOfSize_bigDirectImage :
    PreservesLimitsOfSize.{w, w'} (bigDirectImage S) :=
  (bigDirectImageAdjunction S).rightAdjoint_preservesLimits

/-- `i_{X, *}` is additive, being a right adjoint and hence preserving binary products. -/
instance additive_bigDirectImage : (bigDirectImage S).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (bigDirectImage S) := inferInstance
  Functor.additive_of_preserves_binary_products _

/-- **The lower shriek `i_{X, !}` is left adjoint to restriction to the small crystalline site**,
[Stacks, Tag 00XR] (2), carried on abelian sheaves. -/
def smallRestrictionAdjunction :
    Functor.sheafPullbackConstruction.sheafPullback (CrystallineThickening.ι S)
        AddCommGrpCat.{u + 1} (smallTopology S) (topology S) ⊣ smallRestriction S :=
  (CrystallineThickening.ι S).sheafAdjunctionLowerShriek AddCommGrpCat.{u + 1}
    (smallTopology S) (topology S)

/-- Restriction to the small crystalline site commutes with every limit that exists, being a right
adjoint. -/
instance preservesLimitsOfSize_smallRestriction :
    PreservesLimitsOfSize.{w, w'} (smallRestriction S) :=
  (smallRestrictionAdjunction S).rightAdjoint_preservesLimits

/-- Restriction to the small crystalline site is additive. -/
instance additive_smallRestriction : (smallRestriction S).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (smallRestriction S) := inferInstance
  Functor.additive_of_preserves_binary_products _

section ChangeBase

include hf

/-- **The abelian direct image `f_{CRIS, *} : Ab(CRIS(X/S)) ⥤ Ab(CRIS(X'/S'))`** along change of
divided power base, [Stacks, Tag 07IC].  It is the right Kan extension of [Stacks, Tag 00XK] at the
coefficients `AddCommGrpCat.{u + 1}`, the functor of sites being cocontinuous by
`Crystalline.GlobalCrystallineSituation.changeBase_isCocontinuous`. -/
def changeBaseDirectImage :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤ Sheaf (topology S') AddCommGrpCat.{u + 1} :=
  (changeBase S S' fS fX hf).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (topology S) (topology S')

/-- **[Stacks, Tag 00XL] for `f_CRIS` on abelian sheaves.**  The sheaf pullback along the
cocontinuous change of divided power base is left adjoint to the abelian direct image. -/
def changeBaseDirectImageAdjunction :
    (changeBase S S' fS fX hf).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
        (topology S) (topology S') ⊣ changeBaseDirectImage S S' fS fX hf :=
  (changeBase S S' fS fX hf).sheafAdjunctionPullbackCocontinuous AddCommGrpCat.{u + 1}
    (topology S) (topology S')

/-- `f_{CRIS, *}` commutes with every limit that exists, being a right adjoint. -/
instance preservesLimitsOfSize_changeBaseDirectImage :
    PreservesLimitsOfSize.{w, w'} (changeBaseDirectImage S S' fS fX hf) :=
  (changeBaseDirectImageAdjunction S S' fS fX hf).rightAdjoint_preservesLimits

/-- `f_{CRIS, *}` is additive, being a right adjoint and hence preserving binary products. -/
instance additive_changeBaseDirectImage : (changeBaseDirectImage S S' fS fX hf).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (changeBaseDirectImage S S' fS fX hf) := inferInstance
  Functor.additive_of_preserves_binary_products _

end ChangeBase

/-! ### `f_{cris, *}` on abelian sheaves -/

section DirectImage

include hf

/-- **The direct image `f_{cris, *} : Sh(Cris(X/S)) ⥤ Sh(Cris(X'/S'))` at arbitrary
coefficients**, along the morphism of small crystalline topoi of [Stacks, Tag 07IK].

It is the composite `π_{X', *} ∘ f_{CRIS, *} ∘ i_{X, *}` of the direct images of the three factors
of `f_cris`, with coefficients in any category having the limits that compute the two right Kan
extensions involved.

This is one functor with the two readings this chapter uses.  At `AddCommGrpCat.{u + 1}` it is the
abelian direct image `crisDirectImage` below.  At `Type (u + 1)` it is the pushforward of the
morphism of topoi `Crystalline.GlobalCrystallineSituation.crisMorphism`, which is exactly what
`Crystalline.GlobalCrystallineSituation.crisMorphism_pushforward` says. -/
abbrev crisDirectImageCoeff (E : Type (u + 2)) [Category.{u + 1} E]
    [HasLimitsOfSize.{u, u + 1} E] :
    Sheaf (smallTopology S) E ⥤ Sheaf (smallTopology S') E :=
  (CrystallineThickening.ι S).sheafPushforwardCocontinuous E (smallTopology S) (topology S) ⋙
    (changeBase S S' fS fX hf).sheafPushforwardCocontinuous E (topology S) (topology S') ⋙
      (CrystallineThickening.ι S').sheafPushforwardContinuous E (smallTopology S') (topology S')

/-- **The abelian direct image `f_{cris, *} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S'))`**,
`crisDirectImageCoeff` at the coefficients `AddCommGrpCat.{u + 1}`.  The target is abelian sheaves
and not `𝒪_{X'/S'}`-modules; see the module documentation for exactly what blocks the
module-valued version. -/
def crisDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1} :=
  bigDirectImage S ⋙ changeBaseDirectImage S S' fS fX hf ⋙ smallRestriction S'

/-- The abelian direct image is `crisDirectImageCoeff` at `AddCommGrpCat.{u + 1}`. -/
theorem crisDirectImage_eq :
    crisDirectImage S S' fS fX hf =
      crisDirectImageCoeff S S' fS fX hf AddCommGrpCat.{u + 1} :=
  rfl

/-- `f_{cris, *}` commutes with every limit that exists, each of its three factors being a right
adjoint. -/
instance preservesLimitsOfSize_crisDirectImage :
    PreservesLimitsOfSize.{w, w'} (crisDirectImage S S' fS fX hf) :=
  inferInstanceAs (PreservesLimitsOfSize.{w, w'}
    (bigDirectImage S ⋙ changeBaseDirectImage S S' fS fX hf ⋙ smallRestriction S'))

/-- `f_{cris, *}` is additive, being a composite of additive functors. -/
instance additive_crisDirectImage : (crisDirectImage S S' fS fX hf).Additive :=
  inferInstanceAs ((bigDirectImage S ⋙ changeBaseDirectImage S S' fS fX hf ⋙
    smallRestriction S').Additive)

/-- **The presheaf underlying `f_{cris, *}F` is a right Kan extension read at the objects of the
big crystalline site.**  By definition the value of `f_{cris, *}F` at an object `(U', T', δ')` of
`Cris(X'/S')` is the value at the underlying object of `CRIS(X'/S')` of the right Kan extension of
the presheaf underlying `i_{X, *}F` along change of divided power base.  This holds
definitionally. -/
theorem crisDirectImage_obj_obj_obj (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (A' : CrystallineThickening S') :
    ((crisDirectImage S S' fS fX hf).obj F).obj.obj (op A') =
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj F).obj).obj (op A'.obj) :=
  rfl

/-- **The sections of `f_{cris, *}F` over an object `(U', T', δ')` of `Cris(X'/S')` are a limit
over the objects of `CRIS(X/S)` lying over it.**  The outer stage of `f_{cris, *}` is the right
Kan extension of [Stacks, Tag 00XK] along change of divided power base, so its value at
`(U', T', δ')` is the limit of `i_{X, *}F` over the category
`StructuredArrow (op (U', T', δ')) (changeBase S S' fS fX hf).op` of objects of `CRIS(X/S)`
together with a morphism to `(U', T', δ')` over `S ⟶ S'`.

This is the underived formula that is available.  It is *not* the displayed equation (07MK) of
[Stacks, Tag 07MJ], which computes the derived direct image and which the source states without
proof. -/
def crisDirectImageObjObjIsoLimit (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (A' : CrystallineThickening S') :
    ((crisDirectImage S S' fS fX hf).obj F).obj.obj (op A') ≅
      limit (StructuredArrow.proj (op A'.obj) (changeBase S S' fS fX hf).op ⋙
        ((bigDirectImage S).obj F).obj) :=
  (changeBase S S' fS fX hf).op.ranObjObjIsoLimit ((bigDirectImage S).obj F).obj (op A'.obj)

/-! ### `R^i f_{cris, *}` -/

/-- **The higher direct image `R^i f_{cris, *} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S'))`**, the `i`-th
right derived functor of the abelian direct image along `f_cris`.  It exists because
`f_{cris, *}` is additive and abelian sheaves on `Cris(X/S)` have enough injectives, by
`Crystalline.GlobalCrystallineSituation.SmallSite.instEnoughInjectives`.

These are the sheaves [Stacks, Tag 07MP] and [Stacks, Tag 07MQ] are about. -/
def higherCrisDirectImage (i : ℕ) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1} :=
  (crisDirectImage S S' fS fX hf).rightDerived i

/-- **`R^i f_{cris, *} I = 0` for `i > 0` and `I` an injective abelian sheaf.** -/
theorem isZero_higherCrisDirectImage_of_injective
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective F] (i : ℕ) :
    IsZero ((higherCrisDirectImage S S' fS fX hf (i + 1)).obj F) :=
  (crisDirectImage S S' fS fX hf).isZero_rightDerived_obj_injective_succ i F

/-- **`R^0 f_{cris, *} ≅ f_{cris, *}`.**  The abelian direct image is left exact, each of its
three factors being a right adjoint, so nothing is lost in degree zero. -/
def higherCrisDirectImageZeroIso :
    higherCrisDirectImage S S' fS fX hf 0 ≅ crisDirectImage S S' fS fX hf :=
  haveI : PreservesFiniteLimits (crisDirectImage S S' fS fX hf) := inferInstance
  (crisDirectImage S S' fS fX hf).rightDerivedZeroIsoSelf

/-! ### `Rf_{cris, *}` -/

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]

/-- **The derived direct image
`Rf_{cris, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(Cris(X'/S')))`**, as a functor between bounded below
derived categories.  The derived category models enter as instance arguments at free universes,
following the convention of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/DerivedGlobalSections.lean`;
`Crystalline.GlobalCrystallineSituation.SmallSite.hasDerivedCategorySheaf` supplies them. -/
def derivedCrisDirectImageFunctor :
    DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :=
  (crisDirectImage S S' fS fX hf).rightDerivedFunctorPlus

/-- **`Rf_{cris, *}F` for a single abelian sheaf `F`**: the sheaf placed in degree zero, then the
derived direct image.  This is the object the displayed equation (07MK) of [Stacks, Tag 07MJ] is
about. -/
def derivedCrisDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
    derivedCrisDirectImageFunctor S S' fS fX hf

/-- **The `ℤ`-indexed higher direct image**, the degree-`i` cohomology sheaf of
`Rf_{cris, *}`. -/
def higherCrisDirectImagePlus (i : ℤ) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1} :=
  (crisDirectImage S S' fS fX hf).rightDerivedPlus i

/-- Taking the degree-`i` cohomology of `Rf_{cris, *}` is the `ℤ`-indexed higher direct image, by
definition of the latter. -/
theorem derivedCrisDirectImage_comp_homologyFunctor (i : ℤ) :
    derivedCrisDirectImage S S' fS fX hf ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) i =
      higherCrisDirectImagePlus S S' fS fX hf i :=
  rfl

/-- **The derived and the graded higher direct images agree**:
`H^i(Rf_{cris, *}F) ≅ R^i f_{cris, *}F`, naturally in `F`.  The cohomology of `Rf_{cris, *}` is
the `ℤ`-indexed right derived functor of the abelian direct image, which agrees with Mathlib's
`ℕ`-indexed one by `Stacks.DerivedIndexing.rightDerivedIso`. -/
def homologyDerivedCrisDirectImageIso (i : ℕ) :
    derivedCrisDirectImage S S' fS fX hf ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℤ) ≅
      higherCrisDirectImage S S' fS fX hf i :=
  (Stacks.DerivedIndexing.rightDerivedIso (crisDirectImage S S' fS fX hf) i).symm

/-- **`Rf_{cris, *}I` is concentrated in degree zero for `I` injective.** -/
theorem isZero_homology_derivedCrisDirectImage_of_injective
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective F] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) i).obj
        ((derivedCrisDirectImage S S' fS fX hf).obj F)) :=
  Functor.isZero_rightDerivedPlus_obj_injective (crisDirectImage S S' fS fX hf) i hi F

end Derived

end DirectImage

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
