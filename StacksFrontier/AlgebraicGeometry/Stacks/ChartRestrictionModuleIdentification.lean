module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartLocalRestrictionIdentification

/-!
# The module-level chart-local identification of restrictions (Stacks 0GQC, Remark 0GQA)

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`U`, and let `W` be a scheme étale over `U`. This file proves the module half of the
identification `ℱ|_{W_étale} = (ℱ|_{U_étale})|_{W_étale}` of Remark 0GQA, the hypothesis `hiso`
of `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_chartLocalModuleIdentification`, and with it
**Stacks 0GQC with no hypothesis beyond the source's**:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestriction`.

The two modules being compared are sections of `ℱ` at two objects of `𝒳`: the restriction of
Stacks 06W1 (`AlgebraicGeometry.Stack.restrictToSmallEtale`, the site local quasi-coherence is
stated on) evaluates `ℱ` at
`(CategoryTheory.Over.post (p ⋙ CategoryTheory.Over.forget _)).inv.obj …`, a chosen quasi-inverse
of the localization equivalence of Stacks 06W0, whereas restriction along `u_U` (equation 075K,
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`) evaluates it at
`(AlgebraicGeometry.Space.restrictionFunctor …).obj …`, built from the chosen inverse of the
equivalence over the site of Stacks 073M. Those two objects are not definitionally equal, and the
comparison also has to be shown semilinear for the two structure-sheaf identifications
`AlgebraicGeometry.Stack.localStructurePresheafIso` and
`AlgebraicGeometry.Space.etaleChartStructureHom`, which are built along the two different routes.
That is the content of Remark 0GQA at the module level, and it is what is proved here.

## Main definitions

* `AlgebraicGeometry.Space.chartLocalIndexFunctor`: the functor `W_étale ⥤ 𝒳` along which
  equation 075K restricts `ℱ` and then localizes at an étale chart `W` of `U`.
* `AlgebraicGeometry.Space.localRestrictionIndexFunctor`: the functor `W_étale ⥤ 𝒳` along which
  Stacks 06W1 restricts `ℱ` at the object `u_U W` of `𝒳`.
* `AlgebraicGeometry.Space.chartRestrictionSliceIso` and
  `AlgebraicGeometry.Space.chartRestrictionIndexIso`: **the two index functors are canonically
  isomorphic**, in the slice of `𝒳` at `u_U W` and then in `𝒳`.
* `AlgebraicGeometry.Space.chartRestrictionCoefficient` and
  `AlgebraicGeometry.Space.localRestrictionCoefficient`: the two sides as single
  `CategoryTheory.SheafOfModules.pushforward`s of `ℱ`, with their coefficient homomorphisms.
* `AlgebraicGeometry.Space.ChartRestrictionSemilinear`: the compatibility of the isomorphism of
  index functors with those two coefficient homomorphisms.

## Main results

* `AlgebraicGeometry.Space.chartLocalSliceFunctor_comp_overPost`: **the two restrictions agree on
  the nose after localization**, an equality of functors into the big fppf slice at the scheme
  below `u_U W`.
* `AlgebraicGeometry.Space.isContinuous_localRestrictionIndexFunctor`: the Stacks 06W1 index
  functor is continuous for the étale topologies.
* `AlgebraicGeometry.Space.restrictionChartModule_eq_pushforward`: the restriction of Stacks 06WJ
  at `u_U W` *is* the pushforward of `ℱ` along the Stacks 06W1 index functor, with
  `AlgebraicGeometry.Stack.localStructurePresheafIso` as coefficient homomorphism.
* `AlgebraicGeometry.Space.chartRestrictionSemilinear`: **Remark 0GQA for the structure sheaves.**
* `AlgebraicGeometry.Space.chartRestriction_iso`: **Remark 0GQA at the module level**, the
  displayed equality `ℱ|_{W_étale} = (ℱ|_{U_étale})|_{W_étale}` of the proof of Stacks 0GQC.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestriction`: **Stacks 0GQC**,
  unconditionally.

## Implementation notes

The three nested `CategoryTheory.SheafOfModules.pushforward`s of the equation 075K side — along
`u_U`, along `CategoryTheory.Over.forget W` and along the chart-local equivalence — are merged
into one by `CategoryTheory.SheafOfModules.pushforwardComp`, which is the identity isomorphism;
merging them by `rfl` instead exceeds the elaborator's default heartbeat budget, so the
isomorphism is used explicitly.

`AlgebraicGeometry.Space.isoOfEqRingPushforward` is the transport of a module along an equality of
its sheaf of rings, phrased so that the equality is consumed as a `CategoryTheory.eqToHom`
coefficient rather than as a `▸` on the module: that keeps the comparison on the side of morphisms
of sheaves of rings, which is where the semilinearity lives.

The semilinearity is assembled at term level, by `Eq.trans` and `congrArg`, rather than by `rw`.
The two slices of the underlying category of schemes which it compares — the one at
`B.obj ‹B.Contains …›` and the one at `(p ⋙ CategoryTheory.Over.forget _).obj (u_U W)` — carry
`CategoryTheory.Category` instance terms which are definitionally but not syntactically equal, and
`rw` fails on keyed matching inside the arguments of `F.map` for that reason, so each such step is
applied as a term built from `CategoryTheory.Functor.map_comp`, `CategoryTheory.eqToHom_op` and
`CategoryTheory.eqToHom_map` rather than rewritten with.

Everything below is stated for the small étale site read as
`AlgebraicGeometry.Space.SmallEtale` rather than as `(AlgebraicGeometry.Space.smallEtaleRingedSite
‹_›).C`. Those two readings carry different `CategoryTheory.Category` instance terms on the same
category, and in the ringed reading instance search does not find `Category (Over W)`; the final
theorem is applied across that definitional equality in term mode, exactly as
`AlgebraicGeometry.Space.chartLocalSiteEquivalenceOver` does.

## References

* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ m

/-! ### General lemmas on transports and on equivalences -/

/-- The small étale site of a scheme, transported along an equality of schemes and then composed
with a localization functor, is the small étale inclusion of Stacks 06W1.

Both sides are indexed by a functor `n` to the underlying category of schemes; the hypothesis is
the same statement for a functor `t` equal to it. -/
theorem transportSmallEtale_post_eq (B : BigFppfSite.{u}) (E : BigEtaleSite.{u})
    (hE : E.cutoff = B.cutoff) {C : Type u₁} [Category.{v₁} C] (W : C)
    {t n : C ⥤ B.Schemes} (hn : n = t)
    (hT' : E.Contains (t.obj W).obj)
    (eqv : _root_.AlgebraicGeometry.SmallEtale E (t.obj W).obj hT' ≌ Over W)
    (core : eqv.functor ⋙ Over.post (X := W) t =
      Stack.smallEtaleInclusion B E hE (t.obj W).obj hT')
    (hT : E.Contains (n.obj W).obj) :
    (transportSmallEtale E
        (congrArg (fun k : C ⥤ B.Schemes => (k.obj W).obj) hn) hT hT' eqv).functor
        ⋙ Over.post (X := W) n =
      Stack.smallEtaleInclusion B E hE (n.obj W).obj hT := by
  subst hn
  exact core

/-- Transport of a sheaf of modules along an equality of its sheaf of rings.

The data asked for is an isomorphism onto the pushforward of `N` along the identity functor with
`CategoryTheory.eqToHom` of the equality as coefficient homomorphism, which is restriction of
scalars along that equality; the conclusion replaces it by the `▸` transport. -/
noncomputable def isoOfEqRingPushforward {A : Type u₁} [Category.{v₁} A]
    {D : Type u₂} [Category.{v₂} D]
    {JA : GrothendieckTopology A} {JD : GrothendieckTopology D}
    {R₁ R₂ : Sheaf JA RingCat.{u}} (hR : R₁ = R₂)
    {F : A ⥤ D} [F.IsContinuous JA JD] {R : Sheaf JD RingCat.{u}}
    (ψ : R₂ ⟶ (F.sheafPushforwardContinuous RingCat.{u} JA JD).obj R)
    (X : SheafOfModules.{m} R) (N : SheafOfModules.{m} R₂)
    (hN : (SheafOfModules.pushforward.{m} ψ).obj X = N)
    (M : SheafOfModules.{m} R₁)
    (iso : M ≅ (SheafOfModules.pushforward.{m} (eqToHom hR ≫ ψ)).obj X) :
    M ≅ hR.symm ▸ N := by
  subst hR
  subst hN
  simp only [eqToHom_refl, Category.id_comp] at iso
  exact iso

/-- **The counit of an equivalence, at an object in the image of a functor which the equivalence
carries to a given one.** If `G ⋙ eqv.functor = K`, then `G` is isomorphic to `K ⋙ eqv.inverse`
through the unit of `eqv` whiskered with that equality, and the counit of `eqv` at `K Z` is the
image under `eqv.functor` of the inverse of that isomorphism. -/
theorem counitApp_of_comp_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A] (eqv : C ≌ D) (G : A ⥤ C) {K : A ⥤ D}
    (h : G ⋙ eqv.functor = K) (Z : A) :
    eqv.counit.app (K.obj Z) =
      eqv.functor.map ((Functor.isoWhiskerLeft G eqv.unitIso ≪≫
          eqToIso (congrArg (fun T : A ⥤ D => T ⋙ eqv.inverse) h)).inv.app Z) ≫
        eqToHom (Functor.congr_obj h Z) := by
  subst h
  refine Eq.trans (Equivalence.counit_app_functor eqv (G.obj Z)) ?_
  refine Eq.trans
    (congrArg eqv.functor.map (Category.id_comp (eqv.unitInv.app (G.obj Z))).symm) ?_
  exact (Category.comp_id _).symm

/-- A presheaf maps the opposite of an `eqToHom` to the `eqToHom` of the reversed equation of
its values. -/
private theorem map_eqToHom_op {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : Cᵒᵖ ⥤ D) {X Y : C} (h : X = Y) :
    F.map (eqToHom h).op = eqToHom (congrArg (fun Z => F.obj (op Z)) h).symm :=
  Eq.trans (congrArg F.map (eqToHom_op _)) (eqToHom_map _ _)

/-! ### The two index functors and their identification -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (U.1 ⋙ typeToCat)).p)

/-- The small étale inclusion of Stacks 06W1 at the object of `𝒳` attached to an étale chart `W`
of `U`: the small étale site of the scheme below that object, inside the big fppf slice at it. -/
noncomputable abbrev chartLocalInclusion (W : SmallEtale B S hS U.1) :=
  Stack.smallEtaleInclusion B (associatedBigEtaleSite B) rfl
    (p.obj (restrictionChartObject B S hS U p e W)).left.1
    (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
      (restrictionChartObject B S hS U p e W))

/-- The canonical localization functor of Stacks 06W0 at the object of `𝒳` attached to an étale
chart `W` of `U`. -/
noncomputable abbrev chartLocalOverPost (W : SmallEtale B S hS U.1) :=
  Over.post (X := restrictionChartObject B S hS U p e W) (p ⋙ Over.forget (B.obj hS))

/-- The chart-local equivalence of sites followed by `CategoryTheory.Over.post u_U`: the small
étale site of the scheme below `u_U W`, read as a slice of `𝒳` at `u_U W`. -/
noncomputable abbrev chartLocalSliceFunctor (W : SmallEtale B S hS U.1) :=
  (chartLocalSiteEquivalence B S hS U p e W).functor ⋙
    Over.post (X := W) (restrictionFunctor B S hS U.1 p e)

/-- The functor `W_étale ⥤ 𝒳` along which equation 075K restricts an `𝒪_𝒳`-module and then
localizes at an étale chart `W` of `U`. -/
noncomputable abbrev chartLocalMidFunctor (W : SmallEtale B S hS U.1) :=
  Over.forget W ⋙ etaleChartToFibred B S hS p e (𝟭 𝒳)

/-- The index functor of the equation 075K side: the chart-local equivalence of sites followed by
the slice projection and the functor `u_U : U_étale ⥤ 𝒳` of Stacks 073M. -/
noncomputable abbrev chartLocalIndexFunctor (W : SmallEtale B S hS U.1) :=
  (chartLocalSiteEquivalence B S hS U p e W).functor ⋙ chartLocalMidFunctor B S hS U p e W

/-- The small étale topology on the site below the object of `𝒳` attached to an étale chart. -/
noncomputable abbrev chartLocalTopology (W : SmallEtale B S hS U.1) :=
  _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    (p.obj (restrictionChartObject B S hS U p e W)).left.1
    (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
      (restrictionChartObject B S hS U p e W))

/-- The functor `u_U : U_étale ⥤ 𝒳` of Stacks 073M is over the base, read after forgetting down to
the underlying category of schemes. -/
theorem restrictionFunctor_comp_forget :
    restrictionFunctor B S hS U.1 p e ⋙ (p ⋙ Over.forget (B.obj hS)) =
      SmallEtale.toOver B S hS U.1 ⋙ Over.forget (B.obj hS) :=
  congrArg (fun k : SmallEtale B S hS U.1 ⥤ BigFppfOver B S hS =>
    k ⋙ Over.forget (B.obj hS)) (restrictionFunctor_comp B S hS U.1 p e)

/-- **The two restrictions of the chart-local identification agree on the nose after
localization.** The chart-local equivalence of sites, followed by `CategoryTheory.Over.post u_U`
and by the localization functor of Stacks 06W0, is the small étale inclusion of Stacks 06W1.

This is the object-level half of Remark 0GQA. -/
theorem chartLocalSliceFunctor_comp_overPost (W : SmallEtale B S hS U.1) :
    chartLocalSliceFunctor B S hS U p e W ⋙ chartLocalOverPost B S hS U p e W =
      chartLocalInclusion B S hS U p e W :=
  transportSmallEtale_post_eq B (associatedBigEtaleSite B) rfl W
    (restrictionFunctor_comp_forget B S hS U p e)
    (chartOverObject B S hS U W).left.property
    (chartSchemeEquivalence B S hS U W) rfl
    (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
      (restrictionChartObject B S hS U p e W))

variable (hp : p.IsFiberedInGroupoids)

include hp

/-- The index functor of the Stacks 06W1 side: the small étale inclusion, the chosen quasi-inverse
of the localization equivalence of Stacks 06W0, and the slice projection. This is the functor
`AlgebraicGeometry.Stack.restrictModuleToSmallEtale` restricts along. -/
noncomputable def localRestrictionIndexFunctor (W : SmallEtale B S hS U.1) :
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      (p.obj (restrictionChartObject B S hS U p e W)).left.1
      (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
        (restrictionChartObject B S hS U p e W)) ⥤ 𝒳 :=
  letI := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
  chartLocalInclusion B S hS U p e W ⋙ (chartLocalOverPost B S hS U p e W).inv ⋙
    Over.forget (restrictionChartObject B S hS U p e W)

/-- The comparison of the two index functors, read in the slice of `𝒳` at the object attached to
an étale chart: the unit isomorphism of the localization equivalence of Stacks 06W0, whiskered
with the equality `AlgebraicGeometry.Space.chartLocalSliceFunctor_comp_overPost`.

**The two index functors of the chart-local identification are canonically isomorphic.**

The restriction of Stacks 06W1 at `u_U W` and the restriction of equation 075K localized at `W`
evaluate an `𝒪_𝒳`-module at two objects of `𝒳` which are not definitionally equal, one produced by
the chosen quasi-inverse of the localization equivalence of Stacks 06W0 and the other by the
chosen inverse of the equivalence over the site of Stacks 073M. This is the isomorphism between
them, natural in the étale chart of the scheme below `u_U W`. -/
noncomputable def chartRestrictionSliceIso (W : SmallEtale B S hS U.1) :
    letI := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
    chartLocalSliceFunctor B S hS U p e W ≅
      chartLocalInclusion B S hS U p e W ⋙ (chartLocalOverPost B S hS U p e W).inv :=
  letI := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
  Functor.isoWhiskerLeft (chartLocalSliceFunctor B S hS U p e W)
      (chartLocalOverPost B S hS U p e W).asEquivalence.unitIso ≪≫
    eqToIso (congrArg (fun F : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) ⥤
        Over ((p ⋙ Over.forget (B.obj hS)).obj (restrictionChartObject B S hS U p e W)) =>
      F ⋙ (chartLocalOverPost B S hS U p e W).asEquivalence.inverse)
      (chartLocalSliceFunctor_comp_overPost B S hS U p e W))

/-- `AlgebraicGeometry.Space.chartRestrictionSliceIso` after the slice projection: the comparison
of the two index functors into `𝒳`. -/
noncomputable def chartRestrictionIndexIso (W : SmallEtale B S hS U.1) :
    chartLocalIndexFunctor B S hS U p e W ≅ localRestrictionIndexFunctor B S hS U p e hp W :=
  Functor.isoWhiskerRight (chartRestrictionSliceIso B S hS U p e hp W)
    (Over.forget (restrictionChartObject B S hS U p e W))

/-! ### Continuity of the two index functors -/

/-- The slice projection followed by `u_U` is continuous for the étale topologies. -/
theorem isContinuous_chartLocalMidFunctor (W : SmallEtale B S hS U.1) :
    (chartLocalMidFunctor B S hS U p e W).IsContinuous
      ((SmallEtale.topology B S hS U.1).over W)
      (BigFppfOver.associatedTopology B S hS p SiteKind.etale) :=
  let := etaleChartToFibred_isContinuous B S hS p p hp e (𝟭 𝒳)
    (Functor.IsFibredOneMorphism.id p)
  Functor.isContinuous_comp _ _ ((SmallEtale.topology B S hS U.1).over W)
    (SmallEtale.topology B S hS U.1)
    (BigFppfOver.associatedTopology B S hS p SiteKind.etale)

/-- The index functor of the equation 075K side is continuous for the étale topologies. -/
theorem isContinuous_chartLocalIndexFunctor (W : SmallEtale B S hS U.1) :
    (chartLocalIndexFunctor B S hS U p e W).IsContinuous (chartLocalTopology B S hS U p e W)
      (BigFppfOver.associatedTopology B S hS p SiteKind.etale) :=
  let := isContinuous_chartLocalMidFunctor B S hS U p e hp W
  Functor.isContinuous_comp _ _ (chartLocalTopology B S hS U p e W)
    ((SmallEtale.topology B S hS U.1).over W)
    (BigFppfOver.associatedTopology B S hS p SiteKind.etale)

/-- **The index functor of the Stacks 06W1 side is continuous for the étale topologies.** -/
theorem isContinuous_localRestrictionIndexFunctor (W : SmallEtale B S hS U.1) :
    (localRestrictionIndexFunctor B S hS U p e hp W).IsContinuous
      (chartLocalTopology B S hS U p e W)
      (BigFppfOver.associatedTopology B S hS p SiteKind.etale) :=
  let := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
  Functor.isContinuous_of_iso (chartRestrictionIndexIso B S hS U p e hp W) _ _

/-! ### The two sides as single pushforwards of `ℱ` -/

/-- The coefficient homomorphism of the Stacks 06W1 side: the identification
`AlgebraicGeometry.Stack.localStructurePresheafIso` of the structure sheaf of the small étale site
of the scheme below `u_U W` with the restriction there of the structure sheaf of `𝒳`, read as a
morphism of sheaves of rings. -/
noncomputable def localRestrictionCoefficient (W : SmallEtale B S hS U.1) :
    letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
    _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) ⟶
      ((localRestrictionIndexFunctor B S hS U p e hp W).sheafPushforwardContinuous RingCat.{u}
          (chartLocalTopology B S hS U p e W)
          (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).obj
        (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale) :=
  letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
  ObjectProperty.homMk (Stack.localStructurePresheafIso B (associatedBigEtaleSite B) rfl S hS
    p hp (restrictionChartObject B S hS U p e W) (etaleTopology B)
    (Stack.etaleTopology_le_topology B)).hom

/-- **The restriction of Stacks 06WJ at `u_U W` is a pushforward of `ℱ`.** The restriction
`ℱ|_{W_étale}` which local quasi-coherence supplies at the object of `𝒳` attached to an étale
chart is the pushforward of `ℱ` along the Stacks 06W1 index functor with
`AlgebraicGeometry.Space.localRestrictionCoefficient` as coefficient homomorphism. -/
theorem restrictionChartModule_eq_pushforward (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS p hp ℱ.val)
    (W : SmallEtale B S hS U.1) :
    letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
    (SheafOfModules.pushforward.{m} (localRestrictionCoefficient B S hS U p e hp W)).obj ℱ =
      restrictionChartModule B (associatedBigEtaleSite B) rfl S hS U p hp e ℱ hℱ W := rfl

/-- The coefficient homomorphism `𝒪_U = u_U^*𝒪_𝒳` of equation 075K. -/
noncomputable abbrev chartRestrictionBaseCoefficient :=
  etaleChartStructureHom B S hS p p hp hp e (𝟭 𝒳) (Functor.IsFibredOneMorphism.id p)

/-- The coefficient homomorphism of equation 075K localized at an étale chart `W` of `U`. -/
noncomputable abbrev chartRestrictionMidCoefficient (W : SmallEtale B S hS U.1) :
    letI := isContinuous_chartLocalMidFunctor B S hS U p e hp W
    (structureRingSheaf B S hS U).over W ⟶
      ((chartLocalMidFunctor B S hS U p e W).sheafPushforwardContinuous RingCat.{u}
          ((SmallEtale.topology B S hS U.1).over W)
          (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).obj
        (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale) :=
  letI := isContinuous_chartLocalMidFunctor B S hS U p e hp W
  letI := etaleChartToFibred_isContinuous B S hS p p hp e (𝟭 𝒳)
    (Functor.IsFibredOneMorphism.id p)
  𝟙 ((structureRingSheaf B S hS U).over W) ≫
    ((Over.forget W).sheafPushforwardContinuous RingCat.{u}
      ((SmallEtale.topology B S hS U.1).over W)
      (SmallEtale.topology B S hS U.1)).map (chartRestrictionBaseCoefficient B S hS U p e hp)

/-- The coefficient homomorphism of the equation 075K side, after the three nested pushforwards
have been merged into one. -/
noncomputable abbrev chartRestrictionCoefficient (W : SmallEtale B S hS U.1) :
    letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
    Stacks.SheafOfModules.reindexRing (chartLocalTopology B S hS U p e W)
        (chartLocalSiteEquivalence B S hS U p e W) ((structureRingSheaf B S hS U).over W) ⟶
      ((chartLocalIndexFunctor B S hS U p e W).sheafPushforwardContinuous RingCat.{u}
          (chartLocalTopology B S hS U p e W)
          (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).obj
        (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale) :=
  letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
  letI := isContinuous_chartLocalMidFunctor B S hS U p e hp W
  𝟙 (Stacks.SheafOfModules.reindexRing (chartLocalTopology B S hS U p e W)
      (chartLocalSiteEquivalence B S hS U p e W) ((structureRingSheaf B S hS U).over W)) ≫
    (((chartLocalSiteEquivalence B S hS U p e W).functor).sheafPushforwardContinuous
      RingCat.{u} (chartLocalTopology B S hS U p e W)
      ((SmallEtale.topology B S hS U.1).over W)).map
      (chartRestrictionMidCoefficient B S hS U p e hp W)

/-- The restriction `ℱ|_{U_étale}` of equation 075K, typed at the structure sheaf of the small
étale site of `U` rather than at the projection of the ringed site. -/
noncomputable abbrev chartRestrictionModule (ℱ : inheritedEtaleModules B S hS p hp) :
    SheafOfModules.{m} (structureRingSheaf B S hS U) :=
  etaleRestrictedModuleInverseImage B S hS p p hp hp e (𝟭 𝒳)
    (Functor.IsFibredOneMorphism.id p) ℱ

/-- **The equation 075K side is a single pushforward of `ℱ`.** Restricting `ℱ` along `u_U`, then
to the slice at an étale chart `W`, then across the chart-local equivalence of sites, is the
pushforward of `ℱ` along `AlgebraicGeometry.Space.chartLocalIndexFunctor` with
`AlgebraicGeometry.Space.chartRestrictionCoefficient` as coefficient homomorphism. -/
noncomputable def chartRestrictionPushforwardIso (ℱ : inheritedEtaleModules B S hS p hp)
    (W : SmallEtale B S hS U.1) :
    letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
    (SheafOfModules.pushforward.{m} (𝟙 (Stacks.SheafOfModules.reindexRing
        (chartLocalTopology B S hS U p e W) (chartLocalSiteEquivalence B S hS U p e W)
        ((structureRingSheaf B S hS U).over W)))).obj
      ((chartRestrictionModule B S hS U p e hp ℱ).over W) ≅
      (SheafOfModules.pushforward.{m} (chartRestrictionCoefficient B S hS U p e hp W)).obj ℱ :=
  letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
  letI := isContinuous_chartLocalMidFunctor B S hS U p e hp W
  letI := etaleChartToFibred_isContinuous B S hS p p hp e (𝟭 𝒳)
    (Functor.IsFibredOneMorphism.id p)
  (SheafOfModules.pushforward.{m} (𝟙 (Stacks.SheafOfModules.reindexRing
        (chartLocalTopology B S hS U p e W) (chartLocalSiteEquivalence B S hS U p e W)
        ((structureRingSheaf B S hS U).over W)))).mapIso
      ((SheafOfModules.pushforwardComp.{m} (𝟙 ((structureRingSheaf B S hS U).over W))
        (chartRestrictionBaseCoefficient B S hS U p e hp)).app ℱ) ≪≫
    (SheafOfModules.pushforwardComp.{m} (𝟙 (Stacks.SheafOfModules.reindexRing
        (chartLocalTopology B S hS U p e W) (chartLocalSiteEquivalence B S hS U p e W)
        ((structureRingSheaf B S hS U).over W)))
      (chartRestrictionMidCoefficient B S hS U p e hp W)).app ℱ

/-! ### The one equation that remains -/

omit hp in
/-- `AlgebraicGeometry.Space.chartLocalSiteEquivalence_ringSheaf`, restated with the structure
sheaf of the small étale site of `U` written in the plain reading
`AlgebraicGeometry.Space.structureRingSheaf` rather than as the projection of the ringed site. -/
theorem chartLocalRingSheaf_eq (W : SmallEtale B S hS U.1) :
    Stacks.SheafOfModules.reindexRing (chartLocalTopology B S hS U p e W)
        (chartLocalSiteEquivalence B S hS U p e W) ((structureRingSheaf B S hS U).over W) =
      _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) :=
  chartLocalSiteEquivalence_ringSheaf B S hS U p e W

/-- The coefficient homomorphism of the Stacks 06W1 side, with its source moved across the
equality of the two structure sheaves of the chart-local identification. -/
noncomputable abbrev localRestrictionCoefficientShift (W : SmallEtale B S hS U.1) :
    letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
    Stacks.SheafOfModules.reindexRing (chartLocalTopology B S hS U p e W)
        (chartLocalSiteEquivalence B S hS U p e W) ((structureRingSheaf B S hS U).over W) ⟶
      ((localRestrictionIndexFunctor B S hS U p e hp W).sheafPushforwardContinuous RingCat.{u}
          (chartLocalTopology B S hS U p e W)
          (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).obj
        (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale) :=
  letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
  eqToHom (chartLocalRingSheaf_eq B S hS U p e W) ≫
    localRestrictionCoefficient B S hS U p e hp W

/-- **The semilinearity of the chart-local identification**: the two structure-sheaf
identifications of the situation correspond under
`AlgebraicGeometry.Space.chartRestrictionIndexIso`.

Concretely: transporting the coefficient homomorphism of equation 075K along the isomorphism of
index functors gives the coefficient homomorphism of Stacks 06W1, read through the equality of the
two structure sheaves. This is the algebraic residue of Remark 0GQA. -/
noncomputable abbrev ChartRestrictionSemilinear (W : SmallEtale B S hS U.1) : Prop :=
  letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
  letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
  chartRestrictionCoefficient B S hS U p e hp W ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (chartRestrictionIndexIso B S hS U p e hp W).inv
        RingCat.{u} (chartLocalTopology B S hS U p e W)
        (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).app
        (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale) =
    localRestrictionCoefficientShift B S hS U p e hp W

/-! ### The semilinearity -/

/-- The opposite of the site of the chart-local identification, the index category of the two
sheaves of rings the semilinearity compares. -/
noncomputable abbrev chartLocalSiteOp (W : SmallEtale B S hS U.1) :=
  (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
    (p.obj (restrictionChartObject B S hS U p e W)).left.1
    (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
      (restrictionChartObject B S hS U p e W)))ᵒᵖ

/-- The structure sheaf of the big fppf site of the scheme below the object of `𝒳` attached to an
étale chart: the presheaf of rings through which both sides of the semilinearity factor. -/
noncomputable abbrev chartLocalBaseSheaf (W : SmallEtale B S hS U.1) :=
  (Stack.baseRingStructureSheaf B (p.obj (restrictionChartObject B S hS U p e W)).left.1
    (p.obj (restrictionChartObject B S hS U p e W)).left.2 (etaleTopology B)
    (Stack.etaleTopology_le_topology B)).obj

/-- `AlgebraicGeometry.Space.counitApp_of_comp_eq` at the chart-local identification: the counit of
the localization equivalence of Stacks 06W0 at the small étale inclusion of an object is the image
of `AlgebraicGeometry.Space.chartRestrictionSliceIso` inverted. -/
theorem chartLocal_counit_app (W : SmallEtale B S hS U.1)
    (Z : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      (p.obj (restrictionChartObject B S hS U p e W)).left.1
      (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
        (restrictionChartObject B S hS U p e W))) :
    letI := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
    (chartLocalOverPost B S hS U p e W).asEquivalence.counit.app
        ((chartLocalInclusion B S hS U p e W).obj Z) =
      (chartLocalOverPost B S hS U p e W).map
          ((chartRestrictionSliceIso B S hS U p e hp W).inv.app Z) ≫
        eqToHom (Functor.congr_obj (chartLocalSliceFunctor_comp_overPost B S hS U p e W) Z) :=
  let := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
  counitApp_of_comp_eq (chartLocalOverPost B S hS U p e W).asEquivalence
    (chartLocalSliceFunctor B S hS U p e W)
    (chartLocalSliceFunctor_comp_overPost B S hS U p e W) Z

/-- The coefficient homomorphism of the Stacks 06W1 side, on sections: pullback of regular
functions along the counit of the localization equivalence of Stacks 06W0. -/
theorem localRestrictionCoefficient_app (W : SmallEtale B S hS U.1)
    (Y : chartLocalSiteOp B S hS U p e W) :
    letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
    letI := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
    (localRestrictionCoefficient B S hS U p e hp W).hom.app Y =
      (chartLocalBaseSheaf B S hS U p e W).map
        ((chartLocalOverPost B S hS U p e W).asEquivalence.counit.app
          ((chartLocalInclusion B S hS U p e W).obj Y.unop)).op :=
  let := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
  rfl

/-- The coefficient homomorphism of the equation 075K side, on sections: pullback of regular
functions along the identification of the object of `(Sch/S)_{fppf}` below `u_U V` with the one
below `V`, for `V` the chart which the chart-local equivalence of sites produces. -/
theorem chartRestrictionCoefficient_app (W : SmallEtale B S hS U.1)
    (Y : chartLocalSiteOp B S hS U p e W) :
    letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
    (chartRestrictionCoefficient B S hS U p e hp W).hom.app Y =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p p e (𝟭 𝒳)
          (Functor.IsFibredOneMorphism.id p))
          (((chartLocalSiteEquivalence B S hS U p e W).functor.obj Y.unop).left))).op :=
  etaleChartStructureHom_app B S hS p p hp hp e (𝟭 𝒳)
    (Functor.IsFibredOneMorphism.id p) _

/-- Transport along `AlgebraicGeometry.Space.chartRestrictionIndexIso`, on sections: pullback of
regular functions along the image under the localization functor of Stacks 06W0 of the inverse of
`AlgebraicGeometry.Space.chartRestrictionSliceIso`. -/
theorem chartRestrictionIndexIso_natTrans_app (W : SmallEtale B S hS U.1)
    (Y : chartLocalSiteOp B S hS U p e W) :
    letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
    letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
    letI := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
    ((Functor.sheafPushforwardContinuousNatTrans
        (chartRestrictionIndexIso B S hS U p e hp W).inv
        RingCat.{u} (chartLocalTopology B S hS U p e W)
        (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).app
        (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)).hom.app Y =
      (chartLocalBaseSheaf B S hS U p e W).map
        ((chartLocalOverPost B S hS U p e W).map
          ((chartRestrictionSliceIso B S hS U p e hp W).inv.app Y.unop)).op :=
  let := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
  rfl

omit hp in
/-- **The cast of the chart-local identification of structure sheaves, on sections.** The
`CategoryTheory.eqToHom` of `AlgebraicGeometry.Space.chartLocalRingSheaf_eq`, followed by pullback
along the identification of objects of Stacks 06W1, is pullback along the identification of
Stacks 073M. -/
theorem chartLocalRingSheaf_cast_app (W : SmallEtale B S hS U.1)
    (Y : chartLocalSiteOp B S hS U p e W) :
    (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p p e (𝟭 𝒳)
          (Functor.IsFibredOneMorphism.id p))
          (((chartLocalSiteEquivalence B S hS U p e W).functor.obj Y.unop).left))).op =
      (eqToHom (chartLocalRingSheaf_eq B S hS U p e W)).hom.app Y ≫
        (chartLocalBaseSheaf B S hS U p e W).map
          (eqToHom (Functor.congr_obj
            (chartLocalSliceFunctor_comp_overPost B S hS U p e W) Y.unop)).op := by
  have hA : (eqToHom (chartLocalRingSheaf_eq B S hS U p e W)).hom.app Y =
      eqToHom (Functor.congr_obj (congrArg
        (fun T : Sheaf (chartLocalTopology B S hS U p e W) RingCat.{u} => T.obj)
        (chartLocalRingSheaf_eq B S hS U p e W)) Y) := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  have hB : (chartLocalBaseSheaf B S hS U p e W).map
      (eqToHom (Functor.congr_obj
        (chartLocalSliceFunctor_comp_overPost B S hS U p e W) Y.unop)).op =
      eqToHom (congrArg (fun Z => (chartLocalBaseSheaf B S hS U p e W).obj (op Z))
        (Functor.congr_obj
          (chartLocalSliceFunctor_comp_overPost B S hS U p e W) Y.unop)).symm :=
    map_eqToHom_op _ _
  refine Eq.trans (map_eqToHom_op _ _) ?_
  refine Eq.trans (eqToHom_trans (Functor.congr_obj (congrArg
        (fun T : Sheaf (chartLocalTopology B S hS U p e W) RingCat.{u} => T.obj)
        (chartLocalRingSheaf_eq B S hS U p e W)) Y)
      (congrArg (fun Z => (chartLocalBaseSheaf B S hS U p e W).obj (op Z))
        (Functor.congr_obj (chartLocalSliceFunctor_comp_overPost B S hS U p e W)
          Y.unop)).symm).symm ?_
  exact Eq.trans (congrArg (fun z => z ≫ _) hA.symm) (congrArg (fun z => _ ≫ z) hB.symm)

/-- `AlgebraicGeometry.Space.ChartRestrictionSemilinear` on sections. -/
theorem chartRestrictionSemilinear_app (W : SmallEtale B S hS U.1)
    (Y : chartLocalSiteOp B S hS U p e W) :
    letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
    letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
    (chartRestrictionCoefficient B S hS U p e hp W).hom.app Y ≫
        ((Functor.sheafPushforwardContinuousNatTrans
            (chartRestrictionIndexIso B S hS U p e hp W).inv
            RingCat.{u} (chartLocalTopology B S hS U p e W)
            (BigFppfOver.associatedTopology B S hS p SiteKind.etale)).app
            (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)).hom.app Y =
      (eqToHom (chartLocalRingSheaf_eq B S hS U p e W)).hom.app Y ≫
        (localRestrictionCoefficient B S hS U p e hp W).hom.app Y :=
  let := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
  let := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
  let := Stack.isEquivalence_overPost B S hS p hp (restrictionChartObject B S hS U p e W)
  Eq.trans (congrArg (fun z => z ≫ _) (chartRestrictionCoefficient_app B S hS U p e hp W Y))
    (Eq.trans
      (congrArg (fun z => _ ≫ z) (chartRestrictionIndexIso_natTrans_app B S hS U p e hp W Y))
      (Eq.trans (congrArg (fun z => z ≫ _) (chartLocalRingSheaf_cast_app B S hS U p e W Y))
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (congrArg (fun z => _ ≫ z)
              ((chartLocalBaseSheaf B S hS U p e W).map_comp
                (eqToHom (Functor.congr_obj
                  (chartLocalSliceFunctor_comp_overPost B S hS U p e W) Y.unop)).op
                ((chartLocalOverPost B S hS U p e W).map
                  ((chartRestrictionSliceIso B S hS U p e hp W).inv.app Y.unop)).op).symm)
            (Eq.trans
              (congrArg (fun z => _ ≫ (chartLocalBaseSheaf B S hS U p e W).map
                  (Quiver.Hom.op z)) (chartLocal_counit_app B S hS U p e hp W Y.unop).symm)
              (congrArg (fun z => _ ≫ z)
                (localRestrictionCoefficient_app B S hS U p e hp W Y)).symm)))))

/-- **The semilinearity of the chart-local identification.** This is Remark 0GQA at the level of
the structure sheaves: the identification
`AlgebraicGeometry.Stack.localStructurePresheafIso` of Stacks 06W1 and the identification
`AlgebraicGeometry.Space.etaleChartStructureHom` of equation 075K correspond under the
isomorphism `AlgebraicGeometry.Space.chartRestrictionIndexIso` of index functors. -/
theorem chartRestrictionSemilinear (W : SmallEtale B S hS U.1) :
    ChartRestrictionSemilinear B S hS U p e hp W := by
  ext Y : 3
  exact chartRestrictionSemilinear_app B S hS U p e hp W Y

/-! ### The module-level chart-local identification, and Stacks 0GQC -/

/-- **The module-level chart-local identification of restrictions: Remark 0GQA at the module
level.** For an étale chart `W` of `U`, the restriction `ℱ|_{U_étale}` of equation 075K, localized
at `W` and read across the chart-local equivalence of sites, is the restriction `ℱ|_{W_étale}` of
Stacks 06WJ at the object `u_U W` of `𝒳`.

It is built from `AlgebraicGeometry.Space.chartRestrictionIndexIso`, the identification of the
two objects of `𝒳` at which `ℱ` is evaluated, and
`AlgebraicGeometry.Space.chartRestrictionSemilinear`, the compatibility of that identification
with the two structure sheaves. -/
noncomputable def chartRestriction_iso (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS p hp ℱ.val)
    (W : SmallEtale B S hS U.1) :
    letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
    (SheafOfModules.pushforward.{m} (𝟙 (Stacks.SheafOfModules.reindexRing
        (chartLocalTopology B S hS U p e W) (chartLocalSiteEquivalence B S hS U p e W)
        ((structureRingSheaf B S hS U).over W)))).obj
      ((chartRestrictionModule B S hS U p e hp ℱ).over W) ≅
      (chartLocalRingSheaf_eq B S hS U p e W).symm ▸
        restrictionChartModule B (associatedBigEtaleSite B) rfl S hS U p hp e ℱ hℱ W :=
  letI := isContinuous_chartLocalIndexFunctor B S hS U p e hp W
  letI := isContinuous_localRestrictionIndexFunctor B S hS U p e hp W
  isoOfEqRingPushforward (chartLocalRingSheaf_eq B S hS U p e W)
    (localRestrictionCoefficient B S hS U p e hp W) ℱ _
    (restrictionChartModule_eq_pushforward B S hS U p e hp ℱ hℱ W) _
    (chartRestrictionPushforwardIso B S hS U p e hp ℱ W ≪≫
      (SheafOfModules.pushforwardCongr₂.{m} (chartRestrictionCoefficient B S hS U p e hp W)
        (chartRestrictionIndexIso B S hS U p e hp W).symm
        (chartRestrictionSemilinear B S hS U p e hp W)).app ℱ)

/-- Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by the algebraic
space `U`, through a chosen equivalence over the site as in Stacks 073M. If `ℱ` is a locally
quasi-coherent `𝒪_𝒳`-module (Stacks 06WJ) then its restriction `ℱ|_{U_étale}` (equation 075K) is
quasi-coherent.

The auxiliary big étale site is taken to be `AlgebraicGeometry.associatedBigEtaleSite` of the big
fppf site, which the source does not name; that is the canonical choice, and it is the one
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_chartLocalModuleIdentification` already makes. -/
@[stacks 0GQC]
theorem isQuasicoherentOnSite_etaleRestriction
    (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS p hp ℱ.val) :
    (etaleRestrictedModuleInverseImage B S hS p p hp hp e (𝟭 𝒳)
      (Functor.IsFibredOneMorphism.id p) ℱ).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_chartLocalModuleIdentification B S hS U p e hp ℱ hℱ
    (fun W => chartRestriction_iso B S hS U p e hp ℱ hℱ W)

end

end AlgebraicGeometry.Space

end
