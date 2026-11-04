module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.CategoryTheory.MorphismProperty.BaseChangeCommSquare

/-!
# Local finite presentation of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. A property `P` of morphisms of schemes
which is étale local on the source and target, stable under base change and fpqc local on the
target induces a property of morphisms of algebraic spaces over `S` — the every-chart condition
of **Stacks 03MJ**, part (1) — and that induced property is again local on the target, for the
fpqc topology of **Stacks 03YH**. Local finite presentation is such a `P` by **Stacks 04R3**,
**Stacks 03XR** and **Stacks 02KY**, so being locally of finite presentation is fpqc local on
the base for morphisms of algebraic spaces. That is **Stacks 041T**.

One direction of the criterion is base-change stability of the every-chart condition, which is
**Stacks 0AMM**. For the other, an arbitrary fpqc covering family is reduced to the affine case
in two steps. First, a morphism all of whose base changes along scheme-valued points with
*affine* source satisfy the chart condition satisfies it outright, because the condition is
tested one square of étale charts at a time and the chart of the target is covered by its affine
opens. Second, over an affine object of the site a surjective étale chart of the source is a
morphism of schemes, and `P` holds for that morphism by its own fpqc locality on the target; the
base changes this needs are read off the chart conditions of the given base changes, and one
surjective chart suffices by **Stacks 03MJ**. A covering family of algebraic spaces is reduced
to the affine case by the refinement clause of **Stacks 03MQ**.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isLocalAtTarget_fpqc`: the criterion, stated
  for an arbitrary property of morphisms of schemes.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fpqc`: **Stacks 041T**.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf`: the same at the
  fppf precoverage, which is the form the relative properties of Stacks 03YK consume.

## Implementation notes

The criterion is stated at a variable property of morphisms of schemes rather than at local
finite presentation alone. Nothing in the argument is special to local finite presentation: the
only inputs are `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget`, stability under base change,
and locality at the target for `AlgebraicGeometry.Scheme.fpqcPrecoverage`. Stating it this way
makes `AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc` (**Stacks 042A**) and
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc` (**Stacks 0429**) one application each; that
consolidation is not carried out here. The anticipated reuse has since been realised a third time:
`AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fpqc` (**Stacks 0427**) is one
application of this criterion at the meet
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`.

Tag 041T is in Descent on Spaces, **Chapter 74**, alongside
`AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fpqc` (Tag 041L),
`AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fpqc` (Tag 041W) and
`AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc` (Tag 042A). It
introduces no new notion: both the every-chart condition and the fpqc precoverage of algebraic
spaces are defined elsewhere.

## References

* [Stacks Project, Tag 02KY](https://stacks.math.columbia.edu/tag/02KY)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- If `snd` is the second projection of a pullback square and has `P`, then so does the canonical
second projection of the pullback. -/
private theorem pullback_snd_of_isPullback {C : Type*} [Category C] (P : MorphismProperty C)
    [P.RespectsIso] {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] (h : IsPullback fst snd f g) (hs : P snd) : P (pullback.snd f g) := by
  rwa [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso] at hs

/-- A morphism of algebraic spaces over `S` all of whose base changes along scheme-valued points
with affine source satisfy the every-chart condition of `P` satisfies it itself.

The chart condition is tested at one commuting square of étale charts at a time; the chart of the
target is covered by its affine opens, which are objects of the site because their size is bounded
by its, and over each of them the chart morphism is the base change of the given one along an
affine point, so the hypothesis applies after Zariski locality of `P` on the target. -/
private theorem holdsOnEveryEtaleChart_of_affine_baseChanges
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : ∀ (T : BigAffineFppf B S hS)
      (g : schemeSpace ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
      HoldsOnEveryEtaleChart B S hS P (pullback.snd f g).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  intro U V a b h ha hb comm
  let q := BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q
  let : E.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  let : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  let : E.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  let : E.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition E
  have hisEtale : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : F ⟶ G),
      E.presheaf x → IsEtale B S hS x :=
    fun x hx _ y hy => E.presheaf.comp_mem y x hy hx
  let C := (q.obj V).affineCover
  let : P.IsLocalAtTarget Scheme.zariskiPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := P) C
  intro i
  have hVi : B.Contains (C.X i) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_locallyOfFinitePresentation (C.f i))
      V.left.property
  let ViSite : B.Schemes := B.obj hVi
  let j0 : ViSite ⟶ V.left :=
    B.inclusion.preimage (X := ViSite) (Y := V.left) (C.f i)
  let Vi : BigFppfOver B S hS := Over.mk (j0 ≫ V.hom)
  let j : Vi ⟶ V := Over.homMk j0
  have hj : q.map j = C.f i := by
    show B.inclusion.map j0 = C.f i
    exact B.inclusion.map_preimage _
  have hViAffine : IsAffine (q.obj Vi) := Scheme.isAffine_affineCover (q.obj V) i
  let W := pullback h j
  let r : W ⟶ U := pullback.fst h j
  let s : W ⟶ Vi := pullback.snd h j
  have hs : IsPullback (q.map r) (q.map s) (q.map h) (C.f i) := by
    rw [← hj]
    exact (IsPullback.of_hasPullback h j).map q
  have hjEtale : E j := by
    show Etale (q.map j)
    rw [hj]
    infer_instance
  have hrEtale : E r :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := E) (IsPullback.of_hasPullback h j).flip hjEtale
  let bi : yoneda.obj Vi ⟶ Y.obj := yoneda.map j ≫ b
  let ai : yoneda.obj W ⟶ X.obj := yoneda.map r ≫ a
  have hbi : E.presheaf bi :=
    E.presheaf.comp_mem _ _ (MorphismProperty.relative_map (F := yoneda) hjEtale) hb
  have hai : E.presheaf ai :=
    E.presheaf.comp_mem _ _ (MorphismProperty.relative_map (F := yoneda) hrEtale) ha
  let g : schemeSpace Vi ⟶ Y := ObjectProperty.homMk bi
  have sq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)
  have hc : ai ≫ f.hom = yoneda.map s ≫ bi := by
    dsimp [ai, bi]
    rw [Category.assoc, ← comm, ← Category.assoc, ← Functor.map_comp,
      pullback.condition, Functor.map_comp, Category.assoc]
  let p : yoneda.obj W ⟶ (pullback f g).obj := sq.lift ai (yoneda.map s) hc
  have hpE : IsEtale B S hS p :=
    isEtale_of_isEtale_over B S hS
      (isAlgebraicSpace_yoneda B S hS W) (pullback f g).property X.property
      p ai (pullback.fst f g).hom
      (hisEtale ai hai)
      (hisEtale _
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := E.presheaf) sq.flip hbi)) (sq.lift_fst _ _ _)
  have hpRel : E.presheaf p := by
    simpa using hpE W (𝟙 _) (presheaf_etale_id B S hS W)
  have hsP : P (q.map s) := (hf ⟨Vi, hViAffine⟩ g) W Vi p (𝟙 _) s hpRel
    (presheaf_etale_id B S hS Vi) (by
      show yoneda.map s ≫ 𝟙 (yoneda.obj Vi) = p ≫ (pullback.snd f g).hom
      rw [Category.comp_id]
      exact (sq.lift_snd ai (yoneda.map s) hc).symm)
  exact pullback_snd_of_isPullback P hs hsP

/-- If a morphism of algebraic spaces into the space of a site object has a base change along a
site morphism `k` satisfying the every-chart condition of `P`, then the base change along `k` of a
chart morphism of its source has `P` as a morphism of schemes.

This is the step that turns the chart condition of Stacks 03MJ into a statement about the
representing schemes: the fibre product of the chart with `k` maps to the base-changed space by
the universal property, relatively étale because it is a base change of the chart, so the
hypothesis can be read on it. -/
private theorem holdsOnEveryEtaleChart_chartBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X : AlgebraicSpaces B S hS} {U V V' : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace V)
    (p : yoneda.obj U ⟶ X.obj)
    (hpEtale :
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p)
    (h : U ⟶ V) (hh : yoneda.map h = p ≫ f.hom)
    (k : V' ⟶ V)
    (hf : HoldsOnEveryEtaleChart B S hS P (pullback.snd f (schemeSpaceMap k)).hom) :
    P (pullback.snd
      ((BigFppfOver.toScheme B S hS).map h)
      ((BigFppfOver.toScheme B S hS).map k)) := by
  let q := BigFppfOver.toScheme B S hS
  let W := pullback h k
  let r : W ⟶ U := pullback.fst h k
  let s : W ⟶ V' := pullback.snd h k
  let g' := schemeSpaceMap k
  let X' := pullback f g'
  have sqh := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g')
  let pp : yoneda.obj W ⟶ X'.obj :=
    sqh.lift (yoneda.map r ≫ p) (yoneda.map s) (by
      show yoneda.map r ≫ (p ≫ f.hom) = yoneda.map s ≫ yoneda.map k
      rw [← hh]
      show yoneda.map r ≫ yoneda.map h = yoneda.map s ≫ yoneda.map k
      dsimp [r, s, W]
      simpa only [Functor.map_comp] using
        congrArg yoneda.map (pullback.condition : r ≫ h = s ≫ k))
  have sqW : IsPullback (yoneda.map s) (yoneda.map r)
      (yoneda.map k) (yoneda.map h) :=
    ((IsPullback.of_hasPullback h k).map yoneda).flip
  have pp_fst : pp ≫ (pullback.fst f g').hom = yoneda.map r ≫ p :=
    sqh.lift_fst _ _ _
  have pp_snd : pp ≫ (pullback.snd f g').hom = yoneda.map s :=
    sqh.lift_snd _ _ _
  have outer : IsPullback (pp ≫ (pullback.snd f g').hom)
      (yoneda.map r) g'.hom (p ≫ f.hom) := by
    rw [pp_snd, ← hh]
    exact sqW
  have sqAtlas : IsPullback pp (yoneda.map r) (pullback.fst f g').hom p :=
    outer.of_right pp_fst sqh.flip
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q
  let : E.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  let : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  have hppEtale : E.presheaf pp :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := E.presheaf) sqAtlas.flip hpEtale
  have hW : P (q.map s) := by
    apply hf W V' pp (𝟙 _) s hppEtale (presheaf_etale_id B S hS V')
    show yoneda.map s ≫ (𝟙 (yoneda.obj V')) = pp ≫ (pullback.snd f g').hom
    simpa only [schemeSpace, Category.comp_id] using pp_snd.symm
  exact pullback_snd_of_isPullback P ((IsPullback.of_hasPullback h k).map q) hW

/-- A morphism of algebraic spaces into the space of an affine object of the site satisfies the
every-chart condition of `P` as soon as its base changes along the members of a presieve covering
that object in the scheme-level fpqc precoverage do.

A surjective étale chart of the source gives a scheme morphism to the affine object; it has `P` by
fpqc locality of `P` on the base applied to that presieve, each base change being supplied by
`holdsOnEveryEtaleChart_chartBaseChange`; and one surjective chart suffices by Stacks 03MJ. -/
private theorem holdsOnEveryEtaleChart_of_affineFpqcPresieve
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (T : BigAffineFppf B S hS) (R : Presieve T)
    (hR : R.map (BigAffineFppf.toScheme B S hS) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T))
    (X : AlgebraicSpaces B S hS)
    (f : X ⟶ schemeSpace ((BigAffineFppf.inclusion B S hS).obj T))
    (hf : ∀ {T' : BigAffineFppf B S hS} (g : T' ⟶ T),
      R g → HoldsOnEveryEtaleChart B S hS P
        (pullback.snd f (schemeSpaceMap
          ((BigAffineFppf.inclusion B S hS).map g))).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := X.property.exists_atlas
  let V := (BigAffineFppf.inclusion B S hS).obj T
  let h : U ⟶ V := yoneda.preimage (p ≫ f.hom)
  have hh : yoneda.map h = p ≫ f.hom := yoneda.map_preimage _
  let q := BigFppfOver.toScheme B S hS
  have hscheme : P (q.map h) := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := P) (f := q.map h) hR
    intro W j hj hmem
    rcases hmem with ⟨hg⟩
    rename_i T' g
    exact holdsOnEveryEtaleChart_chartBaseChange B S hS P f p hpEtale h hh
      ((BigAffineFppf.inclusion B S hS).map g) (hf g hg)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP
    X.property (schemeSpace V).property f.hom).mpr
    ⟨U, V, p, 𝟙 _, h, hpEtale, presheaf_etale_id B S hS V, hpSurj,
      by simpa only [schemeSpace, Category.comp_id] using hh, hscheme⟩

/-- A property of morphisms of schemes which is étale local on the source and target, stable under
base change and local on the target for the fpqc topology of schemes induces a property of
morphisms of algebraic spaces over `S` — the every-chart condition of **Stacks 03MJ**, part (1) —
which is local on the target for the fpqc topology of **Stacks 03YH**. -/
theorem holdsOnEveryEtaleChart_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fpqcPrecoverage] :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.fpqc.precoverage.{u, v} B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) := fun {_ _} f =>
    HoldsOnEveryEtaleChart B S hS P f.hom
  let : Q.IsStableUnderBaseChange :=
    holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS P hP
  let : Q.RespectsIso := inferInstance
  refine { pullbackSnd := ?_, of_forall_pullbackSnd := ?_ }
  · intro X Y f R U g hR hg hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := Q) (IsPullback.of_hasPullback f g) hf
  · intro X Y f R hR h
    obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
    obtain ⟨hY, hYi, hfpqc⟩ := hcover
    change IsFpqcCovering B S hS (fun i => (gi i).hom) at hfpqc
    apply holdsOnEveryEtaleChart_of_affine_baseChanges B S hS P f
    intro T gT
    obtain ⟨U, hfinite, hUcover, href⟩ := hfpqc.2 T gT.hom
    apply holdsOnEveryEtaleChart_of_affineFpqcPresieve B S hS P hP T
      U.presieve₀ hUcover (pullback f gT) (pullback.snd f gT)
    intro T' k hk
    rcases hk with ⟨j⟩
    obtain ⟨i, a, ha⟩ := href j
    let a' : schemeSpace ((BigAffineFppf.inclusion B S hS).obj (U.X j)) ⟶ Yi i :=
      ObjectProperty.homMk a
    let k' := schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map (U.f j))
    have hcomm : a' ≫ gi i = k' ≫ gT := ObjectProperty.hom_ext _ ha
    exact MorphismProperty.pullbackSnd_of_comm Q f (gi i) gT a' k' hcomm
      (h (g := gi i) (Presieve.ofArrows.mk i))

/-- **Stacks Project, Tag 041T** (Lemma 74.11.10 of Chapter 74, *Descent and Algebraic
Spaces*). The property `𝒫(f)` = "`f` is locally of finite presentation" of morphisms of
algebraic spaces over `S` is fpqc local on the base.

The setting is the source's own. By the conventions of that chapter (**Stacks 041I**, Section
74.2) every scheme lies in a big fppf site `Sch_fppf`, here `B`, and `S` is one of its objects;
algebraic spaces over `S` are the objects of `AlgebraicSpaces B S S_mem`, and local finite
presentation of a morphism of algebraic spaces is that of **Stacks 03XP**, part (1). "Fpqc local
on the base" is Definition 74.10.1 (**Stacks 03YH**) at the fpqc topology: for every fpqc
covering `{Yᵢ → Y}` of algebraic spaces in the sense of **Stacks 03MQ**, indexed by a type in any
universe `v`, and every morphism `f : X ⟶ Y`, the morphism `f` is locally of finite presentation
if and only if every base change `Yᵢ ×_Y X → Yᵢ` is. That is the class
`CategoryTheory.MorphismProperty.IsLocalAtTarget` at `Topology.fpqc.precoverage`, whose coverings
are exactly the families `Presieve.ofArrows Yᵢ gᵢ` with `gᵢ` an fpqc covering of `Y`.

The scheme-level statement, for morphisms of schemes, is Descent, Lemma 35.23.13 (**Stacks
02KY**), `Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fpqc`; the proof of the
source reduces to it, and so does this one. -/
@[stacks 041T,
  ega "IV 2.7.1" "more general",
  sga "3 VIB 10.8" "(i)⇒(ii)",
  sga "4 IV 8.5.5" "more general"]
instance isLocallyOfFinitePresentation_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (S_mem : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S S_mem⦄ (f : X ⟶ Y) =>
        IsLocallyOfFinitePresentation B S S_mem f.hom)
      (Topology.fpqc.precoverage.{u, v} B S S_mem) :=
  holdsOnEveryEtaleChart_isLocalAtTarget_fpqc B S S_mem
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget

/-- **Stacks 041T** at the fppf precoverage: being locally of finite presentation is local on the
target for the fppf topology of algebraic spaces. This is the form in which the relative
properties of Stacks 03YK ask for it, and it follows from the fpqc form because every fppf
covering family of algebraic spaces is an fpqc covering family. -/
instance isLocallyOfFinitePresentation_isLocalAtTarget_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        IsLocallyOfFinitePresentation B S hS f.hom)
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
