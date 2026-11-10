module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FinitenessConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.CategoryTheory.MorphismProperty.BaseChangeCommSquare

/-!
# Unramifiedness of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. Unramifiedness of a morphism of algebraic
spaces over `S`, the chart condition `AlgebraicGeometry.Space.IsUnramified`, is local on the target
for the fpqc topology.

## Main results

* `AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc`: unramifiedness of morphisms of
  algebraic spaces over `S` is local on the target for the fpqc precoverage.
* `AlgebraicGeometry.Space.isUnramified_iff_forall_pullbackSnd_of_isFpqcCovering`: for an fpqc
  covering `{gᵢ : Yᵢ ⟶ Y}`, a morphism `f : X ⟶ Y` is unramified if and only if every base change
  `Yᵢ ×_Y X ⟶ Yᵢ` is.

## References

* [Stacks Project, Tag 02VM](https://stacks.math.columbia.edu/tag/02VM)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 03ZJ](https://stacks.math.columbia.edu/tag/03ZJ)
* [Stacks Project, Tag 042A](https://stacks.math.columbia.edu/tag/042A)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- If the second projection of a pullback square of schemes is unramified, so is the second
projection of the canonical pullback. -/
private theorem unramified_pullbackSnd_of_isPullback {X Y Z W : Scheme.{u}}
    {r : W ⟶ X} {s : W ⟶ Z} {h : X ⟶ Y} {k : Z ⟶ Y} (sq : IsPullback r s h k)
    (hs : AlgebraicGeometry.Unramified s) :
    AlgebraicGeometry.Unramified (pullback.snd h k) := by
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Unramified
  rw [← sq.isoPullback_hom_snd] at hs
  exact (P.cancel_left_of_respectsIso sq.isoPullback.hom _).mp hs

/-- A morphism of algebraic spaces over `S` all of whose base changes along scheme-valued
points with affine source are unramified is unramified. -/
private theorem unramified_of_affine_baseChanges
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : ∀ (T : BigAffineFppf B S hS)
      (g : schemeSpace ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
      IsUnramified B S hS (pullback.snd f g).hom) :
    IsUnramified B S hS f.hom := by
  intro U V a b h ha hb comm
  let q := BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q
  let : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  let C := (q.obj V).affineCover
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Unramified
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
    change B.inclusion.map j0 = C.f i
    exact B.inclusion.map_preimage _
  have hViAffine : IsAffine (q.obj Vi) := Scheme.isAffine_affineCover (q.obj V) i
  let W := pullback h j
  let r : W ⟶ U := pullback.fst h j
  let s : W ⟶ Vi := pullback.snd h j
  have hs : IsPullback (q.map r) (q.map s) (q.map h) (C.f i) := by
    rw [← hj]
    exact (IsPullback.of_hasPullback h j).map q
  have hjEtale : E j := by change Etale (q.map j); rw [hj]; infer_instance
  have hrEtale : E r :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := E) (IsPullback.of_hasPullback h j).flip hjEtale
  let bi : yoneda.obj Vi ⟶ Y.obj := yoneda.map j ≫ b
  let ai : yoneda.obj W ⟶ X.obj := yoneda.map r ≫ a
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hbi : E.presheaf bi := MorphismProperty.comp_mem _ _ _
    (MorphismProperty.relative_map (F := yoneda) hjEtale) hb
  have hai : E.presheaf ai := MorphismProperty.comp_mem _ _ _
    (MorphismProperty.relative_map (F := yoneda) hrEtale) ha
  let g : schemeSpace Vi ⟶ Y := ObjectProperty.homMk bi
  have sq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)
  have hc : ai ≫ f.hom = yoneda.map s ≫ bi := by
    dsimp [ai, bi]
    rw [Category.assoc, ← comm, ← Category.assoc, ← Functor.map_comp,
      pullback.condition, Functor.map_comp, Category.assoc]
  let p : yoneda.obj W ⟶ (pullback f g).obj := sq.lift ai (yoneda.map s) hc
  have hp : p ≫ (pullback.fst f g).hom = ai := sq.lift_fst _ _ _
  have hpE : IsEtale B S hS p :=
    isEtale_of_isEtale_over B S hS
      (isAlgebraicSpace_yoneda B S hS W) (pullback f g).property X.property
      p ai (pullback.fst f g).hom
      (isEtale_of_presheaf_etale B S hS hai)
      (isEtale_of_presheaf_etale B S hS
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := E.presheaf) sq.flip hbi)) hp
  have hpRel : E.presheaf p := by
    simpa using hpE W (𝟙 _) (presheaf_etale_id B S hS W)
  have hsP : P (q.map s) := (hf ⟨Vi, hViAffine⟩ g) W Vi p (𝟙 _) s hpRel
    (presheaf_etale_id B S hS Vi) (by
      change yoneda.map s ≫ 𝟙 (yoneda.obj Vi) = p ≫ (pullback.snd f g).hom
      rw [Category.comp_id]
      exact (sq.lift_snd ai (yoneda.map s) hc).symm)
  exact unramified_pullbackSnd_of_isPullback hs hsP

/-- If a morphism of algebraic spaces into the space of a site object has unramified base
change along a site morphism `k`, then the base change along `k` of a chart morphism of its
source is unramified as a morphism of schemes. -/
private theorem unramified_chartBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}
    {U V V' : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace V)
    (p : yoneda.obj U ⟶ X.obj)
    (hpEtale :
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p)
    (h : U ⟶ V) (hh : yoneda.map h = p ≫ f.hom)
    (k : V' ⟶ V)
    (hf : IsUnramified B S hS
      (pullback.snd f (schemeSpaceMap k)).hom) :
    AlgebraicGeometry.Unramified
      (pullback.snd
        ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).map k)) := by
  let q := BigFppfOver.toScheme B S hS
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Unramified
  let W := pullback h k
  let r : W ⟶ U := pullback.fst h k
  let s : W ⟶ V' := pullback.snd h k
  let g' := schemeSpaceMap k
  let X' := pullback f g'
  have sq : IsPullback (pullback.fst f g') (pullback.snd f g') f g' :=
    IsPullback.of_hasPullback f g'
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  let pp : yoneda.obj W ⟶ X'.obj :=
    sqh.lift (yoneda.map r ≫ p) (yoneda.map s) (by
      change yoneda.map r ≫ (p ≫ f.hom) = yoneda.map s ≫ yoneda.map k
      rw [← hh]
      change yoneda.map r ≫ yoneda.map h = yoneda.map s ≫ yoneda.map k
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
  have sqAtlas : IsPullback pp (yoneda.map r)
      (pullback.fst f g').hom p :=
    outer.of_right pp_fst sqh.flip
  let E : MorphismProperty (BigFppfOver B S hS) :=
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q)
  let := etale_inverseImage_isStableUnderBaseChange B S hS
  have : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  have hppEtale :
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q).presheaf pp :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q).presheaf)
      sqAtlas.flip hpEtale
  have hbEtale := presheaf_etale_id B S hS V'
  have hW : AlgebraicGeometry.Unramified (q.map s) := by
    apply hf W V' pp (𝟙 _) s hppEtale hbEtale
    change yoneda.map s ≫ (𝟙 (yoneda.obj V')) = pp ≫ (pullback.snd f g').hom
    simpa only [schemeSpace, Category.comp_id] using pp_snd.symm
  exact unramified_pullbackSnd_of_isPullback ((IsPullback.of_hasPullback h k).map q) hW

/-- A morphism of algebraic spaces into the space of an affine object of the site is unramified
as soon as its base changes along the members of a presieve covering that object in the
scheme-level fpqc precoverage are unramified. -/
private theorem unramified_of_affineFpqcPresieve
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigAffineFppf B S hS) (R : Presieve T)
    (hR : R.map (BigAffineFppf.toScheme B S hS) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T))
    (X : AlgebraicSpaces B S hS)
    (f : X ⟶ schemeSpace
      ((BigAffineFppf.inclusion B S hS).obj T))
    (hf : ∀ {T' : BigAffineFppf B S hS} (g : T' ⟶ T),
      R g → IsUnramified B S hS
        (pullback.snd f (schemeSpaceMap
          ((BigAffineFppf.inclusion B S hS).map g))).hom) :
    IsUnramified B S hS f.hom := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := X.property.exists_atlas
  let V := (BigAffineFppf.inclusion B S hS).obj T
  let h : U ⟶ V := yoneda.preimage (p ≫ f.hom)
  have hh : yoneda.map h = p ≫ f.hom := yoneda.map_preimage _
  let q := BigFppfOver.toScheme B S hS
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Unramified
  have hscheme : P (q.map h) := by
    apply (AlgebraicGeometry.unramified_isLocalAtTarget_fpqc :
      P.IsLocalAtTarget Scheme.fpqcPrecoverage).of_forall_pullbackSnd
        (f := q.map h) hR
    intro W j hj hmem
    rcases hmem with ⟨hg⟩
    rename_i T' g
    let k := (BigAffineFppf.inclusion B S hS).map g
    exact unramified_chartBaseChange B S hS f p hpEtale h hh k (hf g hg)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P
    AlgebraicGeometry.Unramified.isEtaleLocalOnSourceAndTarget
    X.property (schemeSpace V).property f.hom).mpr
    ⟨U, V, p, 𝟙 _, h, hpEtale, presheaf_etale_id B S hS V, hpSurj,
      by simpa only [schemeSpace, Category.comp_id] using hh, hscheme⟩

/-- Unramifiedness of a morphism of algebraic spaces over `S` is local on the target for the
fpqc topology. -/
@[stacks 042A]
public instance isUnramified_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        IsUnramified B S hS f.hom)
      (Topology.fpqc.precoverage.{u, v} B S hS) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) := fun {_ _} f =>
    IsUnramified B S hS f.hom
  let : P.IsStableUnderBaseChange :=
    isUnramified_isStableUnderBaseChange B S hS
  let : P.RespectsIso := inferInstance
  refine { pullbackSnd := ?_, of_forall_pullbackSnd := ?_ }
  · intro X Y f R U g hR hg hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := P) (IsPullback.of_hasPullback f g) hf
  · intro X Y f R hR h
    obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
    obtain ⟨hY, hYi, hfpqc⟩ := hcover
    change IsFpqcCovering B S hS (fun i => (gi i).hom) at hfpqc
    apply unramified_of_affine_baseChanges B S hS f
    intro T gT
    obtain ⟨U, hfinite, hUcover, href⟩ := hfpqc.2 T gT.hom
    let fT := pullback.snd f gT
    apply unramified_of_affineFpqcPresieve B S hS T
      U.presieve₀ hUcover (pullback f gT) fT
    intro T' k hk
    rcases hk with ⟨j⟩
    obtain ⟨i, a, ha⟩ := href j
    let a' : schemeSpace
        ((BigAffineFppf.inclusion B S hS).obj (U.X j)) ⟶ Yi i :=
      ObjectProperty.homMk a
    let k' := schemeSpaceMap
      ((BigAffineFppf.inclusion B S hS).map (U.f j))
    have hcomm : a' ≫ gi i = k' ≫ gT := ObjectProperty.hom_ext _ ha
    have hgi : P (pullback.snd f (gi i)) :=
      h (g := gi i) (Presieve.ofArrows.mk i)
    exact MorphismProperty.pullbackSnd_of_comm P f (gi i) gT a' k' hcomm hgi

/-- Let `{gᵢ : Yᵢ ⟶ Y}` be an fpqc covering of algebraic spaces over `S`, indexed by a type `I`
in any universe, and `f : X ⟶ Y` a morphism of algebraic spaces over `S`. Then `f` is unramified
if and only if every base change `pullback.snd f (g i) : Yᵢ ×_Y X ⟶ Yᵢ` of `f` is unramified. -/
@[stacks 042A "Definition 03YH unfolded: f unramified iff every Yᵢ ×_Y X → Yᵢ is"]
theorem isUnramified_iff_forall_pullbackSnd_of_isFpqcCovering
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {I : Type v} {X Y : AlgebraicSpaces B S hS} {Yi : I → AlgebraicSpaces B S hS}
    (g : ∀ i, Yi i ⟶ Y) (hg : IsFpqcCovering B S hS (fun i => (g i).hom)) (f : X ⟶ Y) :
    IsUnramified B S hS f.hom ↔ ∀ i, IsUnramified B S hS (pullback.snd f (g i)).hom := by
  have hR : Presieve.ofArrows Yi g ∈ Topology.fpqc.precoverage.{u, v} B S hS Y :=
    ⟨I, Yi, g, rfl, Y.property, fun i => (Yi i).property, hg⟩
  rw [MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsUnramified B S hS f.hom) hR]
  refine ⟨fun h i => h (g i) (Presieve.ofArrows.mk i), fun h U g' _ hg' => ?_⟩
  rcases hg' with ⟨i⟩
  exact h i

end AlgebraicGeometry.Space

end
