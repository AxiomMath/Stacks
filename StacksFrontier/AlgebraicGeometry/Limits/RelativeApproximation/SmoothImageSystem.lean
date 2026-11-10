module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystemModels
public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemLimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Smooth morphisms descend to the image systems of good diagrams

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let `f : X ⟶ Y` be a smooth morphism of schemes quasi-separated and of
finite type over `S`. For good diagrams of `X ⟶ S` and `Y ⟶ S`, every sufficiently late stage map
of a morphism of their systems of scheme-theoretic images is smooth.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.eventually_smooth_morphismAt`: the stage maps of the
  morphism of image systems induced by a smooth morphism are eventually smooth.

## Implementation notes

The stage maps are the components of a morphism of image systems on a common tail. The assertion
applies to every such morphism inducing the given map on the limits.

Smoothness is descended through the base-change description of a cartesian transition square: the
stage map is the base change along the projection from the limit of the morphism of slices over
the image at that stage, and smoothness of a base change is reflected and preserved there.

The index preorder may live in any universe, but it is assumed small relative to the universe of
the schemes, which is what descending smoothness to a finite stage requires: for an index category
larger than that universe the limit need not be computed by the filtered colimits of coordinate
rings the argument uses. Tag 0C0C, which the proof consumes, is stated for an index category in
the universe of the schemes, so it is applied in a model of the index of the image system that
lives in that universe.

The index is assumed nonempty because that is part of the directed set of Tag 0CNM, carried by
`AlgebraicGeometry.LimitNoetherianSituation`: the type of the situation, of its good diagrams and
of a morphism of their image systems is only defined for a nonempty index. The assumption costs no
generality here, since the stage `i₀` is an explicit argument and already exhibits an element.

## References

* [Stacks Project, Tag 0CNU](https://stacks.math.columbia.edu/tag/0CNU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

private lemma smooth_overPullback_of_isPullback
    {X Y A B : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ A) (b : Y ⟶ B)
    (c : A ⟶ B) (h : IsPullback f a b c) :
    Smooth ((Over.pullback b).map
      (Over.homMk (U := Over.mk c) (V := Over.mk (𝟙 B)) c)).left ↔ Smooth f := by
  let eX := h.isoPullback ≪≫ pullbackSymmetry b c
  have hY : IsPullback (𝟙 Y) b b (𝟙 B) := IsPullback.of_id_fst
  let eY := hY.isoPullback ≪≫ pullbackSymmetry b (𝟙 B)
  let m : pullback c b ⟶ pullback (𝟙 B) b :=
    pullback.lift (pullback.fst c b ≫ c) (pullback.snd c b) (by
      simp only [Category.comp_id, pullback.condition])
  have hXfst : eX.hom ≫ pullback.fst c b = a := by simp [eX]
  have hXsnd : eX.hom ≫ pullback.snd c b = f := by simp [eX]
  have hYfst : eY.hom ≫ pullback.fst (𝟙 B) b = b := by simp [eY]
  have hYsnd : eY.hom ≫ pullback.snd (𝟙 B) b = 𝟙 Y := by simp [eY]
  have hcomm : eX.hom ≫ m = f ≫ eY.hom := by
    apply pullback.hom_ext <;> dsimp [m] <;>
      simp [reassoc_of% hXfst, hXsnd, hYfst, hYsnd, h.w]
  have : MorphismProperty.RespectsIso (@Smooth) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  simpa [Over.pullback, Over.homMk, Over.mk, m] using
    (MorphismProperty.arrow_mk_iso_iff (@Smooth) (Arrow.isoMk eX eY hcomm) :
      Smooth f ↔ Smooth m).symm

/-! ### A small model for the index of an image system -/

/-- The tail of a preorder above a given element. -/
private abbrev IndexTail (P : Type v) [Preorder P] (i : P) := {j : P // i ≤ j}

private instance {P : Type v} [Preorder P] (i : P) : Nonempty (IndexTail P i) := ⟨⟨i, le_rfl⟩⟩

private instance {P : Type v} [Preorder P] [IsDirected P (· ≤ ·)] (i : P) :
    IsDirected (IndexTail P i) (· ≤ ·) where
  directed a b := by
    obtain ⟨m, ham, hbm⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨m, a.2.trans ham⟩, ham, hbm⟩

private instance {P : Type v} [Preorder P] [IsDirected P (· ≤ ·)] [Small.{u} P] (i : P) :
    IsDirected (Shrink.{u} (IndexTail P i)) (· ≤ ·) where
  directed a b := by
    let eT := orderIsoShrink.{u} (IndexTail P i)
    obtain ⟨m, ha, hb⟩ := directed_of (· ≤ ·) (eT.symm a) (eT.symm b)
    exact ⟨eT m, by simpa using eT.monotone ha, by simpa using eT.monotone hb⟩

/-- The opposite of a tail of a preorder is the category of objects over the corresponding
object. -/
private noncomputable def indexTailOverEquiv {P : Type v} [Preorder P] (i : P) :
    (IndexTail P i)ᵒᵖ ≌ Over (op i) where
  functor :=
    { obj := fun j => Over.mk ((homOfLE j.unop.2).op)
      map := fun {j k} a => Over.homMk ((homOfLE (leOfHom a.unop)).op)
      map_id _ := Over.OverMorphism.ext (Subsingleton.elim _ _)
      map_comp _ _ := Over.OverMorphism.ext (Subsingleton.elim _ _) }
  inverse :=
    { obj := fun A => op ⟨A.left.unop, leOfHom A.hom.unop⟩
      map := fun {A B} a => (homOfLE (leOfHom a.left.unop)).op
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }
  unitIso := NatIso.ofComponents (fun j => eqToIso (by cases j; rfl))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun A => Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))
    (fun _ => rfl)

/-- A model, in the universe of the schemes, of the category of objects over `op i` in a preorder
whose underlying type is small relative to that universe. -/
private noncomputable def shrinkTailOverEquiv {P : Type v} [Preorder P] [Small.{u} P] (i : P) :
    (Shrink.{u} (IndexTail P i))ᵒᵖ ≌ Over (op i) :=
  ((orderIsoShrink.{u} (IndexTail P i)).symm.equivalence.op).trans (indexTailOverEquiv i)

/-- Tag 0C0C for an index category that admits a model in the universe of the schemes: a morphism
over one stage which becomes smooth over the limit is smooth after base change to some later
stage. The hypotheses that Tag 0C0C takes as instances are explicit here, because at the point of
use they are available only for the given stage and not for its counterpart in the model. -/
private lemma exists_smooth_baseChange_of_smooth_limitBaseChange_of_equiv
    {K : Type v} [Category.{v} K] {K' : Type u} [Category.{u} K']
    (E : K' ≌ K) [IsCofiltered K'] (Dg : K ⥤ Scheme.{u}) (c : Cone Dg) (hc : IsLimit c)
    (k₀ : K') (i₀ : K) (hk₀ : E.functor.obj k₀ = i₀)
    (X₀ Y₀ : Over (Dg.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    (haff : ∀ {a b : K} (g : a ⟶ b), IsAffineHom (Dg.map g))
    (hcpt : CompactSpace (Dg.obj i₀)) (hqs : QuasiSeparatedSpace (Dg.obj i₀))
    (hcptX : CompactSpace X₀.left) (hqsX : QuasiSeparatedSpace X₀.left)
    (hcptY : CompactSpace Y₀.left) (hqsY : QuasiSeparatedSpace Y₀.left)
    (hfp : LocallyOfFinitePresentation f₀.left)
    (hsm : Smooth ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (a : K) (g : a ⟶ i₀), Smooth ((Over.pullback (Dg.map g)).map f₀).left := by
  subst hk₀
  have haff' : ∀ {a b : K'} (g : a ⟶ b), IsAffineHom ((E.functor ⋙ Dg).map g) :=
    fun _ => haff _
  have hcpt' : CompactSpace ((E.functor ⋙ Dg).obj k₀) := hcpt
  have hqs' : QuasiSeparatedSpace ((E.functor ⋙ Dg).obj k₀) := hqs
  have hsm' : Smooth ((Over.pullback ((c.whisker E.functor).π.app k₀)).map f₀).left := hsm
  obtain ⟨a, g, hg⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange
    (E.functor ⋙ Dg) (c.whisker E.functor) k₀ X₀ Y₀ f₀ (hc.whiskerEquivalence E)
  exact ⟨E.functor.obj a, E.functor.map g, hg⟩

private lemma stageImage_isNoetherian
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} {p : X ⟶ D.limitScheme} (G : GoodDiagram D p)
    (j : Over (op G.index)) :
    IsNoetherian (GoodDiagram.stageMap G j).image := by
  let m := GoodDiagram.stageMap G j
  let q := pullback.fst (D.system.map j.hom) G.modelMap
  let b := m.imageι ≫ q
  have : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  have : QuasiCompact G.modelMap := G.quasiCompact
  have : IsNoetherian (D.system.obj j.left) := D.noetherian (unop j.left)
  exact { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian b
          toCompactSpace := QuasiCompact.compactSpace_of_compactSpace b }

private lemma morphismAt_locallyOfFinitePresentation
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D (X := X) (Y := Y) (pX := pX) (pY := pY) f GX GY i₀ hX hY)
    (j : Over (op i₀)) :
    LocallyOfFinitePresentation (F.maps.app j) := by
  let jX := (Over.map ((homOfLE hX).op)).obj j
  let jY := (Over.map ((homOfLE hY).op)).obj j
  let mX := GoodDiagram.stageMap GX jX
  let mY := GoodDiagram.stageMap GY jY
  let qX := pullback.fst (D.system.map jX.hom) GX.modelMap
  let qY := pullback.fst (D.system.map jY.hom) GY.modelMap
  let bX := mX.imageι ≫ qX
  let bY := mY.imageι ≫ qY
  let f₀ := F.maps.app j
  have : LocallyOfFiniteType GX.modelMap := GX.locallyOfFiniteType
  have : LocallyOfFiniteType GY.modelMap := GY.locallyOfFiniteType
  have hcomp : LocallyOfFiniteType (f₀ ≫ bY) := by
    rw [show f₀ ≫ bY = bX from F.over_base j]
    infer_instance
  have : LocallyOfFiniteType f₀ := locallyOfFiniteType_of_comp f₀ bY
  have : IsNoetherian
      ((Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY).obj j) :=
    stageImage_isNoetherian D GY jY
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

private lemma stageTargetMap_isAffineHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} {p : X ⟶ D.limitScheme} (G : GoodDiagram D p)
    {j k : Over (op G.index)} (a : j ⟶ k) :
    IsAffineHom (GoodDiagram.stageTargetMap G a) := by
  have hcomp : D.system.map a.left ≫ D.system.map k.hom = D.system.map j.hom := by
    rw [← D.system.map_comp, Over.w a]
  have hpull : IsPullback (GoodDiagram.stageTargetMap G a)
      (pullback.fst (D.system.map j.hom) G.modelMap)
      (pullback.fst (D.system.map k.hom) G.modelMap) (D.system.map a.left) :=
    IsPullback.of_right
      (by
        rw [GoodDiagram.stageTargetMap, pullback.lift_snd, hcomp]
        exact (IsPullback.of_hasPullback _ _).flip)
      (by rw [GoodDiagram.stageTargetMap, pullback.lift_fst])
      (IsPullback.of_hasPullback _ _).flip
  exact MorphismProperty.of_isPullback hpull.flip (D.transition_affine a.left)

private lemma imageTransition_isAffineHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} {p : X ⟶ D.limitScheme} (G : GoodDiagram D p)
    {j k : Over (op G.index)} (a : j ⟶ k) :
    IsAffineHom ((GoodDiagram.imageSystem G).map a) := by
  change IsAffineHom (GoodDiagram.imageTransition G a)
  have := stageTargetMap_isAffineHom D G a
  have : IsAffineHom
      (GoodDiagram.imageTransition G a ≫ (GoodDiagram.stageMap G k).imageι) := by
    rw [GoodDiagram.imageTransition_imageι]
    infer_instance
  exact IsAffineHom.comp_iff.mp this

/-- Tag 0C0C for the image system of a good diagram, applied in a model of its index living in
the universe of the schemes. -/
private lemma exists_smooth_imageSystem_baseChange
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {Y : Scheme.{u}} {pY : Y ⟶ D.limitScheme}
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GY : GoodDiagram D pY) (j : Over (op GY.index))
    (X₀ Y₀ : Over ((GoodDiagram.imageSystem GY).obj j)) (f₀ : X₀ ⟶ Y₀)
    [IsNoetherian ((GoodDiagram.imageSystem GY).obj j)] [IsNoetherian X₀.left]
    [IsNoetherian Y₀.left] [LocallyOfFinitePresentation f₀.left]
    (hsm : Smooth ((Over.pullback ((GoodDiagram.imageCone GY).π.app j)).map f₀).left) :
    ∃ (k : Over (op GY.index)) (g : k ⟶ j),
      Smooth ((Over.pullback ((GoodDiagram.imageSystem GY).map g)).map f₀).left := by
  let eT := orderIsoShrink.{u} (IndexTail I GY.index)
  have : Nonempty (Shrink.{u} (IndexTail I GY.index)) := eT.symm.toEquiv.nonempty
  let E : (Shrink.{u} (IndexTail I GY.index))ᵒᵖ ≌ Over (op GY.index) :=
    shrinkTailOverEquiv GY.index
  let k₀ : (Shrink.{u} (IndexTail I GY.index))ᵒᵖ := op (eT ⟨unop j.left, leOfHom j.hom.unop⟩)
  have hk₀ : E.functor.obj k₀ = j :=
    congrArg (fun x : IndexTail I GY.index =>
      (Over.mk (homOfLE x.2).op : Over (op GY.index))) (eT.symm_apply_apply _)
  exact exists_smooth_baseChange_of_smooth_limitBaseChange_of_equiv E _ _
    (GoodDiagram.isLimit_imageCone D pY GY) k₀ j hk₀ X₀ Y₀ f₀
    (imageTransition_isAffineHom D GY) inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hsm

/-- The morphisms on the image systems of a smooth map become smooth at every
sufficiently late stage.

`Nonempty I` is not a weakening. The conclusion names a specific cofinal stage `i₃ ≥ i₀`,
which is exactly how Stacks 0CNU states it ("there exists an `i₃ ≥ i₀` such that for `i ≥ i₃`"),
and that phrasing presupposes the index `i₀`. The hypothesis is the source's own. -/
@[stacks 0CNU]
theorem eventually_smooth_morphismAt {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [Small.{u} I] [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Smooth f]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → Smooth (F.maps.app j) := by
  have : QuasiSeparated (f ≫ pY) := hf ▸ inferInstance
  have : QuasiSeparated f := QuasiSeparated.of_comp f pY
  have : QuasiCompact (f ≫ pY) := hf ▸ inferInstance
  have : QuasiCompact f := QuasiCompact.of_comp f pY
  have hfp : FinitePresentation f := FinitePresentation.mk inferInstance inferInstance inferInstance
  obtain ⟨i₃, hi₃, hpb⟩ :=
    eventually_isPullback_limit_morphismAt D f hf hfp GX GY i₀ hX hY F
  obtain ⟨i₄, hi₄, hcart⟩ :=
    eventually_isPullback_morphismAt D f hf hfp GX GY i₀ hX hY F
  obtain ⟨i₅, hi₃₅, hi₄₅⟩ := directed_of (· ≤ ·) i₃ i₄
  have hi₀₅ : i₀ ≤ i₅ := hi₃.trans hi₃₅
  let j₅ : Over (op i₀) := Over.mk ((homOfLE hi₀₅).op)
  have hj₅ : i₃ ≤ unop j₅.left := by simpa [j₅]
  let jY₅ := (Over.map ((homOfLE hY).op)).obj j₅
  let Dimg := GoodDiagram.imageSystem GY
  let cY : Cone Dimg := GoodDiagram.imageCone GY
  let X₀ : Over (Dimg.obj jY₅) := Over.mk (F.maps.app j₅)
  let Y₀ : Over (Dimg.obj jY₅) := Over.mk (𝟙 (Dimg.obj jY₅))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk (U := X₀) (V := Y₀) (F.maps.app j₅) (Category.comp_id _)
  have : IsNoetherian (X₀.left) := stageImage_isNoetherian D GX
    ((Over.map ((homOfLE hX).op)).obj j₅)
  have : IsNoetherian (Dimg.obj jY₅) := stageImage_isNoetherian D GY jY₅
  have : IsNoetherian (Y₀.left) := stageImage_isNoetherian D GY jY₅
  have : LocallyOfFinitePresentation f₀.left :=
    morphismAt_locallyOfFinitePresentation D f GX GY i₀ hX hY F j₅
  have hpb₅ : IsPullback f
      ((GoodDiagram.imageCone GX).π.app ((Over.map ((homOfLE hX).op)).obj j₅))
      (cY.π.app jY₅) (F.maps.app j₅) := by
    simpa [cY, jY₅] using hpb j₅ hj₅
  obtain ⟨k, g, hdesc⟩ := exists_smooth_imageSystem_baseChange D GY jY₅ X₀ Y₀ f₀
    ((smooth_overPullback_of_isPullback _ _ _ _ hpb₅).mpr inferInstance)
  have h5k : i₅ ≤ unop k.left := leOfHom g.left.unop
  have hi₀k : i₀ ≤ unop k.left := hi₀₅.trans h5k
  let jₖ : Over (op i₀) := Over.mk ((homOfLE hi₀k).op)
  let aₖ₅ : jₖ ⟶ j₅ := Over.homMk ((homOfLE h5k).op) (Subsingleton.elim _ _)
  have hi4k : i₄ ≤ unop k.left := hi₄₅.trans h5k
  have haₖ₅ : (Over.map ((homOfLE hY).op)).map aₖ₅ = g :=
    Over.OverMorphism.ext (Subsingleton.elim _ _)
  have hcartₖ₅' : IsPullback (F.maps.app jₖ)
      ((Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX).map aₖ₅)
      (Dimg.map g) (F.maps.app j₅) := by
    simpa [Dimg, haₖ₅] using hcart aₖ₅ (by simpa [jₖ] using hi4k) hi₄₅
  have hsmoothₖ : Smooth (F.maps.app jₖ) :=
    (smooth_overPullback_of_isPullback _ _ _ _ hcartₖ₅').mp (by simpa [f₀, X₀, Y₀] using hdesc)
  refine ⟨unop k.left, hi₀k, fun l hl => ?_⟩
  let aₗₖ : l ⟶ jₖ := Over.homMk ((homOfLE hl).op) (Subsingleton.elim _ _)
  exact MorphismProperty.of_isPullback (P := @Smooth) (hcart aₗₖ (hi4k.trans hl) hi4k).flip
    hsmoothₖ

end LimitNoetherianSituation

end AlgebraicGeometry

end
