module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Affine
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of quasi-compact and quasi-separated schemes
with affine transition morphisms. If a morphism over one stage is locally of finite type and
becomes finite after base change to the limit, then it is already finite after base change to some
later stage.

## Main results

* `AlgebraicGeometry.exists_isFinite_baseChange_of_isLimit` descends finiteness of a morphism from
  the inverse limit to a finite stage.

## Implementation notes

The indexing category for descent is essentially small relative to the scheme universe,
expressing the set-sized inverse systems in the source.

Schemes over the chosen stage are represented by objects of its over category, and base change is
`CategoryTheory.Over.pullback`. A morphism `i ⟶ i₀` represents a stage later than `i₀` in the
cofiltered indexing category. This generalizes the directed indexing set in the source.

Since a finite morphism is affine, the descent of affineness reduces the statement to a morphism
which is already affine over the chosen stage; an affine open covering of its target then reduces
it further to a morphism of affine schemes. There the global sections of the stages form a
filtered colimit of rings, each stage map is of finite type with generators coming from one stage,
and finiteness of a ring map descends along such a colimit.

Finiteness is the affine-target property that the source is affine and the induced map of global
sections is a finite ring map. The two consequences of this description used below are that
finiteness is local at the target, and that over an affine target it is exactly that conjunction.

## References

* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-! ### Finiteness as an affine-target property -/

/-- A morphism of schemes is finite exactly when it is affine and, over every affine open of the
target, the induced map of sections is a finite ring map. -/
private lemma hasAffineProperty_isFinite :
    HasAffineProperty (@IsFinite) (affineAnd RingHom.Finite) :=
  (HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
      RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan).mpr
    (fun f ↦ by simp [isFinite_iff])

/-- Finiteness of a morphism of schemes is local at the target. -/
@[ega "II 6.3.10"]
public lemma isZariskiLocalAtTarget_isFinite :
    IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasAffineProperty_isFinite

/-- A morphism with affine target is finite exactly when its source is affine and its map of
global sections is a finite ring map. -/
private lemma isFinite_iff_finite_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    IsFinite f ↔ IsAffine X ∧ RingHom.Finite f.appTop.hom :=
  have := hasAffineProperty_isFinite
  HasAffineProperty.iff_of_isAffine (P := (@IsFinite : MorphismProperty Scheme.{u}))

/-- A morphism of affine schemes whose map of global sections is finite is finite. -/
private lemma isFinite_of_finite_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    (hf : RingHom.Finite f.appTop.hom) : IsFinite f :=
  (isFinite_iff_finite_appTop f).mpr ⟨inferInstance, hf⟩

/-! ### Finiteness in a directed colimit of rings -/

/-- A diagram of rings over a directed preorder, together with a compatible family of maps to a
ring whose elements all come from a stage and whose vanishing is detected at a later stage, is a
directed colimit. -/
private lemma isDirectedColimit_of_maps {α : Type u} [PartialOrder α] [IsDirected α (· ≤ ·)]
    [Nonempty α] (F : α ⥤ CommRingCat.{u}) (R : CommRingCat.{u}) (p : ∀ a, F.obj a ⟶ R)
    (hp : ∀ {a b : α} (h : a ≤ b), F.map (homOfLE h) ≫ p b = p a)
    (hsurj : ∀ z : R, ∃ (a : α) (x : F.obj a), (p a).hom x = z)
    (hzero : ∀ (a : α) (x : F.obj a), (p a).hom x = 0 →
      ∃ (b : α) (h : a ≤ b), (F.map (homOfLE h)).hom x = 0) :
    IsDirectedColimit (R := ℤ) (fun a ↦ (F.obj a : Type u))
      (fun _ _ h ↦ (F.map (homOfLE h)).hom.toIntAlgHom) (R : Type u)
      (fun a ↦ (p a).hom.toIntAlgHom) := by
  refine ⟨?_, ?_, ?_, hsurj, hzero⟩
  · intro i j k hij hjk x
    show (F.map (homOfLE hjk)).hom ((F.map (homOfLE hij)).hom x) = (F.map (homOfLE _)).hom x
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, homOfLE_comp]
  · intro a x
    show (F.map (homOfLE le_rfl)).hom x = x
    simp
  · intro i j hij x
    show (p j).hom ((F.map (homOfLE hij)).hom x) = (p i).hom x
    rw [← ConcreteCategory.comp_apply, hp hij]

/-- Finiteness descends along a filtered colimit of diagrams of rings: a morphism of diagrams of
rings over a directed preorder whose colimit map is finite, whose stage maps are of finite type,
and which has a finite generating family at one stage whose images generate at every later stage,
is finite at some stage.

This is the form in which the finiteness descent of Tag 07RG, which is proved for a directed
colimit of algebras, is applied to the diagrams of global sections of the stages. -/
private lemma exists_finite_app_of_maps {α : Type u} [PartialOrder α] [IsDirected α (· ≤ ·)]
    [Nonempty α] (F G : α ⥤ CommRingCat.{u}) (η : F ⟶ G) (RF RG : CommRingCat.{u})
    (pF : ∀ a, F.obj a ⟶ RF) (pG : ∀ a, G.obj a ⟶ RG) (φ : RF ⟶ RG)
    (hpF : ∀ {a b : α} (h : a ≤ b), F.map (homOfLE h) ≫ pF b = pF a)
    (hpG : ∀ {a b : α} (h : a ≤ b), G.map (homOfLE h) ≫ pG b = pG a)
    (hsurjF : ∀ z : RF, ∃ (a : α) (x : F.obj a), (pF a).hom x = z)
    (hzeroF : ∀ (a : α) (x : F.obj a), (pF a).hom x = 0 →
      ∃ (b : α) (h : a ≤ b), (F.map (homOfLE h)).hom x = 0)
    (hsurjG : ∀ z : RG, ∃ (a : α) (x : G.obj a), (pG a).hom x = z)
    (hzeroG : ∀ (a : α) (x : G.obj a), (pG a).hom x = 0 →
      ∃ (b : α) (h : a ≤ b), (G.map (homOfLE h)).hom x = 0)
    (hcompat : ∀ a, η.app a ≫ pG a = pF a ≫ φ)
    (hφ : φ.hom.Finite) (hft : ∀ a, (η.app a).hom.FiniteType)
    (a₀ : α) (gen : Finset (G.obj a₀))
    (hgen : ∀ (a : α) (h : a₀ ≤ a),
      letI := (η.app a).hom.toAlgebra
      Algebra.adjoin (F.obj a) ((G.map (homOfLE h)).hom '' (gen : Set (G.obj a₀))) = ⊤) :
    ∃ a, (η.app a).hom.Finite :=
  Stacks.DirectLimit.FiniteDescent.finite_descend_of_colimit
    (isDirectedColimit_of_maps F RF pF hpF hsurjF hzeroF)
    (isDirectedColimit_of_maps G RG pG hpG hsurjG hzeroG)
    (fun a ↦ (η.app a).hom.toIntAlgHom) φ.hom.toIntAlgHom
    (by
      intro i j hij x
      show (η.app j).hom ((F.map (homOfLE hij)).hom x) =
        (G.map (homOfLE hij)).hom ((η.app i).hom x)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, η.naturality])
    (by
      intro a x
      show φ.hom ((pF a).hom x) = (pG a).hom ((η.app a).hom x)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hcompat a])
    hft hφ a₀ gen hgen

/-- Finiteness descends along filtered colimits of rings: a morphism of diagrams of rings over a
directed preorder whose colimit map is finite, whose stage maps are of finite type, and whose
naturality squares are pushouts, is finite at some stage. -/
private lemma exists_finite_app_of_isColimit {α : Type u} [PartialOrder α] [IsDirected α (· ≤ ·)]
    [Nonempty α] (F G : α ⥤ CommRingCat.{u}) (η : F ⟶ G) (rF : Cocone F) (rG : Cocone G)
    (hrF : IsColimit rF) (hrG : IsColimit rG) (φ : rF.pt ⟶ rG.pt)
    (hcompat : ∀ a, η.app a ≫ rG.ι.app a = rF.ι.app a ≫ φ)
    (hφ : φ.hom.Finite) (hft : ∀ a, (η.app a).hom.FiniteType)
    (hpush : ∀ (a b : α) (h : a ≤ b),
      IsPushout (F.map (homOfLE h)) (η.app a) (η.app b) (G.map (homOfLE h))) :
    ∃ a, (η.app a).hom.Finite := by
  obtain ⟨a₀⟩ : Nonempty α := inferInstance
  let : Algebra (F.obj a₀) (G.obj a₀) := (η.app a₀).hom.toAlgebra
  have hFT : Algebra.FiniteType (F.obj a₀) (G.obj a₀) := hft a₀
  obtain ⟨gen, hgen₀⟩ := hFT.out
  have hgen : ∀ (a : α) (h : a₀ ≤ a),
      let := (η.app a).hom.toAlgebra
      Algebra.adjoin (F.obj a) ((G.map (homOfLE h)).hom '' (gen : Set (G.obj a₀))) = ⊤ :=
    fun a h ↦ adjoin_image_eq_top_of_isPushout (hpush a₀ a h).flip gen hgen₀
  exact exists_finite_app_of_maps F G η rF.pt rG.pt (fun a ↦ rF.ι.app a)
    (fun a ↦ rG.ι.app a) φ (fun h ↦ rF.w (homOfLE h)) (fun h ↦ rG.w (homOfLE h))
    (ring_colimit_surjective F rF hrF) (ring_colimit_eventually_zero F rF hrF)
    (ring_colimit_surjective G rG hrG) (ring_colimit_eventually_zero G rG hrG)
    hcompat hφ hft a₀ gen hgen

/-! ### The affine case -/

/-- The base change of a morphism locally of finite type, along a map making both base changes
affine, induces a ring map of finite type on global sections. -/
private lemma finiteType_appTop_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S) {X Y : Over S}
    (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    [IsAffine (pullback g X.hom)] [IsAffine (pullback g Y.hom)] :
    (baseChangeMap g X Y f).appTop.hom.FiniteType := by
  have : LocallyOfFiniteType (baseChangeMap g X Y f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (baseChangeMap_isPullback g X Y f).flip inferInstance
  simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
    (baseChangeMap g X Y f).finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)

/-- A morphism of affine schemes over a stage which is locally of finite type and becomes finite
over the limit is finite at some later stage. -/
private lemma exists_isFinite_affine_baseChange {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X Y : Over (D.obj i₀)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left]
    [IsFinite ((Over.pullback (c.π.app i₀)).map f).left] :
    ∃ A : Over i₀, IsFinite ((Over.pullback (D.map A.hom)).map f).left := by
  classical
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨α, _, _, _, e, he⟩ := exists_directed_cofinal_over (I := I) i₀
  let FX := baseChangeDiagram D i₀ X
  let FY := baseChangeDiagram D i₀ Y
  let cX : Cone FX := baseChangeCone D c i₀ X
  let cY : Cone FY := baseChangeCone D c i₀ Y
  have hA (Z : Over (D.obj i₀)) [IsAffine Z.left] (A : Over i₀) :
      IsAffine ((baseChangeDiagram D i₀ Z).obj A) := isAffine_baseChangeDiagram_obj D i₀ Z A
  have (Z : Over (D.obj i₀)) [IsAffine Z.left] (A : Over i₀) :
      IsAffine (pullback (D.map A.hom) Z.hom) := hA Z A
  have (Z : Over (D.obj i₀)) [IsAffine Z.left] (A : (Over i₀)ᵒᵖ) :
      IsAffine ((baseChangeDiagram D i₀ Z).op.obj A).unop := hA Z A.unop
  have (Z : Over (D.obj i₀)) [IsAffine Z.left] (a : αᵒᵖ) :
      IsAffine ((e.leftOp ⋙ baseChangeDiagram D i₀ Z).obj a) := hA Z _
  -- The diagrams of global sections over a directed cofinal reindexing of the later stages.
  let F : α ⥤ CommRingCat.{u} := e ⋙ FY.op ⋙ Scheme.Γ
  let G : α ⥤ CommRingCat.{u} := e ⋙ FX.op ⋙ Scheme.Γ
  let η : F ⟶ G := Functor.whiskerLeft e
    (Functor.whiskerRight (NatTrans.op (baseChangeDiagramMap D i₀ f)) Scheme.Γ)
  let rF : Cocone F := (Scheme.Γ.mapCocone cY.op).whisker e
  let rG : Cocone G := (Scheme.Γ.mapCocone cX.op).whisker e
  let φ : rF.pt ⟶ rG.pt := (baseChangeMap (c.π.app i₀) X Y f).appTop
  -- The sections at the limit are the filtered colimit of the sections at the stages.
  have hr (Z : Over (D.obj i₀)) [IsAffine Z.left] :
      IsColimit ((Scheme.Γ.mapCocone (baseChangeCone D c i₀ Z).op).whisker e) :=
    (Functor.Final.isColimitWhiskerEquiv e _).symm
      (Classical.choice (nonempty_isColimit_sections_baseChange D c hc i₀ Z))
  have hrF : IsColimit rF := hr Y
  have hrG : IsColimit rG := hr X
  -- The colimit map is the map of sections of the base change to the limit.
  have hcompat : ∀ a, η.app a ≫ rG.ι.app a = rF.ι.app a ≫ φ := fun a ↦
    congrArg (fun q : cX.pt ⟶ FY.obj (e.obj a).unop => q.appTop)
      (baseChangeCone_π_isPullback D i₀ f c (e.obj a).unop).w
  have hlim (Z : Over (D.obj i₀)) [IsAffine Z.left] : IsAffine (pullback (c.π.app i₀) Z.hom) :=
    Scheme.isAffine_of_isLimit ((baseChangeCone D c i₀ Z).whisker e.leftOp)
      ((Functor.Initial.isLimitWhiskerEquiv e.leftOp _).symm (baseChangeConeIsLimit D hc i₀ Z))
  have := hlim X
  have := hlim Y
  have hφ : φ.hom.Finite := ((isFinite_iff_finite_appTop _).mp
    ((baseChangeMap_prop_iff (@IsFinite) (c.π.app i₀) X Y f).2 inferInstance)).2
  -- Each stage map is of finite type, and generators at one stage generate at all later stages.
  have hpush (a b : α) (h : a ≤ b) :
      IsPushout (F.map (homOfLE h)) (η.app a) (η.app b) (G.map (homOfLE h)) :=
    isPushout_appTop_of_isPullback (baseChangeTransition_isPullback (D.map (e.obj a).unop.hom)
      (D.map (e.obj b).unop.hom) (D.map (e.map (homOfLE h)).unop.left)
      (by rw [← D.map_comp, (e.map (homOfLE h)).unop.w]) X Y f)
  obtain ⟨a, ha⟩ := exists_finite_app_of_isColimit F G η rF rG hrF hrG φ hcompat hφ
    (fun a ↦ finiteType_appTop_baseChangeMap (D.map (e.obj a).unop.hom) f) hpush
  let A : Over i₀ := (e.obj a).unop
  exact ⟨A, (baseChangeMap_prop_iff (@IsFinite) (D.map A.hom) X Y f).1
    (isFinite_of_finite_appTop _ ha)⟩

/-! ### Reduction to the affine case -/

/-- A morphism whose base change is finite over each member of an open cover of the target of the
base change has finite base change. -/
private lemma isFinite_of_baseChange_cover {S T : Scheme.{u}} (p : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) (U : Y.left.OpenCover) (XU : U.I₀ → Over S)
    (fu : ∀ k, XU k ⟶ Over.mk (U.f k ≫ Y.hom)) (vx : ∀ k, XU k ⟶ X)
    (hOver : ∀ k, IsPullback (vx k) (fu k) f (Over.homMk (U.f k)))
    (H : ∀ k, IsFinite ((Over.pullback p).map (fu k)).left) :
    IsFinite ((Over.pullback p).map f).left := by
  have := isZariskiLocalAtTarget_isFinite.{u}
  let vy (k) : Over.mk (U.f k ≫ Y.hom) ⟶ Y := Over.homMk (U.f k)
  let Up : ((Over.pullback p).obj Y).left.OpenCover :=
    { I₀ := U.I₀
      X := fun k => ((Over.pullback p).obj (Over.mk (U.f k ≫ Y.hom))).left
      f := fun k => ((Over.pullback p).map (vy k)).left
      mem₀ := Precoverage.mem_coverings_of_isPullback U.f U.mem₀ (pullback.fst Y.hom p)
        (fun k => ((Over.pullback p).map (vy k)).left)
        (fun k => pullback.fst (U.f k ≫ Y.hom) p)
        (fun k => (overPullback_isPullback p (Over.mk (U.f k ≫ Y.hom)) Y (vy k)).flip) }
  apply IsZariskiLocalAtTarget.of_openCover (P := (@IsFinite : MorphismProperty Scheme.{u})) Up
  intro k
  have hp := (hOver k).map (Over.pullback p ⋙ Over.forget _)
  change IsPullback ((Over.pullback p).map (vx k)).left ((Over.pullback p).map (fu k)).left
    ((Over.pullback p).map f).left ((Over.pullback p).map (vy k)).left at hp
  show IsFinite (pullback.snd ((Over.pullback p).map f).left
    ((Over.pullback p).map (vy k)).left)
  rw [← hp.isoPullback_inv_snd]
  have := H k
  infer_instance

/-- If a morphism over a stage is affine and locally of finite type and becomes finite over the
limit, it is finite at some later stage. -/
private lemma exists_isFinite_of_isAffineHom {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (X Y : Over (D.obj i₀)) (f : X ⟶ Y)
    [CompactSpace Y.left] [IsAffineHom f.left] [LocallyOfFiniteType f.left]
    [IsFinite ((Over.pullback (c.π.app i₀)).map f).left] :
    ∃ A : Over i₀, IsFinite ((Over.pullback (D.map A.hom)).map f).left := by
  classical
  let U := Y.left.affineCover.finiteSubcover
  have (k : U.I₀) : IsAffine (U.X k) := by
    dsimp [U, Scheme.OpenCover.finiteSubcover]
    infer_instance
  let XU (k : U.I₀) : Over (D.obj i₀) := Over.mk (pullback.fst f.left (U.f k) ≫ X.hom)
  let YU (k : U.I₀) : Over (D.obj i₀) := Over.mk (U.f k ≫ Y.hom)
  let fu (k : U.I₀) : XU k ⟶ YU k := Over.homMk (pullback.snd f.left (U.f k)) (by
    dsimp [XU, YU]
    rw [← Category.assoc, ← pullback.condition, Category.assoc, f.w])
  let vx (k : U.I₀) : XU k ⟶ X := Over.homMk (pullback.fst f.left (U.f k))
  let vy (k : U.I₀) : YU k ⟶ Y := Over.homMk (U.f k)
  have hpb (k : U.I₀) : IsPullback (vx k).left (fu k).left f.left (vy k).left :=
    IsPullback.of_hasPullback _ _
  have hOver (k : U.I₀) : IsPullback (vx k) (fu k) f (vy k) :=
    IsPullback.of_map_of_faithful (Over.forget _) (hpb k)
  have hstage (k : U.I₀) : ∃ A : Over i₀,
      IsFinite ((Over.pullback (D.map A.hom)).map (fu k)).left := by
    have : IsAffine (YU k).left := by change IsAffine (U.X k); infer_instance
    have : IsAffine (XU k).left := IsAffine.of_isPullback (hpb k).flip
    have : LocallyOfFiniteType (fu k).left := by
      show LocallyOfFiniteType (pullback.snd f.left (U.f k))
      infer_instance
    have : IsFinite ((Over.pullback (c.π.app i₀)).map (fu k)).left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        ((hOver k).map (Over.pullback (c.π.app i₀) ⋙ Over.forget _))
        (show IsFinite ((Over.pullback (c.π.app i₀)).map f).left from inferInstance)
    exact exists_isFinite_affine_baseChange D c hc i₀ (XU k) (YU k) (fu k)
  obtain ⟨k₁, g₁, hg₁⟩ := common_stage_of_finite_prop (@IsFinite) D i₀ XU YU fu
    (fun k ↦ by
      obtain ⟨A, hA⟩ := hstage k
      exact ⟨A.left, A.hom, hA⟩)
  exact ⟨Over.mk g₁, isFinite_of_baseChange_cover (D.map g₁) f U XU fu vx hOver hg₁⟩

/-! ### Descending finiteness -/

/-- **Stacks Project, Tag 01ZO.** If a morphism over a stage of a cofiltered inverse system is
locally of finite type and its base change to the limit is finite, then its base change to some
later stage is finite. -/
@[stacks 01ZO]
theorem exists_isFinite_baseChange_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsFinite ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (hi : i ⟶ i₀), IsFinite ((Over.pullback (D.map hi)).map f₀).left := by
  classical
  obtain ⟨i₁, hi₁, hAffine⟩ := exists_isAffineHom_of_isLimit D c hc i₀ X₀ Y₀ f₀
  let X₁ := (Over.pullback (D.map hi₁)).obj X₀
  let Y₁ := (Over.pullback (D.map hi₁)).obj Y₀
  let f₁ : X₁ ⟶ Y₁ := (Over.pullback (D.map hi₁)).map f₀
  have : IsAffineHom f₁.left := hAffine
  have : CompactSpace Y₁.left := by
    show CompactSpace ↥(pullback Y₀.hom (D.map hi₁))
    infer_instance
  have : LocallyOfFiniteType f₁.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) (D.map hi₁) f₀ inferInstance
  have : IsFinite ((Over.pullback (c.π.app i₁)).map f₁).left := by
    apply (overPullback_map_comp_iff (@IsFinite) (D.map hi₁) (c.π.app i₁) f₀).mp
    rw [c.w hi₁]
    infer_instance
  obtain ⟨A, hA⟩ := exists_isFinite_of_isAffineHom D c hc i₁ X₁ Y₁ f₁
  refine ⟨A.left, A.hom ≫ hi₁, ?_⟩
  rw [D.map_comp]
  exact (overPullback_map_comp_iff (@IsFinite) (D.map hi₁) (D.map A.hom) f₀).mpr hA

end AlgebraicGeometry
