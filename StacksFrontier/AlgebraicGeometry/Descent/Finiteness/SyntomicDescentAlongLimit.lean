module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.AffineLimitGlobalSections
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII

/-!
# Syntomic morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered inverse system of schemes with affine transition
morphisms.  A morphism over one stage which is locally of finite presentation and becomes
syntomic over the limit is already syntomic after base change to some later stage.

The reduction to the affine case is the one used for smoothness in
`StacksFrontier/AlgebraicGeometry/Limits/DescendingMorphisms/Smooth.lean`: syntomicity is local at
the source, stable under base change and composition, and holds for open immersions, so it may
be checked on finitely many affine charts, and finitely many charts can be moved to a common
stage.  Over affine source and target the base changes have coordinate rings forming a filtered
system of rings whose colimit is the coordinate ring of the base change to the limit — this is
the global-sections half of Mathlib's theory of cofiltered limits with affine transition
morphisms — and syntomicity of ring maps descends along such a system.

## Main results

* `AlgebraicGeometry.exists_syntomic_baseChange_of_syntomic_limitBaseChange` descends
  syntomicity from the inverse limit to a finite stage.

## Implementation notes

Schemes over the chosen stage and their base changes are represented by `CategoryTheory.Over`
and `CategoryTheory.Over.pullback`; a morphism `g : i ⟶ i₀` means that `i` is a later stage
than `i₀`.  The indexing category is taken in the universe of the schemes, as in Mathlib's
theory of cofiltered limits with affine transition morphisms, so that the filtered colimits of
affine coordinate rings used in the proof are computed on underlying sets.  A categorical limit
in `Scheme.{u}` indexed by a larger category need not have this property, and the conclusion
genuinely fails there.

## References

* [Stacks Project, Tag 0C3L](https://stacks.math.columbia.edu/tag/0C3L)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Syntomicity on affine charts -/

/-- Over affine base changes, syntomicity of the base change of a morphism is syntomicity of the
map of global section rings of the comparison morphism `baseChangeMap`. -/
private lemma syntomic_overPullback_iff_appTop_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [IsAffine (pullback g X.hom)] [IsAffine (pullback g Y.hom)] :
    Syntomic ((Over.pullback g).map f).left ↔ (baseChangeMap g X Y f).appTop.hom.Syntomic := by
  have : MorphismProperty.RespectsIso (@Syntomic : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← baseChangeMap_prop_iff (@Syntomic) g X Y f,
    HasRingHomProperty.iff_of_isAffine (P := @Syntomic)]

/-! ### Filtered systems of rings -/

/-- A functor out of a preorder into commutative rings is a directed system of rings. -/
private lemma directedSystem_of_functor {ι : Type*} [Preorder ι] (F : ι ⥤ CommRingCat.{u}) :
    DirectedSystem (fun i ↦ (F.obj i : Type u)) (fun _ _ h ↦ (F.map (homOfLE h)).hom) := by
  constructor
  · intro i x
    simp
  · intro k j i hij hjk x
    exact congrArg (fun f : F.obj i ⟶ F.obj k ↦ f.hom x)
      (by simpa using (F.map_comp (homOfLE hij) (homOfLE hjk)).symm)

/-- **Syntomicity descends along a directed system of rings.**  Given two filtered systems of
rings with cocones exhibiting them as the colimits of their stages, a map of systems whose
squares are pushouts and whose stages are of finite presentation is syntomic at some stage as
soon as the induced map of colimits is. -/
private lemma exists_stage_syntomic_of_cocones {α : Type*} [PartialOrder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] (A B : α ⥤ CommRingCat.{u}) (τ : A ⟶ B) (cA : Cocone A)
    (cB : Cocone B) (φ : cA.pt ⟶ cB.pt) (hφ : ∀ i, τ.app i ≫ cB.ι.app i = cA.ι.app i ≫ φ)
    (hAs : ∀ r : cA.pt, ∃ (i : α) (x : A.obj i), (cA.ι.app i).hom x = r)
    (hAz : ∀ (i : α) (x : A.obj i), (cA.ι.app i).hom x = 0 →
      ∃ (j : α) (h : i ≤ j), (A.map (homOfLE h)).hom x = 0)
    (hBs : ∀ r : cB.pt, ∃ (i : α) (x : B.obj i), (cB.ι.app i).hom x = r)
    (hBz : ∀ (i : α) (x : B.obj i), (cB.ι.app i).hom x = 0 →
      ∃ (j : α) (h : i ≤ j), (B.map (homOfLE h)).hom x = 0)
    (hfp : φ.hom.FinitePresentation) (hsyn : φ.hom.Syntomic)
    (hfpStage : ∀ i, (τ.app i).hom.FinitePresentation)
    (hpush : ∀ (i j : α) (h : i ≤ j),
      IsPushout (A.map (homOfLE h)) (τ.app i) (τ.app j) (B.map (homOfLE h))) :
    ∃ i, (τ.app i).hom.Syntomic := by
  let _ : Algebra cA.pt cB.pt := φ.hom.toAlgebra
  let _ (i : α) : Algebra (A.obj i) (B.obj i) := (τ.app i).hom.toAlgebra
  have : Algebra.FinitePresentation cA.pt cB.pt := hfp
  have : Algebra.Syntomic cA.pt cB.pt := hsyn
  have _ : DirectedSystem (fun i ↦ (A.obj i : Type u))
      (fun i j h ↦ (A.map (homOfLE h)).hom) := directedSystem_of_functor A
  have _ : DirectedSystem (fun i ↦ (B.obj i : Type u))
      (fun i j h ↦ (B.map (homOfLE h)).hom) := directedSystem_of_functor B
  have hab : ∀ (i j : α) (h : i ≤ j),
      (B.map (homOfLE h)).hom.comp (algebraMap (A.obj i) (B.obj i)) =
        (algebraMap (A.obj j) (B.obj j)).comp (A.map (homOfLE h)).hom := fun i j h =>
    congrArg CommRingCat.Hom.hom (τ.naturality (homOfLE h)).symm
  have hρ : ∀ (i j : α) (h : i ≤ j) (x : A.obj i),
      (cA.ι.app j).hom ((A.map (homOfLE h)).hom x) = (cA.ι.app i).hom x := fun _ _ h _ => by
    simp
  have hσ : ∀ (i j : α) (h : i ≤ j) (x : B.obj i),
      (cB.ι.app j).hom ((B.map (homOfLE h)).hom x) = (cB.ι.app i).hom x := fun _ _ h _ => by
    simp
  have hρσ : ∀ i, (cB.ι.app i).hom.comp (algebraMap (A.obj i) (B.obj i)) =
      (algebraMap cA.pt cB.pt).comp (cA.ι.app i).hom := fun i =>
    congrArg CommRingCat.Hom.hom (hφ i)
  refine Algebra.Syntomic.exists_stage_of_directed
    (a := fun _ _ h ↦ (A.map (homOfLE h)).hom) (b := fun _ _ h ↦ (B.map (homOfLE h)).hom) hab
    (R := (cA.pt : Type u)) (S := (cB.pt : Type u))
    (ρ := fun i ↦ (cA.ι.app i).hom) (σ := fun i ↦ (cB.ι.app i).hom)
    hρ hσ hρσ hAs hAz hBs hBz (fun i j h ↦ hpush i j h) hfpStage

/-! ### The affine case -/

/-- Over affine base changes, the base change of a locally finitely presented morphism induces a
finitely presented map of global sections. -/
lemma finitePresentation_appTop_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S) (X Y : Over S)
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left] [IsAffine (pullback g X.hom)]
    [IsAffine (pullback g Y.hom)] : (baseChangeMap g X Y f).appTop.hom.FinitePresentation := by
  have : LocallyOfFinitePresentation (baseChangeMap g X Y f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (baseChangeMap_isPullback g X Y f).flip inferInstance
  exact finitePresentation_appTop_of_affine _

/-- At every stage, the base change of a locally finitely presented morphism between affine
schemes induces a finitely presented map of global sections. -/
lemma finitePresentation_appTop_baseChangeDiagramMap_app {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) [∀ {a b : I} (g : a ⟶ b), IsAffineHom (D.map g)]
    {X Y : Over (D.obj i)} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f.left] (j : Over i) :
    ((baseChangeDiagramMap D i f).app j).appTop.hom.FinitePresentation := by
  have := isAffine_baseChangeDiagram_obj D i X j
  have := isAffine_baseChangeDiagram_obj D i Y j
  exact finitePresentation_appTop_baseChangeMap (D.map j.hom) X Y f

/-- Between affine schemes, the global sections of the base-change diagrams and of the map
between them form pushout squares of rings. -/
lemma isPushout_appTop_baseChangeDiagramMap {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) [∀ {a b : I} (g : a ⟶ b), IsAffineHom (D.map g)]
    {X Y : Over (D.obj i)} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) {j k : Over i}
    (g : j ⟶ k) :
    IsPushout ((baseChangeDiagram D i Y).map g).appTop ((baseChangeDiagramMap D i f).app k).appTop
      ((baseChangeDiagramMap D i f).app j).appTop ((baseChangeDiagram D i X).map g).appTop := by
  have := isAffine_baseChangeDiagram_obj D i X j
  have := isAffine_baseChangeDiagram_obj D i X k
  have := isAffine_baseChangeDiagram_obj D i Y j
  have := isAffine_baseChangeDiagram_obj D i Y k
  exact isPushout_appTop_of_isPullback (baseChangeDiagramMap_isPullback D i f g).flip

/-- Affine source and target suffice for the algebraic descent of syntomicity; the ambient base
scheme itself can be arbitrary. -/
private lemma exists_syntomic_baseChange_of_affine_source_target {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (X Y : Over (D.obj i₀)) [IsAffine X.left]
    [IsAffine Y.left] (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (h : Syntomic ((Over.pullback (c.π.app i₀)).map f).left) :
    ∃ j : Over i₀, Syntomic ((Over.pullback (D.map j.hom)).map f).left := by
  classical
  obtain ⟨α, hαOrder, hαDirected, hαNonempty, e, he⟩ := IsFiltered.exists_directed ((Over i₀)ᵒᵖ)
  let _ : PartialOrder α := hαOrder
  have _ : IsDirected α (· ≤ ·) := hαDirected
  have _ : Nonempty α := hαNonempty
  let FX := baseChangeDiagram D i₀ X
  let FY := baseChangeDiagram D i₀ Y
  let cX := baseChangeCone D c i₀ X
  let cY := baseChangeCone D c i₀ Y
  let cXd := cX.whisker e.leftOp
  let cYd := cY.whisker e.leftOp
  have hcXd : IsLimit cXd :=
    (Functor.Initial.isLimitWhiskerEquiv e.leftOp cX).symm (baseChangeConeIsLimit D hc i₀ X)
  have hcYd : IsLimit cYd :=
    (Functor.Initial.isLimitWhiskerEquiv e.leftOp cY).symm (baseChangeConeIsLimit D hc i₀ Y)
  have hAX : ∀ a : αᵒᵖ, IsAffine ((e.leftOp ⋙ FX).obj a) := fun a =>
    isAffine_baseChangeDiagram_obj D i₀ X (e.leftOp.obj a)
  have hAY : ∀ a : αᵒᵖ, IsAffine ((e.leftOp ⋙ FY).obj a) := fun a =>
    isAffine_baseChangeDiagram_obj D i₀ Y (e.leftOp.obj a)
  have hXs := exists_appTop_eq_of_isAffine_of_isLimit_of_directed (e.leftOp ⋙ FX) cXd hcXd
  have hXz := exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed
    (e.leftOp ⋙ FX) cXd hcXd
  have hYs := exists_appTop_eq_of_isAffine_of_isLimit_of_directed (e.leftOp ⋙ FY) cYd hcYd
  have hYz := exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed
    (e.leftOp ⋙ FY) cYd hcYd
  have _ : IsAffine (pullback (c.π.app i₀) X.hom) := Scheme.isAffine_of_isLimit cXd hcXd
  have _ : IsAffine (pullback (c.π.app i₀) Y.hom) := Scheme.isAffine_of_isLimit cYd hcYd
  let tLimit := baseChangeMap (c.π.app i₀) X Y f
  let GX : α ⥤ CommRingCat.{u} := e ⋙ FX.op ⋙ Scheme.Γ
  let GY : α ⥤ CommRingCat.{u} := e ⋙ FY.op ⋙ Scheme.Γ
  let rX := (Scheme.Γ.mapCocone cX.op).whisker e
  let rY := (Scheme.Γ.mapCocone cY.op).whisker e
  let τ : GY ⟶ GX := Functor.whiskerLeft e
    (Functor.whiskerRight (NatTrans.op (baseChangeDiagramMap D i₀ f)) Scheme.Γ)
  let φ : rY.pt ⟶ rX.pt := tLimit.appTop
  have hφ : ∀ a, τ.app a ≫ rX.ι.app a = rY.ι.app a ≫ φ := fun a =>
    congrArg (fun q : cX.pt ⟶ FY.obj (e.obj a).unop ↦ q.appTop)
      (baseChangeCone_π_isPullback D i₀ f c (e.obj a).unop).w
  have hfp : φ.hom.FinitePresentation :=
    finitePresentation_appTop_baseChangeMap (c.π.app i₀) X Y f
  have hsyn : φ.hom.Syntomic :=
    (syntomic_overPullback_iff_appTop_baseChangeMap (c.π.app i₀) X Y f).mp h
  have hfpStage : ∀ a, (τ.app a).hom.FinitePresentation := fun a =>
    finitePresentation_appTop_baseChangeDiagramMap_app D i₀ f (e.obj a).unop
  have hpush : ∀ (a b : α) (hab : a ≤ b),
      IsPushout (GY.map (homOfLE hab)) (τ.app a) (τ.app b) (GX.map (homOfLE hab)) :=
    fun a b hab ↦ isPushout_appTop_baseChangeDiagramMap D i₀ f (e.map (homOfLE hab)).unop
  obtain ⟨a, ha⟩ := exists_stage_syntomic_of_cocones GY GX τ rY rX φ hφ hYs hYz hXs hXz
    hfp hsyn hfpStage hpush
  refine ⟨(e.obj a).unop, ?_⟩
  have _ : IsAffine (pullback (D.map (e.obj a).unop.hom) X.hom) :=
    isAffine_baseChangeDiagram_obj D i₀ X (e.obj a).unop
  have _ : IsAffine (pullback (D.map (e.obj a).unop.hom) Y.hom) :=
    isAffine_baseChangeDiagram_obj D i₀ Y (e.obj a).unop
  exact (syntomic_overPullback_iff_appTop_baseChangeMap _ X Y f).mpr ha

/-! ### Descending syntomicity -/

/-- **Stacks Project, Tag 0C3L.**  If a locally finitely presented morphism over a stage of a
cofiltered inverse system with affine transition morphisms becomes syntomic over the limit, it
becomes syntomic at some later stage. -/
@[stacks 0C3L]
theorem exists_syntomic_baseChange_of_syntomic_limitBaseChange {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I) (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left] (hc : IsLimit c)
    (hf₀ : Syntomic ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (i : I) (g : i ⟶ i₀), Syntomic ((Over.pullback (D.map g)).map f₀).left := by
  classical
  have _ : MorphismProperty.RespectsIso (@Syntomic : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hopP : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion := by
    apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
    intro A B q W hq
    have : LocallyOfFinitePresentation q := hq
    infer_instance
  have hopS : MorphismProperty.HasOfPostcompProperty
      (@Syntomic : MorphismProperty Scheme.{u}) @IsOpenImmersion := by
    apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
    intro _ _ q W hq
    exact IsZariskiLocalAtTarget.restrict hq W
  obtain ⟨C, hCfinite, hCaffine, V, b, p, hVaffine, hb, hp⟩ :=
    exists_finite_affine_charts f₀.left
  have : Finite C.I₀ := hCfinite
  have (j : C.I₀) : IsAffine (C.X j) := hCaffine j
  have (j : C.I₀) : IsAffine (V j) := hVaffine j
  have (j : C.I₀) : IsOpenImmersion (b j) := hb j
  let UX (j : C.I₀) : Over (D.obj i₀) := Over.mk (C.f j ≫ X₀.hom)
  let VY (j : C.I₀) : Over (D.obj i₀) := Over.mk (b j ≫ Y₀.hom)
  let a (j : C.I₀) : UX j ⟶ X₀ := Over.homMk (C.f j)
  let b₀ (j : C.I₀) : VY j ⟶ Y₀ := Over.homMk (b j)
  let p₀ (j : C.I₀) : UX j ⟶ VY j := Over.homMk (p j) (by
    change p j ≫ (b j ≫ Y₀.hom) = C.f j ≫ X₀.hom
    rw [← Category.assoc, hp, Category.assoc, Over.w])
  have (j : C.I₀) : IsAffine (UX j).left := hCaffine j
  have (j : C.I₀) : IsAffine (VY j).left := hVaffine j
  have hoa (j : C.I₀) : IsOpenImmersion (a j).left := C.map_prop j
  have hob (j : C.I₀) : IsOpenImmersion (b₀ j).left := hb j
  have hp₀ (j : C.I₀) : p₀ j ≫ b₀ j = a j ≫ f₀ := by
    ext
    exact hp j
  have hfp (j : C.I₀) : LocallyOfFinitePresentation (p₀ j).left := by
    have hcomp : LocallyOfFinitePresentation ((a j).left ≫ f₀.left) := by
      have := hoa j
      infer_instance
    have heq : (p₀ j).left ≫ (b₀ j).left = (a j).left ≫ f₀.left :=
      congrArg (fun q : UX j ⟶ Y₀ ↦ q.left) (hp₀ j)
    rw [← heq] at hcomp
    exact MorphismProperty.HasOfPostcompProperty.of_postcomp (p₀ j).left (b₀ j).left
      (hob j) hcomp
  have hchart : ∀ j : C.I₀, ∃ (i : I) (g : i ⟶ i₀),
      Syntomic ((Over.pullback (D.map g)).map (p₀ j)).left := by
    intro j
    have := hoa j
    have := hob j
    have := hfp j
    have hs : Syntomic ((Over.pullback (c.π.app i₀)).map (p₀ j)).left :=
      prop_overPullback_chart (@Syntomic) (c.π.app i₀) X₀ Y₀ (UX j) (VY j) f₀ (a j) (b₀ j)
        (p₀ j) (hp₀ j) hf₀
    obtain ⟨j', hj'⟩ := exists_syntomic_baseChange_of_affine_source_target D c hc i₀
      (UX j) (VY j) (p₀ j) hs
    exact ⟨j'.left, j'.hom, hj'⟩
  obtain ⟨i', g, hg⟩ := common_stage_of_finite_prop (@Syntomic) D i₀ UX VY p₀ hchart
  exact ⟨i', g, prop_overPullback_of_charts (@Syntomic)
    (fun q hq => by have := hq; exact syntomic_of_isOpenImmersion q)
    (D.map g) X₀ Y₀ f₀ UX VY a b₀ p₀ hp₀
    (fun x ↦ by
      obtain ⟨j, y, hy⟩ := C.exists_eq x
      exact ⟨j, y, hy⟩)
    hg⟩

end AlgebraicGeometry

end
