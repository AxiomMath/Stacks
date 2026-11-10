module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. A
morphism over one stage which is locally of finite presentation and becomes flat over the limit is
flat after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange` descends flatness from the limit
  to a stage of the diagram.
* `AlgebraicGeometry.flat_overPullback_terminal_iff` reads that statement about a morphism over a
  stage back as a statement about one base-changed structure morphism.

## Implementation notes

Schemes over the chosen stage and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` means that `i` is a later stage than `i₀`
in the cofiltered indexing category. The cone leg at `i₀` gives the base change to the limit. The
index category is essentially small in the scheme universe: this ensures that the affine limits in
the proof are spectra of the actual filtered colimits of rings. The universes of index
objects and morphisms may otherwise be independent.

## References

* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace AlgebraicGeometry

/-! ### Flatness on affine charts -/

/-- For affine schemes, flatness of the map on global sections gives flatness of the scheme
morphism. This is the final step when applying the algebraic descent theorem to affine charts. -/
private lemma flat_of_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    (hf : f.appTop.hom.Flat) : Flat f :=
  (HasRingHomProperty.iff_of_isAffine (P := @Flat)).2 hf

/-- Local finite presentation passes to the maps in the base-change diagram. -/
@[ega "IV 21.15.9" "partial"]
private lemma locallyOfFinitePresentation_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [LocallyOfFinitePresentation f.left] :
    LocallyOfFinitePresentation (baseChangeMap g X Y f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (baseChangeMap_isPullback g X Y f).flip inferInstance

/-! ### Directed colimits of rings -/

/-- A functor from a preorder supplies the directed-system laws for its ring maps. -/
private lemma directedSystem_of_commRingCat_functor {ι : Type v} [Preorder ι]
    (F : ι ⥤ CommRingCat.{u}) :
    DirectedSystem (fun i ↦ (F.obj i : Type u)) (fun _ _ h ↦ (F.map (homOfLE h)).hom) := by
  constructor
  · intro i x
    simp
  · intro k j i hij hjk x
    exact congrArg (fun f : F.obj i ⟶ F.obj k ↦ f.hom x)
      (by simpa using (F.map_comp (homOfLE hij) (homOfLE hjk)).symm)

/-- The algebraic flatness descent theorem for a directed system of ring maps whose squares are
pushouts. This is the ring-map specialization of Tag 02JO (3). -/
private lemma eventually_flat_ring_of_directed {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {A B : ι → Type u} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    [DirectedSystem A fun i j h => a i j h] [DirectedSystem B fun i j h => b i j h]
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
    (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r)
    (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hσs : ∀ s, ∃ i x, σ i x = s)
    (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)
    (hpush : ∀ i j (h : i ≤ j),
      IsPushout (CommRingCat.ofHom (a i j h)) (CommRingCat.ofHom (algebraMap (A i) (B i)))
        (CommRingCat.ofHom (algebraMap (A j) (B j))) (CommRingCat.ofHom (b i j h)))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i)) :
    ∃ i, ∀ j, i ≤ j → (algebraMap (A j) (B j)).Flat := by
  let n (i j : ι) (h : i ≤ j) : B i →ₛₗ[b i j h] B j := (b i j h).toSemilinearMap
  have : DirectedSystem B (fun i j h => n i j h) :=
    ⟨fun _ x => DirectedSystem.map_self' b x,
      fun _ _ _ hij hjk x => DirectedSystem.map_map' b hij hjk x⟩
  have hbc : ∀ i j (h : i ≤ j),
      let := Module.Flat.DirectedModel.algebraB b h
      let := Module.compHom (B j) (b i j h)
      have : IsScalarTower (B i) (B j) (B j) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange (B j) (Module.Flat.DirectedModel.transLinear b n h) := by
    intro i j h
    let : Algebra (B i) (B j) := (b i j h).toAlgebra
    change IsBaseChange (B j) (Algebra.linearMap (B i) (B j))
    exact IsBaseChange.linearMap (B i) (B j)
  obtain ⟨i, hi⟩ := Module.Flat.eventually_flat_of_directed (R := R) (S := S) S
    a b n hab ρ σ (fun i => (σ i).toSemilinearMap)
    hρ hσ hσ hρσ hρs hρz hσs hσz hσs hσz hpush hbc hfp (fun _ => inferInstance)
  refine ⟨i, fun j hij => ?_⟩
  have hm : Module.compHom (B j) (algebraMap (A j) (B j)) =
      (inferInstance : Module (A j) (B j)) := by
    apply Module.ext'
    intro x y
    change (algebraMap (A j) (B j)) x * y = x • y
    rw [Algebra.smul_def]
  have hj := hi j hij
  rw [hm] at hj
  exact (RingHom.flat_algebraMap_iff).2 hj

/-- A diagram of finitely presented ring maps with pushout transition squares is eventually flat
when its colimit map is flat. -/
private lemma eventually_flat_of_ring_cocones {α : Type u} [PartialOrder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] (A B : α ⥤ CommRingCat.{u}) (τ : A ⟶ B)
    (cA : Cocone A) (cB : Cocone B) (hcA : IsColimit cA) (hcB : IsColimit cB)
    (φ : cA.pt ⟶ cB.pt) (hφ : ∀ i, τ.app i ≫ cB.ι.app i = cA.ι.app i ≫ φ)
    (hfp : φ.hom.FinitePresentation) (hflat : φ.hom.Flat)
    (hfpStage : ∀ i, (τ.app i).hom.FinitePresentation)
    (hpush : ∀ i j (h : i ≤ j),
      IsPushout (A.map (homOfLE h)) (τ.app i) (τ.app j) (B.map (homOfLE h))) :
    ∃ i, ∀ j, i ≤ j → (τ.app j).hom.Flat := by
  let : Algebra cA.pt cB.pt := φ.hom.toAlgebra
  let (i : α) : Algebra (A.obj i) (B.obj i) := (τ.app i).hom.toAlgebra
  have : Algebra.FinitePresentation cA.pt cB.pt := hfp
  have : Module.Flat cA.pt cB.pt := (RingHom.flat_algebraMap_iff).mp hflat
  let a (i j : α) (h : i ≤ j) : A.obj i →+* A.obj j := (A.map (homOfLE h)).hom
  let b (i j : α) (h : i ≤ j) : B.obj i →+* B.obj j := (B.map (homOfLE h)).hom
  have : DirectedSystem (fun i ↦ (A.obj i : Type u)) (fun i j h ↦ a i j h) :=
    directedSystem_of_commRingCat_functor A
  have : DirectedSystem (fun i ↦ (B.obj i : Type u)) (fun i j h ↦ b i j h) :=
    directedSystem_of_commRingCat_functor B
  have hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A.obj i) (B.obj i)) =
        (algebraMap (A.obj j) (B.obj j)).comp (a i j h) := fun i j h =>
    congrArg CommRingCat.Hom.hom (τ.naturality (homOfLE h)).symm
  let ρ (i : α) : A.obj i →+* cA.pt := (cA.ι.app i).hom
  let σ (i : α) : B.obj i →+* cB.pt := (cB.ι.app i).hom
  have hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x := by simp [ρ, a]
  have hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x := by simp [σ, b]
  have hρσ : ∀ i, (σ i).comp (algebraMap (A.obj i) (B.obj i)) =
      (algebraMap cA.pt cB.pt).comp (ρ i) := fun i => congrArg CommRingCat.Hom.hom (hφ i)
  exact eventually_flat_ring_of_directed a b hab ρ σ hρ hσ hρσ
    (ring_colimit_surjective A cA hcA) (ring_colimit_eventually_zero A cA hcA)
    (ring_colimit_surjective B cB hcB) (ring_colimit_eventually_zero B cB hcB) hpush hfpStage

/-! ### The affine case -/

/-- Flatness descends for an arrow between affine schemes over the fixed stage. -/
private lemma exists_flat_affine_baseChange {I : Type v} [Category.{w} I] [EssentiallySmall.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X Y : Over (D.obj i₀)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f.left]
    [Flat ((Over.pullback (c.π.app i₀)).map f).left] :
    ∃ (i : I) (g : i ⟶ i₀), Flat ((Over.pullback (D.map g)).map f).left := by
  classical
  have hriF : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨α, _, _, _, e, he⟩ := exists_directed_cofinal_over (I := I) i₀
  let FX := baseChangeDiagram D i₀ X
  let FY := baseChangeDiagram D i₀ Y
  let cX : Cone FX := baseChangeCone D c i₀ X
  let cY : Cone FY := baseChangeCone D c i₀ Y
  let rX := (Scheme.Γ.mapCocone cX.op).whisker e
  let rY := (Scheme.Γ.mapCocone cY.op).whisker e
  have haff (Z : Over (D.obj i₀)) [IsAffine Z.left] (a : Over i₀) :
      IsAffine (pullback (D.map a.hom) Z.hom) := isAffine_baseChangeDiagram_obj D i₀ Z a
  have (Z : Over (D.obj i₀)) [IsAffine Z.left] (a : αᵒᵖ) :
      IsAffine ((e.leftOp ⋙ baseChangeDiagram D i₀ Z).obj a) := haff Z _
  have (Z : Over (D.obj i₀)) [IsAffine Z.left] (a : (Over i₀)ᵒᵖ) :
      IsAffine ((baseChangeDiagram D i₀ Z).op.obj a).unop := haff Z _
  have hcol (Z : Over (D.obj i₀)) [IsAffine Z.left] :
      IsColimit ((Scheme.Γ.mapCocone (baseChangeCone D c i₀ Z).op).whisker e) :=
    (Functor.Final.isColimitWhiskerEquiv e _).symm
      (Classical.choice (nonempty_isColimit_sections_baseChange D c hc i₀ Z))
  have haffLim (Z : Over (D.obj i₀)) [IsAffine Z.left] : IsAffine (pullback (c.π.app i₀) Z.hom) :=
    Scheme.isAffine_of_isLimit ((baseChangeCone D c i₀ Z).whisker e.leftOp)
      ((Functor.Initial.isLimitWhiskerEquiv e.leftOp _).symm (baseChangeConeIsLimit D hc i₀ Z))
  have hcX : IsColimit rX := hcol X
  have hcY : IsColimit rY := hcol Y
  have := haffLim X
  have := haffLim Y
  let t := baseChangeDiagramMap D i₀ f
  let tLimit := baseChangeMap (c.π.app i₀) X Y f
  let GY := e ⋙ FY.op ⋙ Scheme.Γ
  let GX := e ⋙ FX.op ⋙ Scheme.Γ
  let τ : GY ⟶ GX := Functor.whiskerLeft e (Functor.whiskerRight (NatTrans.op t) Scheme.Γ)
  let φ : rY.pt ⟶ rX.pt := tLimit.appTop
  have hφ : ∀ a, τ.app a ≫ rX.ι.app a = rY.ι.app a ≫ φ := fun a =>
    congrArg (fun q : cX.pt ⟶ FY.obj (e.obj a).unop => q.appTop)
      (baseChangeCone_π_isPullback D i₀ f c (e.obj a).unop).w
  have hfp : φ.hom.FinitePresentation := by
    have : LocallyOfFinitePresentation tLimit :=
      locallyOfFinitePresentation_baseChangeMap (c.π.app i₀) X Y f
    exact Scheme.Hom.finitePresentation_appTop tLimit
  have hflat : φ.hom.Flat := by
    have h : Flat tLimit := (baseChangeMap_prop_iff (@Flat) (c.π.app i₀) X Y f).2 inferInstance
    exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 h
  have hfpStage : ∀ a, (τ.app a).hom.FinitePresentation := by
    intro a
    let A := (e.obj a).unop
    have : LocallyOfFinitePresentation (baseChangeMap (D.map A.hom) X Y f) :=
      locallyOfFinitePresentation_baseChangeMap (D.map A.hom) X Y f
    change (baseChangeMap (D.map A.hom) X Y f).appTop.hom.FinitePresentation
    exact Scheme.Hom.finitePresentation_appTop _
  have hpush : ∀ a b (h : a ≤ b),
      IsPushout (GY.map (homOfLE h)) (τ.app a) (τ.app b) (GX.map (homOfLE h)) := by
    intro a b h
    let A := (e.obj a).unop
    let B := (e.obj b).unop
    let k : B ⟶ A := (e.map (homOfLE h)).unop
    have hg : D.map k.left ≫ D.map A.hom = D.map B.hom := by rw [← D.map_comp, k.w]
    exact isPushout_appTop_of_isPullback
      (baseChangeTransition_isPullback (D.map A.hom) (D.map B.hom) (D.map k.left) hg X Y f)
  obtain ⟨a, ha⟩ := eventually_flat_of_ring_cocones GY GX τ rY rX hcY hcX φ hφ hfp hflat
    hfpStage hpush
  let A := (e.obj a).unop
  refine ⟨A.left, A.hom, ?_⟩
  have hf : (τ.app a).hom.Flat := ha a le_rfl
  change (baseChangeMap (D.map A.hom) X Y f).appTop.hom.Flat at hf
  exact (baseChangeMap_prop_iff (@Flat) (D.map A.hom) X Y f).1 (flat_of_appTop _ hf)

/-! ### Descending flatness -/

/-- **Stacks Project, Tag 04AI.** A locally finitely presented morphism over a stage which
becomes flat over the inverse limit is flat at some later stage. -/
@[stacks 04AI]
lemma exists_flat_baseChange_of_limitBaseChange
    {I : Type v} [Category.{w} I] [EssentiallySmall.{u} I]
    (D : Functor I Scheme.{u}) (c : Cone D) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (hc : IsLimit c)
    [Flat ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀), Flat ((Over.pullback (D.map g)).map f₀).left := by
  classical
  have hriF : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hriP : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hzls : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have hopF : MorphismProperty.HasOfPostcompProperty
      (@Flat : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict _
      (fun g _ (_ : Flat g) ↦ inferInstance)
  have hopP : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict _
      (fun g _ (_ : LocallyOfFinitePresentation g) ↦ inferInstance)
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
      Flat ((Over.pullback (D.map g)).map (p₀ j)).left := by
    intro j
    have := hoa j
    have := hob j
    have := hfp j
    have hs : Flat ((Over.pullback (c.π.app i₀)).map (p₀ j)).left :=
      prop_overPullback_chart (@Flat) (c.π.app i₀) X₀ Y₀ (UX j) (VY j) f₀ (a j) (b₀ j)
        (p₀ j) (hp₀ j) inferInstance
    exact exists_flat_affine_baseChange D c hc i₀ (UX j) (VY j) (p₀ j)
  obtain ⟨i', g, hg⟩ := common_stage_of_finite_prop (@Flat) D i₀ UX VY p₀ hchart
  refine ⟨i', g, ?_⟩
  have hoa' : ∀ j, IsOpenImmersion (a j).left := hoa
  have hob' : ∀ j, IsOpenImmersion (b₀ j).left := hob
  exact prop_overPullback_of_charts (@Flat) (fun q hq => by have := hq; infer_instance)
    (D.map g) X₀ Y₀ f₀ UX VY a b₀ p₀ hp₀ C.exists_eq hg

/-- Flatness of the base change of the morphism from an object of an overcategory to its terminal
object is flatness of the base-changed structure morphism. This is how
`AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange`, a statement about morphisms over a
stage, is read as a statement about one structure morphism. -/
lemma flat_overPullback_terminal_iff {S T : Scheme.{u}} (b : T ⟶ S) (Z : Over S) :
    Flat ((Over.pullback b).map (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 S))).left ↔
      Flat ((Over.pullback b).obj Z).hom := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← MorphismProperty.cancel_right_of_respectsIso
    (P := (@Flat : MorphismProperty Scheme.{u})) _ (pullback.snd (𝟙 S) b)]
  simp only [Over.pullback_map_left, Over.pullback_obj_hom, Over.homMk_left,
    Over.mk_hom, pullback.lift_snd]

end AlgebraicGeometry
