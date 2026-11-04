module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Affine
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent

/-!
# Closed immersions descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of quasi-compact and quasi-separated schemes
with affine transition morphisms. If a morphism over one stage is locally of finite type and
becomes a closed immersion after base change to the limit, then it is a closed immersion after
base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit` descends a closed immersion
  from the limit to a finite stage.

## Implementation notes

The indexing category for descent is essentially small relative to the scheme universe,
expressing the set-sized inverse systems in the source.

Schemes over the chosen stage are represented by objects of its over category, and base change is
`CategoryTheory.Over.pullback`. A morphism `i ⟶ i₀` represents a stage later than `i₀` in the
cofiltered indexing category. This generalizes the directed indexing set in the source.

The affine case is the heart of the argument: there the morphism of global section rings is a
filtered colimit of the morphisms at the finite stages, and a surjection out of a filtered colimit
of finitely generated algebras is already a surjection at a finite stage.

## References

* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u z q

namespace AlgebraicGeometry

/-! ### Global sections of a cofiltered limit -/

/-- The global sections of a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition morphisms are the filtered colimit of the global sections of the stages, as a colimit
of sets. -/
private noncomputable def isColimit_sections {J : Type v} [Category.{w} J] [IsCofiltered J]
    [EssentiallySmall.{u} J] (E : J ⥤ Scheme.{u}) (d : Cone E) (hd : IsLimit d)
    [∀ {j k : J} (g : j ⟶ k), IsAffineHom (E.map g)]
    [∀ j, CompactSpace (E.obj j)] [∀ j, QuasiSeparatedSpace (E.obj j)] :
    IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone d.op) := by
  have : InitiallySmall.{u} J := initiallySmall_of_essentiallySmall J
  refine Types.FilteredColimit.isColimitOf' _
    ((Scheme.Γ ⋙ forget CommRingCat).mapCocone d.op) ?_ ?_
  · intro s
    obtain ⟨i, t, ht⟩ := exists_appTop_π_eq_of_isLimit_of_initiallySmall E d hd s
    exact ⟨Opposite.op i, t, ht⟩
  · intro i s t h
    obtain ⟨j, g, hg⟩ := exists_app_map_eq_map_of_isLimit_of_initiallySmall E d hd
      (U := ⊤) isCompact_univ s t h
    exact ⟨Opposite.op j, g.op, hg⟩

/-- Two global sections of two stages which agree in the limit already agree at a common later
stage. -/
private lemma exists_equal_stage_of_equal_limit_sections {J : Type v} [Category.{w} J]
    [IsCofiltered J] (F : J ⥤ Scheme.{u}) (c : Cone F)
    (hΓ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone c.op))
    {j k : J} (x : Γ(F.obj j, ⊤)) (y : Γ(F.obj k, ⊤))
    (h : (c.π.app j).appTop x = (c.π.app k).appTop y) :
    ∃ (l : J) (f : l ⟶ j) (g : l ⟶ k), (F.map f).appTop x = (F.map g).appTop y := by
  let cΓ := (Scheme.Γ ⋙ forget CommRingCat).mapCocone c.op
  let m := IsCofiltered.min j k
  let f := IsCofiltered.minToLeft j k
  let g := IsCofiltered.minToRight j k
  have hm : (c.π.app m).appTop ((F.map f).appTop x) =
      (c.π.app m).appTop ((F.map g).appTop y) := by
    calc
      (c.π.app m).appTop ((F.map f).appTop x) = (c.π.app j).appTop x := by
        show ((F.map f).appTop ≫ (c.π.app m).appTop) x = _
        rw [← Scheme.Hom.comp_appTop, c.w f]
      _ = (c.π.app k).appTop y := h
      _ = (c.π.app m).appTop ((F.map g).appTop y) := by
        show _ = ((F.map g).appTop ≫ (c.π.app m).appTop) y
        rw [← Scheme.Hom.comp_appTop, c.w g]
  have hm' : cΓ.ι.app (Opposite.op m) ((F.map f).appTop x) =
      cΓ.ι.app (Opposite.op m) ((F.map g).appTop y) := hm
  obtain ⟨l, t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff' hΓ _ _).mp hm'
  refine ⟨l.unop, t.unop ≫ f, t.unop ≫ g, ?_⟩
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, Functor.map_comp, Scheme.Hom.comp_appTop]
  exact ht

/-! ### Finitely many stages in a filtered category -/

/-- Finitely many objects of a filtered category admit a common successor. -/
private lemma exists_common_object_of_finset {J : Type v} [Category.{w} J] [IsFiltered J]
    {α : Type*} (s : Finset α) (obj : α → J) :
    Nonempty {j : J // ∀ a ∈ s, Nonempty (obj a ⟶ j)} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⟨Classical.choice IsFiltered.nonempty, by simp⟩⟩
  | @insert a s ha ih =>
      obtain ⟨⟨j, hj⟩⟩ := ih
      obtain ⟨k, hjk, hak, -⟩ := IsFilteredOrEmpty.cocone_objs j (obj a)
      refine ⟨⟨k, fun b hb => ?_⟩⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨hak⟩
      · exact ⟨(hj b hb).some ≫ hjk⟩

/-- Finitely many pairs of parallel arrows in a filtered category can be equalised
simultaneously by postcomposition. -/
private lemma exists_postcompose_equalize_finset {J : Type v} [Category.{w} J]
    [IsFilteredOrEmpty J] {α : Type*} (s : Finset α) {a b : J} (f g : α → (a ⟶ b)) :
    ∃ (c : J) (h : b ⟶ c), ∀ x ∈ s, f x ≫ h = g x ≫ h := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨b, 𝟙 _, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨c, h, hh⟩ := ih
      obtain ⟨d, k, hk⟩ := IsFilteredOrEmpty.cocone_maps (f x ≫ h) (g x ≫ h)
      refine ⟨d, h ≫ k, fun y hy => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa [Category.assoc] using hk
      · simpa [Category.assoc] using congrArg (fun q => q ≫ k) (hh y hy)

/-! ### Surjectivity in a filtered colimit of algebras -/

/-- In a morphism of filtered diagrams of rings whose colimit is surjective, every element of a
stage of the target comes, at some later stage, from the source. -/
private lemma exists_stage_eq_map_of_surjective_colimit {J : Type z} [Category.{w} J]
    {F G : J ⥤ CommRingCat.{q}} (η : F ⟶ G) {cF : Cocone F} {cG : Cocone G}
    (α : cF.pt ⟶ cG.pt) (hcompat : ∀ j, cF.ι.app j ≫ α = η.app j ≫ cG.ι.app j)
    (hFsurj : ∀ z : cF.pt, ∃ (j : J) (x : F.obj j), (cF.ι.app j).hom x = z)
    (hGeq : ∀ {j k : J} (x : G.obj j) (y : G.obj k),
      (cG.ι.app j).hom x = (cG.ι.app k).hom y →
      ∃ (l : J) (f : j ⟶ l) (g : k ⟶ l), (G.map f).hom x = (G.map g).hom y)
    (hsurj : Function.Surjective α.hom) {j₀ : J} (x : G.obj j₀) :
    ∃ (j : J) (f : j₀ ⟶ j) (a : F.obj j), (η.app j).hom a = (G.map f).hom x := by
  obtain ⟨aLim, haLim⟩ := hsurj ((cG.ι.app j₀).hom x)
  obtain ⟨k, a, hak⟩ := hFsurj aLim
  have heq : (cG.ι.app k).hom ((η.app k).hom a) = (cG.ι.app j₀).hom x := by
    change (cF.ι.app k).hom a = aLim at hak
    calc
      (cG.ι.app k).hom ((η.app k).hom a) = (α.hom) ((cF.ι.app k).hom a) := by
        simpa [ConcreteCategory.comp_apply] using
          (congrArg (fun q : F.obj k ⟶ cG.pt => q.hom a) (hcompat k)).symm
      _ = α.hom aLim := by rw [hak]
      _ = (cG.ι.app j₀).hom x := haLim
  obtain ⟨j, f, g, hfg⟩ := hGeq ((η.app k).hom a) x heq
  exact ⟨j, g, (F.map f).hom a, (NatTrans.naturality_apply η f a).trans hfg⟩

/-- Finitely many elements of a stage of a filtered diagram of rings, each lying in the image of a
morphism of diagrams at some later stage, all lie in that image at one common later stage. -/
private lemma exists_stage_map_mem_range {J : Type z} [Category.{w} J] [IsFiltered J]
    {F G : J ⥤ CommRingCat.{q}} (η : F ⟶ G) {j₀ : J} (s : Finset (G.obj j₀))
    (hstage : ∀ x ∈ s, ∃ (j : J) (f : j₀ ⟶ j) (a : F.obj j), (η.app j).hom a = (G.map f).hom x) :
    ∃ (n : J) (f : j₀ ⟶ n), ∀ y ∈ s, (G.map f).hom y ∈ (η.app n).hom.range := by
  classical
  choose jx fjx ax hax using hstage
  let αs := {x // x ∈ s}
  let K : Option αs → J := fun x => x.elim j₀ (fun x => jx x.1 x.2)
  have : Fintype αs := Finset.fintypeCoeSort s
  obtain ⟨⟨m, hm⟩⟩ := exists_common_object_of_finset (Finset.univ : Finset (Option αs)) K
  let getHom {a b : J} (x : Nonempty (a ⟶ b)) : a ⟶ b := Classical.choice x
  let f₀ : j₀ ⟶ m := getHom (hm none (Finset.mem_univ _))
  let p (x : αs) := fjx x.1 x.2 ≫ getHom (hm (some x) (Finset.mem_univ _))
  have hrange : ∀ x : αs, (G.map (p x)).hom x.1 ∈ (η.app m).hom.range := by
    intro x
    refine ⟨(F.map (getHom (hm (some x) (Finset.mem_univ _)))).hom (ax x.1 x.2), ?_⟩
    refine (NatTrans.naturality_apply η _ (ax x.1 x.2)).trans ?_
    rw [hax x.1 x.2]
    dsimp [p, K]
    rw [Functor.map_comp]
    rfl
  obtain ⟨n, e, he⟩ :=
    exists_postcompose_equalize_finset (Finset.univ : Finset αs) p (fun _ => f₀)
  let f : j₀ ⟶ n := f₀ ≫ e
  refine ⟨n, f, fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := hrange ⟨y, hy⟩
  refine ⟨(F.map e).hom z, ?_⟩
  refine (NatTrans.naturality_apply η e z).trans ?_
  rw [hz]
  show ((G.map (p ⟨y, hy⟩)) ≫ G.map e).hom y = _
  rw [← Functor.map_comp, he ⟨y, hy⟩ (Finset.mem_univ _)]

/-- A ring map is surjective once its target is generated, as an algebra over its source, by a
set contained in its range. -/
private lemma surjective_of_adjoin_eq_top_of_subset_range {R A : Type*} [CommRing R]
    [CommRing A] (φ : R →+* A) {S : Set A} (hS : letI := φ.toAlgebra; Algebra.adjoin R S = ⊤)
    (hmem : ∀ y ∈ S, y ∈ φ.range) : Function.Surjective φ := by
  let := φ.toAlgebra
  let ψ : R →ₐ[R] A := IsScalarTower.toAlgHom _ _ _
  have hle : Algebra.adjoin R S ≤ ψ.range := Algebra.adjoin_le fun z hz => hmem z hz
  rw [show Algebra.adjoin R S = ⊤ from hS, top_le_iff] at hle
  exact (_root_.AlgHom.range_eq_top ψ).mp hle

/-- A morphism of filtered diagrams of rings whose colimit is surjective, and whose target is
generated over its source by a fixed finite set at every stage, is surjective at some stage. -/
private lemma exists_surjective_component_of_filtered_colimit {J : Type z} [Category.{w} J]
    [IsFiltered J] (F G : J ⥤ CommRingCat.{q}) (η : F ⟶ G) {cF : Cocone F} {cG : Cocone G}
    (α : cF.pt ⟶ cG.pt) (hcompat : ∀ j, cF.ι.app j ≫ α = η.app j ≫ cG.ι.app j)
    (hFsurj : ∀ z : cF.pt, ∃ (j : J) (x : F.obj j), (cF.ι.app j).hom x = z)
    (hGeq : ∀ {j k : J} (x : G.obj j) (y : G.obj k),
      (cG.ι.app j).hom x = (cG.ι.app k).hom y →
      ∃ (l : J) (f : j ⟶ l) (g : k ⟶ l), (G.map f).hom x = (G.map g).hom y)
    (j₀ : J) (s : Finset (G.obj j₀))
    (hgen : ∀ (j : J) (f : j₀ ⟶ j),
      letI := (η.app j).hom.toAlgebra
      Algebra.adjoin (F.obj j) ((G.map f).hom '' (s : Set (G.obj j₀))) = ⊤)
    (hsurj : Function.Surjective α.hom) :
    ∃ (j : J) (_ : j₀ ⟶ j), Function.Surjective (η.app j).hom := by
  obtain ⟨n, f, hmem⟩ := exists_stage_map_mem_range η s fun x _ =>
    exists_stage_eq_map_of_surjective_colimit η α hcompat hFsurj hGeq hsurj x
  refine ⟨n, f, surjective_of_adjoin_eq_top_of_subset_range _ (hgen n f) ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hmem y hy

/-! ### The affine case -/

/-- The base change of a locally of finite type morphism of schemes over a base is again locally
of finite type. -/
private lemma locallyOfFiniteType_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S) (X Y : Over S)
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] : LocallyOfFiniteType (baseChangeMap g X Y f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (baseChangeMap_isPullback g X Y f).flip inferInstance

/-- For a morphism of affine schemes over a stage which is locally of finite type, finitely many
global sections of the base change of the source to that stage generate the global sections of
the base change to every later stage over those of the target. -/
private lemma exists_finset_adjoin_baseChangeDiagram_eq_top {I : Type v} [Category.{w} I]
    (D : I ⥤ Scheme.{u}) (i₀ : I) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X Y : Over (D.obj i₀)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] :
    ∃ s : Finset (((baseChangeDiagram D i₀ X).op ⋙ Scheme.Γ).obj (Opposite.op (Over.mk (𝟙 i₀)))),
      ∀ (a : (Over i₀)ᵒᵖ) (g : Opposite.op (Over.mk (𝟙 i₀)) ⟶ a),
      letI := ((Functor.whiskerRight (NatTrans.op (baseChangeDiagramMap D i₀ f))
        Scheme.Γ).app a).hom.toAlgebra
      Algebra.adjoin (((baseChangeDiagram D i₀ Y).op ⋙ Scheme.Γ).obj a)
        ((((baseChangeDiagram D i₀ X).op ⋙ Scheme.Γ).map g).hom '' (s : Set _)) = ⊤ := by
  let rootObj : Over i₀ := Over.mk (𝟙 i₀)
  let root : (Over i₀)ᵒᵖ := Opposite.op rootObj
  let t := baseChangeDiagramMap D i₀ f
  let F := (baseChangeDiagram D i₀ Y).op ⋙ Scheme.Γ
  let G := (baseChangeDiagram D i₀ X).op ⋙ Scheme.Γ
  let η : F ⟶ G := Functor.whiskerRight (NatTrans.op t) Scheme.Γ
  let : Algebra (F.obj root) (G.obj root) := (η.app root).hom.toAlgebra
  let fRoot := t.app rootObj
  have : IsAffine (pullback (D.map rootObj.hom) X.hom) :=
    isAffine_baseChangeDiagram_obj D i₀ X rootObj
  have : IsAffine (pullback (D.map rootObj.hom) Y.hom) :=
    isAffine_baseChangeDiagram_obj D i₀ Y rootObj
  have : IsAffine ((baseChangeDiagram D i₀ X).obj rootObj) :=
    isAffine_baseChangeDiagram_obj D i₀ X rootObj
  have : IsAffine ((baseChangeDiagram D i₀ Y).obj rootObj) :=
    isAffine_baseChangeDiagram_obj D i₀ Y rootObj
  have : LocallyOfFiniteType fRoot := locallyOfFiniteType_baseChangeMap (D.map rootObj.hom) X Y f
  have hft : Algebra.FiniteType (F.obj root) (G.obj root) := by
    show fRoot.appTop.hom.FiniteType
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      fRoot.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, fun a g => ?_⟩
  have hg : D.map g.unop.left ≫ D.map rootObj.hom = D.map a.unop.hom := by
    rw [← D.map_comp, g.unop.w]
  exact adjoin_image_eq_top_of_isPushout (isPushout_appTop_of_isPullback
    (baseChangeTransition_isPullback (D.map rootObj.hom) (D.map a.unop.hom)
      (D.map g.unop.left) hg X Y f)).flip s hs

/-- A morphism of affine schemes over a stage which is locally of finite type and becomes a closed
immersion over the limit is a closed immersion at some later stage. -/
private lemma exists_isClosedImmersion_affine_baseChange {I : Type v} [Category.{w} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i₀ : I) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X Y : Over (D.obj i₀)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left]
    [IsClosedImmersion ((Over.pullback (c.π.app i₀)).map f).left] :
    ∃ A : Over i₀, IsClosedImmersion ((Over.pullback (D.map A.hom)).map f).left := by
  classical
  let FX := baseChangeDiagram D i₀ X
  let FY := baseChangeDiagram D i₀ Y
  let cX : Cone FX := baseChangeCone D c i₀ X
  let cY : Cone FY := baseChangeCone D c i₀ Y
  let tLimit := baseChangeMap (c.π.app i₀) X Y f
  let F := FY.op ⋙ Scheme.Γ
  let G := FX.op ⋙ Scheme.Γ
  let η : F ⟶ G := Functor.whiskerRight (NatTrans.op (baseChangeDiagramMap D i₀ f)) Scheme.Γ
  let cF : Cocone F := Scheme.Γ.mapCocone cY.op
  let cG : Cocone G := Scheme.Γ.mapCocone cX.op
  have hLimX : IsLimit cX := baseChangeConeIsLimit D hc i₀ X
  have hLimY : IsLimit cY := baseChangeConeIsLimit D hc i₀ Y
  have (A : Over i₀) : IsAffine (FX.obj A) := isAffine_baseChangeDiagram_obj D i₀ X A
  have (A : Over i₀) : IsAffine (FY.obj A) := isAffine_baseChangeDiagram_obj D i₀ Y A
  have : ∀ {A B : Over i₀} (g : A ⟶ B), IsAffineHom (FX.map g) :=
    fun g ↦ isAffineHom_baseChangeDiagram_map D i₀ X g
  have : ∀ {A B : Over i₀} (g : A ⟶ B), IsAffineHom (FY.map g) :=
    fun g ↦ isAffineHom_baseChangeDiagram_map D i₀ Y g
  let α : cF.pt ⟶ cG.pt := tLimit.appTop
  have hcompat : ∀ a, cF.ι.app a ≫ α = η.app a ≫ cG.ι.app a := fun a ↦
    (congrArg (fun q : cX.pt ⟶ FY.obj a.unop => q.appTop)
      (baseChangeCone_π_isPullback D i₀ f c a.unop).w).symm
  have hFsurj : ∀ z : cF.pt, ∃ (a : (Over i₀)ᵒᵖ) (x : F.obj a), (cF.ι.app a).hom x = z :=
    Types.jointly_surjective_of_isColimit (isColimit_sections FY cY hLimY)
  have : LocallyOfFiniteType tLimit := locallyOfFiniteType_baseChangeMap (c.π.app i₀) X Y f
  have : IsClosedImmersion tLimit :=
    (baseChangeMap_prop_iff (@IsClosedImmersion) (c.π.app i₀) X Y f).2 inferInstance
  have hαsurj : Function.Surjective α.hom := by
    have : IsAffine (pullback (c.π.app i₀) Y.hom) := Scheme.isAffine_of_isLimit cY hLimY
    exact Scheme.Hom.app_surjective tLimit ⊤ (isAffineOpen_top _)
  obtain ⟨s, hgen⟩ := exists_finset_adjoin_baseChangeDiagram_eq_top D i₀ X Y f
  obtain ⟨a, g, hsurj⟩ := exists_surjective_component_of_filtered_colimit
    F G η (cF := cF) (cG := cG) α hcompat hFsurj (fun x y h ↦ by
      obtain ⟨l, p, q, heq⟩ := exists_equal_stage_of_equal_limit_sections
        FX cX (isColimit_sections FX cX hLimX) x y h
      exact ⟨Opposite.op l, p.op, q.op, heq⟩)
    (Opposite.op (Over.mk (𝟙 i₀))) s hgen hαsurj
  let A : Over i₀ := a.unop
  have hsurj' : Function.Surjective (baseChangeMap (D.map A.hom) X Y f).appTop := hsurj
  exact ⟨A, (baseChangeMap_prop_iff (@IsClosedImmersion) (D.map A.hom) X Y f).1
    (IsClosedImmersion.of_surjective_of_isAffine _ hsurj')⟩

/-! ### Reduction to the affine case -/

/-- A closed immersion on each member of an open cover of the target of a base-changed morphism
makes the base change a closed immersion. -/
private lemma isClosedImmersion_of_baseChange_cover {S T : Scheme.{u}} (p : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) (U : Y.left.OpenCover) (XU : U.I₀ → Over S)
    (fu : ∀ k, XU k ⟶ Over.mk (U.f k ≫ Y.hom)) (vx : ∀ k, XU k ⟶ X)
    (hpb : ∀ k, IsPullback (vx k).left (fu k).left f.left (U.f k))
    (H : ∀ k, IsClosedImmersion ((Over.pullback p).map (fu k)).left) :
    IsClosedImmersion ((Over.pullback p).map f).left := by
  let vy (k) : Over.mk (U.f k ≫ Y.hom) ⟶ Y := Over.homMk (U.f k)
  let Up : ((Over.pullback p).obj Y).left.OpenCover :=
    { I₀ := U.I₀
      X := fun k => ((Over.pullback p).obj (Over.mk (U.f k ≫ Y.hom))).left
      f := fun k => ((Over.pullback p).map (vy k)).left
      mem₀ := Precoverage.mem_coverings_of_isPullback U.f U.mem₀ (pullback.fst Y.hom p)
        (fun k => ((Over.pullback p).map (vy k)).left)
        (fun k => pullback.fst (U.f k ≫ Y.hom) p)
        (fun k => (overPullback_isPullback p (Over.mk (U.f k ≫ Y.hom)) Y (vy k)).flip) }
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) Up
  intro k
  have hOver : IsPullback (vx k) (fu k) f (vy k) :=
    IsPullback.of_map_of_faithful (Over.forget S) (hpb k)
  have hp := hOver.map (Over.pullback p ⋙ Over.forget _)
  change IsPullback ((Over.pullback p).map (vx k)).left ((Over.pullback p).map (fu k)).left
    ((Over.pullback p).map f).left ((Over.pullback p).map (vy k)).left at hp
  show IsClosedImmersion (pullback.snd ((Over.pullback p).map f).left
    ((Over.pullback p).map (vy k)).left)
  rw [← hp.isoPullback_inv_snd]
  have := H k
  infer_instance

/-- If a morphism over a stage is affine and locally of finite type and becomes a closed immersion
over the limit, it is a closed immersion at some later stage. -/
private lemma exists_isClosedImmersion_of_isAffineHom {I : Type v} [Category.{w} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i₀ : I) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (X Y : Over (D.obj i₀)) (f : X ⟶ Y)
    [CompactSpace Y.left] [IsAffineHom f.left] [LocallyOfFiniteType f.left]
    [IsClosedImmersion ((Over.pullback (c.π.app i₀)).map f).left] :
    ∃ A : Over i₀, IsClosedImmersion ((Over.pullback (D.map A.hom)).map f).left := by
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
      IsClosedImmersion ((Over.pullback (D.map A.hom)).map (fu k)).left := by
    have : IsAffine (YU k).left := inferInstanceAs (IsAffine (U.X k))
    have : IsAffine (XU k).left := IsAffine.of_isPullback (hpb k).flip
    have : LocallyOfFiniteType (fu k).left := by
      show LocallyOfFiniteType (pullback.snd f.left (U.f k))
      infer_instance
    have : IsClosedImmersion ((Over.pullback (c.π.app i₀)).map (fu k)).left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        ((hOver k).map (Over.pullback (c.π.app i₀) ⋙ Over.forget _))
        (show IsClosedImmersion ((Over.pullback (c.π.app i₀)).map f).left from inferInstance)
    exact exists_isClosedImmersion_affine_baseChange D c hc i₀ (XU k) (YU k) (fu k)
  choose A hA using hstage
  obtain ⟨⟨B, hB⟩⟩ :=
    exists_common_object_of_finset (Finset.univ : Finset U.I₀) (fun k => Opposite.op (A k))
  refine ⟨B.unop, isClosedImmersion_of_baseChange_cover (D.map B.unop.hom) f U XU fu vx
    hpb fun k => ?_⟩
  obtain ⟨g⟩ := hB k (Finset.mem_univ _)
  have h := overPullback_map_comp (@IsClosedImmersion) (D.map (A k).hom)
    (D.map g.unop.left) (fu k) (hA k)
  rwa [← D.map_comp, g.unop.w] at h

/-! ### Descending closed immersions -/

/-- If a morphism over a stage is locally of finite type and becomes a closed
immersion over the inverse limit, it becomes a closed immersion at a later stage. -/
@[stacks 01ZP]
theorem exists_isClosedImmersion_baseChange_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsClosedImmersion ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (hi : i ⟶ i₀),
      IsClosedImmersion ((Over.pullback (D.map hi)).map f₀).left := by
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
  have : IsClosedImmersion ((Over.pullback (c.π.app i₁)).map f₁).left := by
    apply (overPullback_map_comp_iff (@IsClosedImmersion) (D.map hi₁) (c.π.app i₁) f₀).mp
    rw [c.w hi₁]
    infer_instance
  obtain ⟨A, hA⟩ := exists_isClosedImmersion_of_isAffineHom D c hc i₁ X₁ Y₁ f₁
  refine ⟨A.left, A.hom ≫ hi₁, ?_⟩
  rw [D.map_comp]
  exact (overPullback_map_comp_iff (@IsClosedImmersion) (D.map hi₁) (D.map A.hom) f₀).mpr hA

end AlgebraicGeometry
