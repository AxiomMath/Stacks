module

public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.NoetherianModelOfProperFlat

/-!
# Noetherian models of a pair of morphisms of proper flat families

Let `S` be an affine scheme, let `X`, `Y₁`, `Y₂` be proper, flat schemes of finite presentation
over `S` and let `cᵢ : X ⟶ Yᵢ` be morphisms over `S`. Then the whole configuration is the base
change, along a morphism `S ⟶ S₀` to a Noetherian affine scheme, of a configuration of the same
kind over `S₀`. This is the reduction "we may assume `S` is Noetherian" in the proof of
[Stacks, Tag 0E89], assembled from [Stacks, Tag 01ZM] (models of the schemes, through
`AlgebraicGeometry.exists_isProper_finitePresentation_overPullbackObj_of_isLimit`, and of the
morphisms, through [Stacks, Tag 01ZC]) and [Stacks, Tag 04AI] (flatness).

## Main results

* `AlgebraicGeometry.C1590Private.exists_properFlat_stageModel`: a proper flat morphism of finite
  presentation over a cofiltered limit is the base change of one over a stage.
* `AlgebraicGeometry.C1590Private.exists_stageModel_hom`: a morphism between two such base changes
  descends to a later stage.
* `AlgebraicGeometry.C1590Private.exists_noetherianModel_pair`: the statement above.

## Implementation notes

A model at the stage `i` of a cone `c` over `E` is a cartesian square
`IsPullback g f f₀ (c.π.app i)`. Its base change to a later stage `e : j ⟶ i` is the fibre product
`pullback (E.map e) f₀` with its first projection, the orientation of
`AlgebraicGeometry.Scheme.baseChangeDiagram`, and the comparison morphism from the limit object is
`AlgebraicGeometry.C1590Private.stageLift`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

section Stage

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {E : I ⥤ Scheme.{u}} {c : Cone E}

/-- The comparison morphism from `X` to the base change `pullback (E.map e) f₀` of a model
`g : X ⟶ X₀` at the stage `i` to a later stage `e : j ⟶ i`. -/
def stageLift {X X₀ : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {f₀ : X₀ ⟶ E.obj i} {g : X ⟶ X₀}
    (sq : IsPullback g f f₀ (c.π.app i)) {j : I} (e : j ⟶ i) : X ⟶ pullback (E.map e) f₀ :=
  pullback.lift (f ≫ c.π.app j) g (by rw [Category.assoc, c.w e, sq.w])

omit [IsCofiltered I] in
/-- The first projection of `stageLift sq e` is `f ≫ c.π.app j`. -/
@[reassoc (attr := simp)]
theorem stageLift_fst {X X₀ : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {f₀ : X₀ ⟶ E.obj i}
    {g : X ⟶ X₀} (sq : IsPullback g f f₀ (c.π.app i)) {j : I} (e : j ⟶ i) :
    stageLift sq e ≫ pullback.fst (E.map e) f₀ = f ≫ c.π.app j :=
  pullback.lift_fst _ _ _

omit [IsCofiltered I] in
/-- The second projection of `stageLift sq e` is `g`. -/
@[reassoc (attr := simp)]
theorem stageLift_snd {X X₀ : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {f₀ : X₀ ⟶ E.obj i}
    {g : X ⟶ X₀} (sq : IsPullback g f f₀ (c.π.app i)) {j : I} (e : j ⟶ i) :
    stageLift sq e ≫ pullback.snd (E.map e) f₀ = g :=
  pullback.lift_snd _ _ _

omit [IsCofiltered I] in
/-- The base change of a model to a later stage is a model. -/
theorem isPullback_stageLift {X X₀ : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {f₀ : X₀ ⟶ E.obj i}
    {g : X ⟶ X₀} (sq : IsPullback g f f₀ (c.π.app i)) {j : I} (e : j ⟶ i) :
    IsPullback (stageLift sq e) f (pullback.fst (E.map e) f₀) (c.π.app j) := by
  refine IsPullback.of_right ?_ (stageLift_fst sq e) (IsPullback.of_hasPullback (E.map e) f₀).flip
  rw [stageLift_snd, c.w e]
  exact sq

omit [IsCofiltered I] in
/-- A property stable under base change passes from a model to its base change. -/
theorem prop_fst_stage (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {i j : I} (e : j ⟶ i) {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ E.obj i} (h : P f₀) :
    P (pullback.fst (E.map e) f₀) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback (E.map e) f₀).flip h

variable (E c) [∀ {i j : I} (e : i ⟶ j), IsAffineHom (E.map e)] [∀ i, CompactSpace (E.obj i)]
  [∀ i, QuasiSeparatedSpace (E.obj i)]

/-- **A proper flat morphism of finite presentation over a cofiltered limit comes from a stage**
([Stacks, Tags 01ZM and 04AI]). -/
theorem exists_properFlat_stageModel (hc : IsLimit c) {X : Scheme.{u}} (f : X ⟶ c.pt)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    ∃ (i : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ E.obj i) (g : X ⟶ X₀),
      IsProper f₀ ∧ Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧ IsPullback g f f₀ (c.π.app i) := by
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  obtain ⟨j, Xj, hXjfp, hXjprop, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit E c hc (Over.mk f) hfp
  have sqj : IsPullback (e.hom.left ≫ pullback.fst Xj.hom (c.π.app j)) f Xj.hom (c.π.app j) :=
    isPullback_left_fst_of_overIso Xj e
  have : LocallyOfFinitePresentation Xj.hom := hXjfp.1
  have : QuasiCompact Xj.hom := hXjfp.2.1
  have : QuasiSeparated Xj.hom := hXjfp.2.2
  have : CompactSpace Xj.left := QuasiCompact.compactSpace_of_compactSpace Xj.hom
  have : QuasiSeparatedSpace Xj.left := quasiSeparatedSpace_of_quasiSeparated Xj.hom
  let τ : Xj ⟶ Over.mk (𝟙 (E.obj j)) := Over.homMk Xj.hom (Category.comp_id _)
  have : LocallyOfFinitePresentation τ.left := hXjfp.1
  have : CompactSpace (Over.mk (𝟙 (E.obj j))).left := inferInstanceAs (CompactSpace (E.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (E.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (E.obj j))
  have : MorphismProperty.RespectsIso @Flat := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat ((Over.pullback (c.π.app j)).map τ).left := by
    rw [Stacks.AlgebraicGeometry.TopDegreeBaseChange.prop_overPullback_map_toTerminal_iff (@Flat)]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have hw : e.hom.left ≫ pullback.snd Xj.hom (c.π.app j) = f := by simpa using Over.w e.hom
    have h1 : Flat (e.hom.left ≫ pullback.snd Xj.hom (c.π.app j)) := by
      rw [hw]
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat) _ _).mp h1
  obtain ⟨k, b, hfl⟩ := exists_flat_baseChange_of_limitBaseChange E c j Xj
    (Over.mk (𝟙 (E.obj j))) τ hc
  rw [Stacks.AlgebraicGeometry.TopDegreeBaseChange.prop_overPullback_map_toTerminal_iff
    (@Flat)] at hfl
  have hsym : Flat (pullback.fst (E.map b) Xj.hom) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  exact ⟨k, pullback (E.map b) Xj.hom, pullback.fst (E.map b) Xj.hom, stageLift sqj b,
    prop_fst_stage @IsProper b hXjprop, hsym, prop_fst_stage @LocallyOfFinitePresentation b hXjfp.1,
    isPullback_stageLift sqj b⟩

/-- **A morphism between the base changes of two models descends to a later stage**
([Stacks, Tag 01ZC]). -/
theorem exists_stageModel_hom (hc : IsLimit c) {X Y X₀ Y₀ : Scheme.{u}} {fX : X ⟶ c.pt}
    {fY : Y ⟶ c.pt} {i : I} {fX₀ : X₀ ⟶ E.obj i} {fY₀ : Y₀ ⟶ E.obj i} {gX : X ⟶ X₀}
    {gY : Y ⟶ Y₀} (sqX : IsPullback gX fX fX₀ (c.π.app i)) (sqY : IsPullback gY fY fY₀ (c.π.app i))
    [QuasiCompact fX₀] [QuasiSeparated fX₀] [LocallyOfFinitePresentation fY₀]
    (h : X ⟶ Y) (hh : h ≫ fY = fX) :
    ∃ (j : I) (e : j ⟶ i) (h₀ : pullback (E.map e) fX₀ ⟶ pullback (E.map e) fY₀),
      h₀ ≫ pullback.fst (E.map e) fY₀ = pullback.fst (E.map e) fX₀ ∧
        stageLift sqX e ≫ h₀ = h ≫ stageLift sqY e := by
  let X' : Over (E.obj i) := Over.mk fX₀
  let D := Scheme.baseChangeDiagram E i X'
  let C := Scheme.baseChangeCone E i X' c
  have hpb : ∀ k : Over i, IsPullback (pullback.snd (E.map k.hom) X'.hom)
      (pullback.fst (E.map k.hom) X'.hom) X'.hom (E.map k.hom) := fun k =>
    (IsPullback.of_hasPullback (E.map k.hom) X'.hom).flip
  have : ∀ {k l : Over i} (a : k ⟶ l), IsAffineHom (D.map a) := fun a =>
    Scheme.isAffineHom_baseChangeDiagram_map E i X' a
  have : ∀ k : Over i, CompactSpace (D.obj k) := fun k => by
    have hq : QuasiCompact (pullback.fst (E.map k.hom) X'.hom) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) (hpb k) ‹QuasiCompact fX₀›
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (E.map k.hom) X'.hom) hq _
  have : ∀ k : Over i, QuasiSeparatedSpace (D.obj k) := fun k => by
    have hq : QuasiSeparated (pullback.fst (E.map k.hom) X'.hom) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) (hpb k) ‹QuasiSeparated fX₀›
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (E.map k.hom) X'.hom) _ hq
  have : EssentiallySmall.{u} (Over i) := Scheme.essentiallySmall_over i
  set ι := sqX.flip.isoPullback
  let Lk : ∀ k : Over i, pullback (c.π.app i) fX₀ ⟶ pullback (E.map k.hom) fX₀ :=
    fun k => C.π.app k
  have hL₁ : ∀ k : Over i, Lk k ≫ pullback.fst (E.map k.hom) fX₀ =
      pullback.fst (c.π.app i) fX₀ ≫ c.π.app k.left :=
    fun k => Scheme.baseChangeCone_π_fst E i X' c k
  have hL₂ : ∀ k : Over i, Lk k ≫ pullback.snd (E.map k.hom) fX₀ = pullback.snd (c.π.app i) fX₀ :=
    fun k => Scheme.baseChangeCone_π_snd E i X' c k
  have key : ∀ k : Over i, Lk k ≫ pullback.snd (E.map k.hom) fX₀ ≫ fX₀ =
      (ι.inv ≫ h ≫ gY) ≫ fY₀ := fun k => by
    rw [reassoc_of% (hL₂ k), Category.assoc, Category.assoc, sqY.w, reassoc_of% hh,
      IsPullback.isoPullback_inv_fst_assoc]
    exact pullback.condition.symm
  obtain ⟨k, g, hg, hgf⟩ := Scheme.exists_π_app_comp_eq_of_essentiallySmall D C
    (Scheme.isLimitBaseChangeCone E i X' c hc) (Scheme.baseChangeStructureMap E i X') fY₀
    (ι.inv ≫ h ≫ gY) (by ext k; exact key k)
  set L := Lk k
  let g' : pullback (E.map k.hom) fX₀ ⟶ Y₀ := g
  have hg' : g' ≫ fY₀ = pullback.snd (E.map k.hom) fX₀ ≫ fX₀ := hgf
  have hgC : L ≫ g' = ι.inv ≫ h ≫ gY := hg
  have hleg : ι.hom ≫ L = stageLift sqX k.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hL₁ k, IsPullback.isoPullback_hom_fst_assoc, stageLift_fst]
    · rw [Category.assoc, hL₂ k, IsPullback.isoPullback_hom_snd, stageLift_snd]
  have hw : pullback.fst (E.map k.hom) fX₀ ≫ E.map k.hom = g' ≫ fY₀ := by
    rw [hg']
    exact pullback.condition
  refine ⟨k.left, k.hom, pullback.lift (pullback.fst _ _) g' hw, pullback.lift_fst _ _ _, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, stageLift_fst, Category.assoc, stageLift_fst,
      reassoc_of% hh]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, stageLift_snd, ← hleg,
      Category.assoc, hgC, Iso.hom_inv_id_assoc]

/-- **A pair of morphisms out of a proper flat family into two others descends to a stage.** Let
`X`, `Y₁`, `Y₂` be proper, flat and of finite presentation over the limit `c.pt` and
`cᵢ : X ⟶ Yᵢ` morphisms over it. Then at some stage `j` there are models `X₀`, `Y₁₀`, `Y₂₀` with
the same properties and morphisms `cᵢ₀ : X₀ ⟶ Yᵢ₀` over `E.obj j` inducing the `cᵢ`. -/
theorem exists_stageModel_pair (hc : IsLimit c) {X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ c.pt)
    (fY₁ : Y₁ ⟶ c.pt) (fY₂ : Y₂ ⟶ c.pt) [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsProper fY₁] [Flat fY₁] [LocallyOfFinitePresentation fY₁] [IsProper fY₂] [Flat fY₂]
    [LocallyOfFinitePresentation fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX) :
    ∃ (j : I) (X₀ Y₁₀ Y₂₀ : Scheme.{u}) (fX₀ : X₀ ⟶ E.obj j) (fY₁₀ : Y₁₀ ⟶ E.obj j)
      (fY₂₀ : Y₂₀ ⟶ E.obj j) (gX : X ⟶ X₀) (gY₁ : Y₁ ⟶ Y₁₀) (gY₂ : Y₂ ⟶ Y₂₀)
      (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀),
      (IsProper fX₀ ∧ Flat fX₀ ∧ LocallyOfFinitePresentation fX₀) ∧
      (IsProper fY₁₀ ∧ Flat fY₁₀ ∧ LocallyOfFinitePresentation fY₁₀) ∧
      (IsProper fY₂₀ ∧ Flat fY₂₀ ∧ LocallyOfFinitePresentation fY₂₀) ∧
      IsPullback gX fX fX₀ (c.π.app j) ∧ IsPullback gY₁ fY₁ fY₁₀ (c.π.app j) ∧
      IsPullback gY₂ fY₂ fY₂₀ (c.π.app j) ∧ c₁₀ ≫ fY₁₀ = fX₀ ∧ c₂₀ ≫ fY₂₀ = fX₀ ∧
      c₁ ≫ gY₁ = gX ≫ c₁₀ ∧ c₂ ≫ gY₂ = gX ≫ c₂₀ := by
  obtain ⟨iX, X₀, fX₀, gX, hX₁, hX₂, hX₃, sqX⟩ := exists_properFlat_stageModel E c hc fX
  obtain ⟨i₁, Y₁₀, fY₁₀, gY₁, hY₁₁, hY₁₂, hY₁₃, sqY₁⟩ := exists_properFlat_stageModel E c hc fY₁
  obtain ⟨i₂, Y₂₀, fY₂₀, gY₂, hY₂₁, hY₂₂, hY₂₃, sqY₂⟩ := exists_properFlat_stageModel E c hc fY₂
  let k₁ := IsCofiltered.min iX i₁
  let k := IsCofiltered.min k₁ i₂
  let eX : k ⟶ iX := IsCofiltered.minToLeft k₁ i₂ ≫ IsCofiltered.minToLeft iX i₁
  let e₁ : k ⟶ i₁ := IsCofiltered.minToLeft k₁ i₂ ≫ IsCofiltered.minToRight iX i₁
  let e₂ : k ⟶ i₂ := IsCofiltered.minToRight k₁ i₂
  have sqXk := isPullback_stageLift sqX eX
  have sqY₁k := isPullback_stageLift sqY₁ e₁
  have sqY₂k := isPullback_stageLift sqY₂ e₂
  have : IsProper (pullback.fst (E.map eX) fX₀) := prop_fst_stage @IsProper eX hX₁
  have : LocallyOfFinitePresentation (pullback.fst (E.map e₁) fY₁₀) :=
    prop_fst_stage @LocallyOfFinitePresentation e₁ hY₁₃
  obtain ⟨j₁, d₁, h₁, hh₁, hc₁'⟩ := exists_stageModel_hom E c hc sqXk sqY₁k c₁ hc₁
  have sqX₂ := isPullback_stageLift sqXk d₁
  have sqY₁' := isPullback_stageLift sqY₁k d₁
  have sqY₂' := isPullback_stageLift sqY₂k d₁
  have : IsProper (pullback.fst (E.map d₁) (pullback.fst (E.map eX) fX₀)) :=
    prop_fst_stage @IsProper d₁ inferInstance
  have : LocallyOfFinitePresentation (pullback.fst (E.map d₁) (pullback.fst (E.map e₂) fY₂₀)) :=
    prop_fst_stage @LocallyOfFinitePresentation d₁
      (prop_fst_stage @LocallyOfFinitePresentation e₂ hY₂₃)
  obtain ⟨j₂, d₂, h₂, hh₂, hc₂'⟩ := exists_stageModel_hom E c hc sqX₂ sqY₂' c₂ hc₂
  have hP : ∀ {i : I} {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ E.obj i} (e : k ⟶ i),
      IsProper f₀ ∧ Flat f₀ ∧ LocallyOfFinitePresentation f₀ →
      let g := pullback.fst (E.map d₂) (pullback.fst (E.map d₁) (pullback.fst (E.map e) f₀))
      IsProper g ∧ Flat g ∧ LocallyOfFinitePresentation g := fun e h =>
    ⟨prop_fst_stage @IsProper d₂ (prop_fst_stage @IsProper d₁ (prop_fst_stage @IsProper e h.1)),
      prop_fst_stage @Flat d₂ (prop_fst_stage @Flat d₁ (prop_fst_stage @Flat e h.2.1)),
      prop_fst_stage @LocallyOfFinitePresentation d₂ (prop_fst_stage
        @LocallyOfFinitePresentation d₁ (prop_fst_stage @LocallyOfFinitePresentation e h.2.2))⟩
  let fX₂ := pullback.fst (E.map d₁) (pullback.fst (E.map eX) fX₀)
  let fY₁' := pullback.fst (E.map d₁) (pullback.fst (E.map e₁) fY₁₀)
  have hh₁' : h₁ ≫ fY₁' = fX₂ := hh₁
  let c₁₃ := pullback.map (E.map d₂) fX₂ (E.map d₂) fY₁' (𝟙 _) h₁ (𝟙 _) (by simp)
    (by rw [Category.comp_id, hh₁'])
  refine ⟨j₂, _, _, _, pullback.fst (E.map d₂) fX₂, pullback.fst (E.map d₂) fY₁',
    pullback.fst (E.map d₂) (pullback.fst (E.map d₁) (pullback.fst (E.map e₂) fY₂₀)),
    stageLift sqX₂ d₂, stageLift sqY₁' d₂, stageLift sqY₂' d₂, c₁₃, h₂,
    hP eX ⟨hX₁, hX₂, hX₃⟩,
    hP e₁ ⟨hY₁₁, hY₁₂, hY₁₃⟩,
    hP e₂ ⟨hY₂₁, hY₂₂, hY₂₃⟩, isPullback_stageLift sqX₂ d₂,
    isPullback_stageLift sqY₁' d₂, isPullback_stageLift sqY₂' d₂, ?_, hh₂, ?_, hc₂'.symm⟩
  · exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  · apply pullback.hom_ext
    · rw [Category.assoc, stageLift_fst, Category.assoc, pullback.lift_fst, Category.comp_id,
        stageLift_fst, reassoc_of% hc₁]
    · rw [Category.assoc, stageLift_snd, Category.assoc, pullback.lift_snd, stageLift_snd_assoc,
        hc₁']

end Stage

/-- **A pair of morphisms of proper flat families over an affine base has a Noetherian model.** Let
`S` be affine, `X`, `Y₁`, `Y₂` proper, flat and of finite presentation over `S` and `cᵢ : X ⟶ Yᵢ`
morphisms over `S`. Then there are a Noetherian affine scheme `S₀`, a morphism `π : S ⟶ S₀` and a
configuration `cᵢ₀ : X₀ ⟶ Yᵢ₀` of the same kind over `S₀` whose base change along `π` is the given
one. -/
theorem exists_noetherianModel_pair {S X Y₁ Y₂ : Scheme.{u}} [IsAffine S] (fX : X ⟶ S)
    (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S) [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsProper fY₁] [Flat fY₁] [LocallyOfFinitePresentation fY₁] [IsProper fY₂] [Flat fY₂]
    [LocallyOfFinitePresentation fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX) :
    ∃ (S₀ : Scheme.{u}) (π : S ⟶ S₀), IsNoetherian S₀ ∧ IsAffine S₀ ∧
    ∃ (X₀ Y₁₀ Y₂₀ : Scheme.{u}) (fX₀ : X₀ ⟶ S₀) (fY₁₀ : Y₁₀ ⟶ S₀)
      (fY₂₀ : Y₂₀ ⟶ S₀) (gX : X ⟶ X₀) (gY₁ : Y₁ ⟶ Y₁₀) (gY₂ : Y₂ ⟶ Y₂₀)
      (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀),
      (IsProper fX₀ ∧ Flat fX₀ ∧ LocallyOfFinitePresentation fX₀) ∧
      (IsProper fY₁₀ ∧ Flat fY₁₀ ∧ LocallyOfFinitePresentation fY₁₀) ∧
      (IsProper fY₂₀ ∧ Flat fY₂₀ ∧ LocallyOfFinitePresentation fY₂₀) ∧
      IsPullback gX fX fX₀ π ∧ IsPullback gY₁ fY₁ fY₁₀ π ∧ IsPullback gY₂ fY₂ fY₂₀ π ∧
      c₁₀ ≫ fY₁₀ = fX₀ ∧ c₂₀ ≫ fY₂₀ = fX₀ ∧ c₁ ≫ gY₁ = gX ≫ c₁₀ ∧ c₂ ≫ gY₂ = gX ≫ c₂₀ := by
  let c := (specAdjoinFinsetCone Γ(S, ⊤)).extend S.isoSpec.hom
  have hc : IsLimit c := IsLimit.ofIsoLimit (isLimit_specAdjoinFinsetCone Γ(S, ⊤))
    (Cone.extendIso (specAdjoinFinsetCone Γ(S, ⊤))
      (S.isoSpec.symm : (specAdjoinFinsetCone Γ(S, ⊤)).pt ≅ S))
  obtain ⟨j, X₀, Y₁₀, Y₂₀, fX₀, fY₁₀, fY₂₀, gX, gY₁, gY₂, c₁₀, c₂₀, h⟩ :=
    exists_stageModel_pair (specAdjoinFinsetDiagram Γ(S, ⊤)) c hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂
  exact ⟨_, c.π.app j, isNoetherian_specAdjoinFinsetDiagram_obj _ j,
    isAffine_specAdjoinFinsetDiagram_obj _ j, X₀, Y₁₀, Y₂₀, fX₀, fY₁₀, fY₂₀, gX, gY₁, gY₂, c₁₀,
    c₂₀, h⟩

end AlgebraicGeometry.C1590Private

end
