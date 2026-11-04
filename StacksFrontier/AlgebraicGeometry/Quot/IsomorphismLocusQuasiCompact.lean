module

public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusStage
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.NoetherianChow
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The isomorphism locus of a proper flat family is quasi-compact

Let `k : W ⟶ V` be a morphism over a quasi-compact quasi-separated scheme `T`, with `W ⟶ T` flat,
proper and of finite presentation and `V ⟶ T` proper and of finite presentation.  The open
subscheme of `T` over which `k` becomes an isomorphism (Stacks 05XD) is quasi-compact: by absolute
Noetherian approximation (Stacks 01ZA) the data descend to a Noetherian scheme `T_j`
(Stacks 01ZM, 04AI, 01ZQ, 081F), where the isomorphism locus is quasi-compact, and it pulls back to
the isomorphism locus over `T` along the affine morphism `T ⟶ T_j`.

This is the quasi-compactness of the locus of graphs inside the Hilbert functor used in the proof
of Stacks 0DPR.

## Main results

* `AlgebraicGeometry.IsoLocus.isCompact_of_forall_range_subset_iff_isIso`.

## References

* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsoLocus

section Helpers

variable {C D : Type*} [Category C] [Category D]

/-- A natural isomorphism of functors identifies the arrows they send a morphism to. -/
def arrowIsoOfNatIso {F G : C ⥤ D} (α : F ≅ G) {X Y : C} (m : X ⟶ Y) :
    Arrow.mk (F.map m) ≅ Arrow.mk (G.map m) :=
  Arrow.isoMk (α.app X) (α.app Y) (α.hom.naturality m).symm

end Helpers

/-- The base change of `X ⟶ Y` along `g`, read through the morphism to the terminal object of
`Over Y`, has a property exactly when the structure morphism of the base change does. -/
theorem over_pullback_map_toTerminal_left_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Y Y' : Scheme.{u}} (X : Over Y) (g : Y' ⟶ Y) :
    P ((Over.pullback g).map (Over.homMk X.hom (Category.comp_id _) :
        X ⟶ Over.mk (𝟙 Y))).left ↔ P ((Over.pullback g).obj X).hom := by
  rw [← P.cancel_right_of_respectsIso _ (pullback.snd (𝟙 Y) g)]
  have : ((Over.pullback g).map (Over.homMk X.hom (Category.comp_id _) :
      X ⟶ Over.mk (𝟙 Y))).left ≫ pullback.snd (𝟙 Y) g = ((Over.pullback g).obj X).hom :=
    pullback.lift_snd _ _ _
  rw [this]

/-- A property of the structure morphism transfers along an isomorphism in `Over Y`. -/
theorem over_hom_iff_of_iso (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {Y : Scheme.{u}}
    {X X' : Over Y} (e : X ≅ X') : P X.hom ↔ P X'.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Y).map e.hom))
  rw [← Over.w e.hom]
  exact P.cancel_left_of_respectsIso e.hom.left X'.hom


/-- A property of the structure morphism of the base change of `X` along `g` transfers to the base
change of the morphism from `X` to the terminal object of `Over Y`. -/
private theorem pullback_map_toTerminal_left_of_iso (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {Y Y' Z : Scheme.{u}} (g : Y' ⟶ Y) (X : Over Y) {t : Z ⟶ Y'}
    (eX : (Over.pullback g).obj X ≅ Over.mk t) (h : P t) :
    P ((Over.pullback g).map (Over.homMk X.hom (Category.comp_id _) :
      X ⟶ Over.mk (𝟙 Y))).left :=
  (over_pullback_map_toTerminal_left_iff P X g).2 ((over_hom_iff_of_iso P eX).2 h)

section Approximation

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
  (c : Cone D) (hc : IsLimit c) [∀ {i j : J} (v : i ⟶ j), IsAffineHom (D.map v)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- Base change along equal morphisms. -/
noncomputable def overPullbackCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    Over.pullback f ≅ Over.pullback g := by
  subst h
  exact Iso.refl _

/-- Base change to the limit through a later stage is base change to the limit. -/
noncomputable def stageShift {j j' : J} (e : j' ⟶ j) :
    Over.pullback (D.map e) ⋙ Over.pullback (c.π.app j') ≅ Over.pullback (c.π.app j) :=
  (Over.pullbackComp (c.π.app j') (D.map e)).symm ≪≫ overPullbackCongr (c.w e)

variable {W V : Scheme.{u}} {a : W ⟶ c.pt} {b : V ⟶ c.pt} (k' : Over.mk a ⟶ Over.mk b)

/-- A model of `k'` at the stage `j`: a morphism of schemes of finite presentation over `D j`
whose base change to the limit is `k'` up to isomorphism. -/
def IsStageModel (j : J) {X Y : Over (D.obj j)} (g : X ⟶ Y) : Prop :=
  FinitePresentation X.hom ∧ FinitePresentation Y.hom ∧
    Nonempty (Arrow.mk ((Over.pullback (c.π.app j)).map g) ≅ Arrow.mk k')

variable {D c k'}

/-- The base change of an object of `Over Y` of finite presentation along `f : Y' ⟶ Y` is of
finite presentation over `Y'`. -/
theorem finitePresentation_pullback_obj_hom {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (X : Over Y)
    (h : FinitePresentation X.hom) : FinitePresentation ((Over.pullback f).obj X).hom := by
  have : LocallyOfFinitePresentation X.hom := h.1
  have : QuasiCompact X.hom := h.2.1
  have : QuasiSeparated X.hom := h.2.2
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom f)),
    inferInstanceAs (QuasiCompact (pullback.snd X.hom f)),
    inferInstanceAs (QuasiSeparated (pullback.snd X.hom f))⟩

omit [IsCofiltered J] [∀ {i j : J} (v : i ⟶ j), IsAffineHom (D.map v)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- A model of `k'` at the stage `j` base changes to a model of `k'` at every later stage `j'`. -/
theorem IsStageModel.shift {j j' : J} (e : j' ⟶ j) {X Y : Over (D.obj j)} {g : X ⟶ Y}
    (h : IsStageModel D c k' j g) :
    IsStageModel D c k' j' ((Over.pullback (D.map e)).map g) :=
  ⟨finitePresentation_pullback_obj_hom _ _ h.1, finitePresentation_pullback_obj_hom _ _ h.2.1,
    ⟨arrowIsoOfNatIso (stageShift D c e) g ≪≫ h.2.2.some⟩⟩

include hc in
/-- A morphism `k'` between schemes of finite presentation over the limit `c.pt` has a model at
some stage (Stacks 01ZM). -/
theorem exists_isStageModel (ha : FinitePresentation a) (hb : FinitePresentation b) :
    ∃ (j : J) (X Y : Over (D.obj j)) (g : X ⟶ Y), IsStageModel D c k' j g := by
  obtain ⟨i₁, W₁, hW₁, ⟨eW₁⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk a) ha
  obtain ⟨i₂, V₁, hV₁, ⟨eV₁⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk b) hb
  let e₁ := IsCofiltered.minToLeft i₁ i₂
  let e₂ := IsCofiltered.minToRight i₁ i₂
  let W₀ := (Over.pullback (D.map e₁)).obj W₁
  let V₀ := (Over.pullback (D.map e₂)).obj V₁
  have hW₀ : FinitePresentation W₀.hom := finitePresentation_pullback_obj_hom _ _ hW₁
  have hV₀ : FinitePresentation V₀.hom := finitePresentation_pullback_obj_hom _ _ hV₁
  let eW : Over.mk a ≅ (Over.pullback (c.π.app (IsCofiltered.min i₁ i₂))).obj W₀ :=
    eW₁ ≪≫ ((stageShift D c e₁).app W₁).symm
  let eV : Over.mk b ≅ (Over.pullback (c.π.app (IsCofiltered.min i₁ i₂))).obj V₀ :=
    eV₁ ≪≫ ((stageShift D c e₂).app V₁).symm
  obtain ⟨j, e, g, α, β, -, -, hαβ⟩ := _root_.AlgebraicGeometry.exists_morphism_after_baseChange
    D c hc _ W₀ V₀ hW₀ hV₀ (eW.inv ≫ k' ≫ eV.hom)
  refine ⟨j, _, _, g, finitePresentation_pullback_obj_hom _ _ hW₀,
    finitePresentation_pullback_obj_hom _ _ hV₀,
    ⟨Arrow.isoMk (α ≪≫ eW.symm) (β ≪≫ eV.symm) ?_⟩⟩
  have := hαβ =≫ eV.inv
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at this
  simpa using this

/-- A property of morphisms stable under base change passes from the structure morphism of an
object of `Over Y` to that of its base change along `f : Y' ⟶ Y`. -/
theorem pullback_obj_hom_of {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) {X : Over Y} (h : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  P.pullback_snd _ _ h

section ObjectDescent

variable {j : J} (X : Over (D.obj j)) (hX : FinitePresentation X.hom) {Z : Scheme.{u}}
  {t : Z ⟶ c.pt} (eX : (Over.pullback (c.π.app j)).obj X ≅ Over.mk t)

include hc hX eX in
/-- If the base change to the limit of a scheme `X` of finite presentation over the stage `j` is
flat over `c.pt`, then `X` becomes flat after base change to some later stage (Stacks 04AI). -/
theorem exists_flat_of_iso [Flat t] :
    ∃ (j' : J) (e : j' ⟶ j), Flat ((Over.pullback (D.map e)).obj X).hom := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let f₀ : X ⟶ Over.mk (𝟙 (D.obj j)) := Over.homMk X.hom (Category.comp_id _)
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat ((Over.pullback (c.π.app j)).map f₀).left := by
    exact pullback_map_toTerminal_left_of_iso (@Flat) _ X eX ‹Flat t›
  have : LocallyOfFinitePresentation f₀.left := ‹LocallyOfFinitePresentation X.hom›
  have : CompactSpace (Over.mk (𝟙 (D.obj j))).left := inferInstanceAs (CompactSpace (D.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  obtain ⟨j', e, he⟩ := exists_flat_baseChange_of_limitBaseChange D c j X _ f₀ hc
  exact ⟨j', e, (over_pullback_map_toTerminal_left_iff (@Flat) X (D.map e)).1 he⟩

include hc hX eX in
/-- If the base change to the limit of a scheme `X` of finite presentation over the stage `j` is
separated over `c.pt`, then `X` becomes separated after base change to some later stage
(Stacks 01ZQ). -/
theorem exists_isSeparated_of_iso [IsSeparated t] :
    ∃ (j' : J) (e : j' ⟶ j), IsSeparated ((Over.pullback (D.map e)).obj X).hom := by
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let f₀ : X ⟶ Over.mk (𝟙 (D.obj j)) := Over.homMk X.hom (Category.comp_id _)
  have : MorphismProperty.RespectsIso (@IsSeparated : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsSeparated ((Over.pullback (c.π.app j)).map f₀).left := by
    exact pullback_map_toTerminal_left_of_iso (@IsSeparated) _ X eX ‹IsSeparated t›
  have : CompactSpace (Over.mk (𝟙 (D.obj j))).left := inferInstanceAs (CompactSpace (D.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  obtain ⟨j', e, he⟩ := exists_isSeparated_baseChange_of_isLimit D c j X _ f₀ hc
  exact ⟨j', e, (over_pullback_map_toTerminal_left_iff (@IsSeparated) X (D.map e)).1 he⟩

include hc hX eX in
/-- If the base change to the limit of a separated scheme `X` of finite presentation over the
Noetherian stage `j` is proper over `c.pt`, then `X` becomes proper after base change to some
later stage (Stacks 081F). -/
theorem exists_isProper_of_iso [IsNoetherian (D.obj j)] [IsSeparated X.hom] [IsProper t] :
    ∃ (j' : J) (e : j' ⟶ j), IsProper ((Over.pullback (D.map e)).obj X).hom := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let f₀ : X ⟶ Over.mk (𝟙 (D.obj j)) := Over.homMk X.hom (Category.comp_id _)
  have : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsProper ((Over.pullback (c.π.app j)).map f₀).left := by
    exact pullback_map_toTerminal_left_of_iso (@IsProper) _ X eX ‹IsProper t›
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X.hom)
  have : IsSeparated f₀.left := ‹IsSeparated X.hom›
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  have : IsNoetherian (Over.mk (𝟙 (D.obj j))).left := ‹IsNoetherian (D.obj j)›
  obtain ⟨j', e, he⟩ := exists_isProper_baseChange_of_isLimit_of_isNoetherian D c hc j X _ f₀
  exact ⟨j', e, (over_pullback_map_toTerminal_left_iff (@IsProper) X (D.map e)).1 he⟩

end ObjectDescent

include hc in
/-- Over Noetherian stages, a morphism `k'` from a flat proper scheme of finite presentation over
`c.pt` to a proper scheme of finite presentation over `c.pt` has a model at some stage whose
source is flat and proper and whose target is proper. -/
theorem exists_isStageModel_flat_proper [∀ i, IsNoetherian (D.obj i)]
    (ha : FinitePresentation a) (hb : FinitePresentation b) [Flat a] [IsProper a] [IsProper b] :
    ∃ (j : J) (X Y : Over (D.obj j)) (g : X ⟶ Y), IsStageModel D c k' j g ∧ Flat X.hom ∧
      IsProper X.hom ∧ IsProper Y.hom := by
  obtain ⟨j₀, X₀, Y₀, g₀, h₀⟩ := exists_isStageModel (k' := k') hc ha hb
  obtain ⟨j₁, e₁, hfl₁⟩ := exists_flat_of_iso hc X₀ h₀.1 (Arrow.leftFunc.mapIso h₀.2.2.some)
  have h₁ := h₀.shift e₁
  obtain ⟨j₂, e₂, hsX₂⟩ :=
    exists_isSeparated_of_iso hc _ h₁.1 (Arrow.leftFunc.mapIso h₁.2.2.some)
  have h₂ := h₁.shift e₂
  have hfl₂ := pullback_obj_hom_of (P := @Flat) (D.map e₂) hfl₁
  obtain ⟨j₃, e₃, hsY₃⟩ :=
    exists_isSeparated_of_iso hc _ h₂.2.1 (Arrow.rightFunc.mapIso h₂.2.2.some)
  have h₃ := h₂.shift e₃
  have hfl₃ := pullback_obj_hom_of (P := @Flat) (D.map e₃) hfl₂
  have hsX₃ := pullback_obj_hom_of (P := @IsSeparated) (D.map e₃) hsX₂
  obtain ⟨j₄, e₄, hpX₄⟩ :=
    exists_isProper_of_iso hc _ h₃.1 (Arrow.leftFunc.mapIso h₃.2.2.some)
  have h₄ := h₃.shift e₄
  have hfl₄ := pullback_obj_hom_of (P := @Flat) (D.map e₄) hfl₃
  have hsY₄ := pullback_obj_hom_of (P := @IsSeparated) (D.map e₄) hsY₃
  obtain ⟨j₅, e₅, hpY₅⟩ :=
    exists_isProper_of_iso hc _ h₄.2.1 (Arrow.rightFunc.mapIso h₄.2.2.some)
  exact ⟨j₅, _, _, _, h₄.shift e₅, pullback_obj_hom_of (P := @Flat) _ hfl₄,
    pullback_obj_hom_of (P := @IsProper) _ hpX₄, hpY₅⟩

end Approximation


/-- An isomorphism after base change in `Over` is an isomorphism of the underlying pullbacks. -/
theorem isIso_over_pullback_map_iff {T T' : Scheme.{u}} (g' : T' ⟶ T) {A A' : Over T}
    (m : A ⟶ A') :
    IsIso ((Over.pullback g').map m) ↔
      IsIso (pullback.lift (f := A'.hom) (g := g') (pullback.fst A.hom g' ≫ m.left)
        (pullback.snd A.hom g') (by rw [Category.assoc, Over.w m, pullback.condition])) := by
  constructor
  · intro h
    exact inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback g').map m)))
  · intro h
    have : IsIso ((Over.forget _).map ((Over.pullback g').map m)) := h
    exact isIso_of_reflects_iso _ (Over.forget _)

/-- **The isomorphism locus of a proper flat family is quasi-compact.**  Let `k : W ⟶ V` be a
morphism over a quasi-compact quasi-separated scheme `T` of the big fppf site, with `W ⟶ T` flat,
proper and of finite presentation and `V ⟶ T` proper and of finite presentation, and let `U` be the
open subscheme of `T` over which `k` becomes an isomorphism (tested on the schemes of the site).
Then `U` is quasi-compact.

By absolute Noetherian approximation (Stacks 01ZA) `T` is the limit of Noetherian schemes `T_j`
with affine transition morphisms; `W`, `V`, `k` descend to some `T_j` (Stacks 01ZM), together with
flatness (Stacks 04AI), separatedness (Stacks 01ZQ) and properness (Stacks 081F over the
Noetherian `T_j`).  The isomorphism locus `U_j ⊆ T_j` of the descended morphism (Stacks 05XD)
pulls back to `U`, since both are characterised by the same test morphisms, and `U_j` is
quasi-compact because `T_j` is Noetherian, so `U` is quasi-compact because `T ⟶ T_j` is affine. -/
theorem isCompact_of_forall_range_subset_iff_isIso (B : BigFppfSite.{u}) {T W V : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T] (hT : B.Contains T) (a : W ⟶ T) (b : V ⟶ T)
    (k : W ⟶ V) (hk : k ≫ b = a) (ha : FinitePresentation a) [Flat a] [IsProper a]
    (hb : FinitePresentation b) [IsProper b] (U : T.Opens)
    (hU : ∀ (T' : Scheme.{u}) (_ : B.Contains T') (g : T' ⟶ T),
      Set.range g ⊆ U ↔ IsIso (pullback.lift (f := b) (g := g) (pullback.fst a g ≫ k)
        (pullback.snd a g) (by rw [Category.assoc, hk, pullback.condition]))) :
    IsCompact (U : Set T) := by
  obtain ⟨I, _, _, _, D, c, haff, hft, hqc, hnoeth, hcpt, hqs, ⟨hc⟩, rfl⟩ :=
    exists_isLimit_finiteType_isNoetherian T
  have : ∀ {i j : Iᵒᵖ} (v : i ⟶ j), IsAffineHom (D.map v) := haff
  have := hcpt
  have := hqs
  have := hnoeth
  let k' : Over.mk a ⟶ Over.mk b := Over.homMk k hk
  obtain ⟨j, X, Y, g, hmod, hfl, hpX, hpY⟩ := exists_isStageModel_flat_proper (k' := k') hc ha hb
  have : LocallyOfFiniteType (terminal.from (D.obj j)) := hft j
  have : QuasiCompact (terminal.from (D.obj j)) := hqc j
  have hTj : B.Contains (D.obj j) :=
    lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (terminal.from _))
      (by rw [Scheme.size_terminal]; exact B.aleph0_lt_cutoff)
  have : LocallyOfFinitePresentation X.hom := hmod.1.1
  have : QuasiCompact X.hom := hmod.1.2.1
  have : LocallyOfFinitePresentation Y.hom := hmod.2.1.1
  have : QuasiCompact Y.hom := hmod.2.1.2.1
  have hXj : B.Contains X.left :=
    lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact X.hom) hTj
  have hYj : B.Contains Y.left :=
    lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact Y.hom) hTj
  obtain ⟨Uj, hUj⟩ := Space.exists_opens_range_subset_iff_isIso_pullbackLift B hTj hXj hYj
    X.hom Y.hom g.left (Over.w g)
  have key : ∀ {T' : Scheme.{u}} (g' : T' ⟶ c.pt),
      IsIso (pullback.lift (f := b) (g := g') (pullback.fst a g' ≫ k) (pullback.snd a g')
        (by rw [Category.assoc, hk, pullback.condition])) ↔
      IsIso (pullback.lift (f := Y.hom) (g := g' ≫ c.π.app j)
        (pullback.fst X.hom (g' ≫ c.π.app j) ≫ g.left) (pullback.snd X.hom (g' ≫ c.π.app j))
        (by rw [Category.assoc, Over.w g, pullback.condition])) := by
    intro T' g'
    refine (isIso_over_pullback_map_iff g' k').symm.trans
      (Iff.trans ?_ (isIso_over_pullback_map_iff (g' ≫ c.π.app j) g))
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      ((Over.pullback g').mapArrow.mapIso hmod.2.2.some)).symm.trans
      (NatIso.isIso_map_iff (Over.pullbackComp g' (c.π.app j)) g).symm
  have hset : (U : Set c.pt) = c.π.app j ⁻¹' (Uj : Set (D.obj j)) := by
    ext x
    constructor
    · intro hx
      have hUc : B.Contains U := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion U.ι) hT
      have h1 := (hU U hUc U.ι).1 (by rw [Scheme.Opens.range_ι])
      exact (hUj U hUc (U.ι ≫ c.π.app j)).2 ((key U.ι).1 h1) ⟨⟨x, hx⟩, rfl⟩
    · intro hx
      let U' := (c.π.app j) ⁻¹ᵁ Uj
      have hUc' : B.Contains U' := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion U'.ι) hT
      have h1 := (hUj U' hUc' (U'.ι ≫ c.π.app j)).1 (by
        rintro _ ⟨y, rfl⟩
        exact y.2)
      exact (hU U' hUc' U'.ι).2 ((key U'.ι).2 h1) ⟨⟨x, hx⟩, rfl⟩
  rw [hset]
  have : IsAffineHom (c.π.app j) := isAffineHom_π_app D c hc j
  exact (c.π.app j).isCompact_preimage (U := Uj) (TopologicalSpace.NoetherianSpace.isCompact _)

end AlgebraicGeometry.IsoLocus
