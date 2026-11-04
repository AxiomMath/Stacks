module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.ProperFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.AffineModel

/-!
# Properness of a morphism to a limit at a finite stage

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact and quasi-separated schemes over a base
scheme `S` with affine transition morphisms. A proper morphism `Y ⟶ X` whose source is locally of
finite type over `S` is already proper over `Xᵢ` for every sufficiently late stage `i`.

## Main results

* `AlgebraicGeometry.eventually_isProper_comp_π_app_of_isLimit`: **Stacks 0EX1**.
* `AlgebraicGeometry.exists_isProper_finitePresentation_overPullbackObj_of_isLimit`: a proper
  morphism of finite presentation over the limit is the base change of a proper morphism of
  finite presentation over a stage, the isomorphism included. This is the quasi-compact
  quasi-separated counterpart of
  `AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`, which asks the stages
  to be Noetherian.
* `AlgebraicGeometry.exists_isProper_overPullbackObj_of_isLimit` and
  `AlgebraicGeometry.exists_isSeparated_overPullbackObj_of_isLimit`: [Stacks, Tag 081F] and
  [Stacks, Tag 01ZQ] for the structure morphism of an object over a stage.

## Implementation notes

The route is the Stacks proof. [Stacks, Tag 09ZR] factors `Y ⟶ X` as a closed immersion into a
morphism `Y' ⟶ X` which is proper and of finite presentation; part (1) of [Stacks, Tag 01ZM]
descends `Y'` to a scheme of finite presentation over a stage, [Stacks, Tag 01ZQ] makes that model
separated over a later stage and [Stacks, Tag 081F] makes it proper over a later stage still; and
[Stacks, Tag 081B] part (1) then makes `Y ⟶ Y'ᵢ` a closed immersion for `i` large, so that
`Y ⟶ Xᵢ` factors as a closed immersion followed by a proper morphism.

The system of base changes of the model along the transition morphisms is
`AlgebraicGeometry.baseChangeDiagram`, whose limit is the base change of the model to `X`. Tag
081B is stated for a system indexed by the opposite of a directed preorder, while that diagram is
indexed by the cofiltered over category of a stage;
`AlgebraicGeometry.exists_directed_cofinal_over` supplies the directed cofinal reindexing, and the
conclusion is transported back along it, a cofinal reindexing of an inverse system having the same
limit.

Three auxiliary statements are proved here rather than reused because the available forms tie the
index category to the universe of the schemes: `exists_isSeparated_overPullbackObj_of_isLimit` is
`AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit` with the index category allowed to
live in its own universe, and `overPullbackObjTransitionIso` is
`AlgebraicGeometry.overPullbackObj_shiftIso` likewise. The index hypothesis used instead is
`CategoryTheory.EssentiallySmall.{u} I`, which is what [Stacks, Tag 081F] and part (1) of
[Stacks, Tag 01ZM] carry.

Chow's lemma over a quasi-compact quasi-separated base enters through
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep`, whose
single-affine-step hypothesis is discharged by
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep`; no Noetherian hypothesis
on the stages is needed.

## References

* [Stacks Project, Tag 0EX1](https://stacks.math.columbia.edu/tag/0EX1)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe v u

namespace AlgebraicGeometry

/-! ### Descending the structure morphism of an object over a stage -/

/-- Base changing a scheme over a stage to the limit is base changing it along a transition
morphism and then to the limit. -/
def overPullbackObjTransitionIso {I : Type v} [Category.{v} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) {i j : I} (a : j ⟶ i) (Z : Over (D.obj i)) :
    (Over.pullback (c.π.app i)).obj Z ≅
      (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map a)).obj Z) :=
  (eqToIso (by rw [c.w a]) :
      (Over.pullback (c.π.app i)).obj Z ≅ (Over.pullback (c.π.app j ≫ D.map a)).obj Z) ≪≫
    (Over.pullbackComp (c.π.app j) (D.map a)).app Z

/-- The source of a morphism of finite presentation over a quasi-compact quasi-separated scheme is
quasi-compact and quasi-separated. -/
private theorem compactSpace_and_quasiSeparatedSpace_left_of_finitePresentation {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (Z : Over X) (hZ : FinitePresentation Z.hom) :
    CompactSpace Z.left ∧ QuasiSeparatedSpace Z.left :=
  have : QuasiCompact Z.hom := hZ.2.1
  have : QuasiSeparated Z.hom := hZ.2.2
  ⟨QuasiCompact.compactSpace_of_compactSpace Z.hom, quasiSeparatedSpace_of_quasiSeparated Z.hom⟩

/-- **[Stacks, Tag 01ZQ] for the structure morphism of an object over a stage.** Let `D` be a
cofiltered inverse system of quasi-compact quasi-separated schemes with affine transition
morphisms and limit cone `c`, and let `Z` be a quasi-compact quasi-separated scheme over the stage
`D.obj i₀`. If the base change of `Z` to the limit is separated over the limit, then the base
change of `Z` to `D.obj i` is separated over `D.obj i` for some later stage `i`. -/
theorem exists_isSeparated_overPullbackObj_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) (Z : Over (D.obj i₀))
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    [IsSeparated ((Over.pullback (c.π.app i₀)).obj Z).hom] :
    ∃ (i : I) (g : i ⟶ i₀), IsSeparated ((Over.pullback (D.map g)).obj Z).hom := by
  let τ : Z ⟶ Over.mk (𝟙 (D.obj i₀)) := Over.homMk Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (CompactSpace (D.obj i₀))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  have : IsSeparated ((Over.pullback (c.π.app i₀)).map τ).left :=
    (overPullback_map_terminal_iff (@IsSeparated) _ Z).mpr ‹_›
  obtain ⟨i, g, hsep⟩ :=
    exists_isSeparated_baseChange_of_isLimit D c i₀ Z (Over.mk (𝟙 (D.obj i₀))) τ hc
  exact ⟨i, g, (overPullback_map_terminal_iff (@IsSeparated) _ Z).mp hsep⟩

/-- **[Stacks, Tag 081F] for the structure morphism of an object over a stage.** Let `D` be a
cofiltered inverse system with affine transition morphisms and limit cone `c`, let the stage
`D.obj i₀` be quasi-compact and quasi-separated, and let `Z` be separated and of finite
presentation over it. If the base change of `Z` to the limit is proper over the limit, then the
base change of `Z` to `D.obj i` is proper over `D.obj i` for some later stage `i`.

Chow's lemma over a quasi-compact quasi-separated base is what removes the Noetherian hypothesis
that `AlgebraicGeometry.exists_isProper_overPullbackObj_of_isLimit_of_isNoetherian` carries. -/
@[sga "4 VII 5.4" "partial"]
theorem exists_isProper_overPullbackObj_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) (Z : Over (D.obj i₀))
    (hZ : FinitePresentation Z.hom) [IsSeparated Z.hom]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [IsProper ((Over.pullback (c.π.app i₀)).obj Z).hom] :
    ∃ (i : I) (g : i ⟶ i₀), IsProper ((Over.pullback (D.map g)).obj Z).hom := by
  have : LocallyOfFinitePresentation Z.hom := hZ.1
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_left_of_finitePresentation Z hZ
  let τ : Z ⟶ Over.mk (𝟙 (D.obj i₀)) := Over.homMk Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (CompactSpace (D.obj i₀))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  have : LocallyOfFiniteType τ.left := inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : IsSeparated τ.left := inferInstanceAs (IsSeparated Z.hom)
  have : IsProper ((Over.pullback (c.π.app i₀)).map τ).left :=
    (overPullback_map_terminal_iff (@IsProper) _ Z).mpr ‹_›
  obtain ⟨i, g, hproper⟩ :=
    exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep
      Scheme.FiniteTypeApproximation.isOneAffineOpenStep D c hc i₀ Z
      (Over.mk (𝟙 (D.obj i₀))) τ
  exact ⟨i, g, (overPullback_map_terminal_iff (@IsProper) _ Z).mp hproper⟩

/-- **A proper morphism of finite presentation over a cofiltered limit of quasi-compact
quasi-separated schemes has a proper model of finite presentation over a stage, and the source is
its base change.** Let `D` be a cofiltered inverse system of quasi-compact quasi-separated schemes
with affine transition morphisms and limit cone `c`, and let `X` be proper and of finite
presentation over `c.pt`. Then there are a stage `j` and a scheme `Xⱼ` over `D.obj j`, proper and
of finite presentation over it, together with an isomorphism
`X ≅ (Over.pullback (c.π.app j)).obj Xⱼ` over `c.pt`.

Part (1) of [Stacks, Tag 01ZM] produces a model of finite presentation,
`AlgebraicGeometry.exists_isSeparated_overPullbackObj_of_isLimit` makes it separated at a later
stage and `AlgebraicGeometry.exists_isProper_overPullbackObj_of_isLimit` makes it proper at a
later stage still; each replacement of the model by its base change along a transition keeps
finite presentation and keeps the isomorphism with `X`. -/
@[ega "IV 8.8.3" "essential surjectivity"]
theorem exists_isProper_finitePresentation_overPullbackObj_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (X : Over c.pt) [IsProper X.hom]
    (hX : FinitePresentation X.hom) :
    ∃ (j : I) (Xⱼ : Over (D.obj j)), FinitePresentation Xⱼ.hom ∧ IsProper Xⱼ.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  obtain ⟨i, Xᵢ, hXᵢ, ⟨e⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc X hX
  have : LocallyOfFinitePresentation Xᵢ.hom := hXᵢ.1
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_left_of_finitePresentation Xᵢ hXᵢ
  have : IsSeparated ((Over.pullback (c.π.app i)).obj Xᵢ).hom :=
    prop_of_overIso (@IsSeparated) e inferInstance
  obtain ⟨j₁, a, hsep₁⟩ := exists_isSeparated_overPullbackObj_of_isLimit D c hc i Xᵢ
  have hfp₁ : FinitePresentation ((Over.pullback (D.map a)).obj Xᵢ).hom :=
    finitePresentation_overPullbackObj _ Xᵢ hXᵢ
  let e₁ : X ≅ (Over.pullback (c.π.app j₁)).obj ((Over.pullback (D.map a)).obj Xᵢ) :=
    e ≪≫ overPullbackObjTransitionIso D c a Xᵢ
  have : IsSeparated ((Over.pullback (D.map a)).obj Xᵢ).hom := hsep₁
  have : IsProper ((Over.pullback (c.π.app j₁)).obj
      ((Over.pullback (D.map a)).obj Xᵢ)).hom := isProper_hom_of_overIso e₁
  obtain ⟨j₂, b, hproper₂⟩ :=
    exists_isProper_overPullbackObj_of_isLimit D c hc j₁ ((Over.pullback (D.map a)).obj Xᵢ) hfp₁
  exact ⟨j₂, (Over.pullback (D.map b)).obj ((Over.pullback (D.map a)).obj Xᵢ),
    finitePresentation_overPullbackObj _ _ hfp₁, hproper₂,
    ⟨e₁ ≪≫ overPullbackObjTransitionIso D c b ((Over.pullback (D.map a)).obj Xᵢ)⟩⟩

/-! ### The eventual closed immersion into a system of base changes -/

/-- **[Stacks, Tag 081B] part (1) for a system of base changes.** Let `D` be a cofiltered inverse
system with affine transition morphisms and limit cone `c`, and let `Z` be a quasi-compact scheme
over the stage `D.obj i₀`. A closed immersion of a scheme `Y` into the base change of `Z` to the
limit, with `Y` locally of finite type over the base `S` of the system, is already a closed
immersion into the base change of `Z` to some later stage.

Tag 081B is stated for an inverse system indexed by the opposite of a directed preorder, and
`AlgebraicGeometry.exists_directed_cofinal_over` reindexes the over category of `i₀` by one. -/
theorem exists_isClosedImmersion_comp_baseChangeCone_π_app
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    {S : Scheme.{u}} (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) (Z : Over (D.obj i₀))
    [CompactSpace (D.obj i₀)] [CompactSpace Z.left]
    {Y : Scheme.{u}} (h : Y ⟶ (baseChangeCone D c i₀ Z).pt) (hh : IsClosedImmersion h)
    (p : (baseChangeCone D c i₀ Z).pt ⟶ S)
    (hp : ∀ a : Over i₀, (baseChangeCone D c i₀ Z).π.app a ≫
      (baseChangeStructureMap D i₀ Z).app a ≫ t.app i₀ = p)
    (hlft : LocallyOfFiniteType (h ≫ p)) :
    ∃ a : Over i₀, IsClosedImmersion (h ≫ (baseChangeCone D c i₀ Z).π.app a) := by
  classical
  obtain ⟨α, _, _, _, ε, hε⟩ := exists_directed_cofinal_over (I := I) i₀
  let G : αᵒᵖ ⥤ Over i₀ := ε.op ⋙ (opOpEquivalence (Over i₀)).functor
  let E : Over i₀ ⥤ Scheme.{u} := baseChangeDiagram D i₀ Z
  let d : Cone E := baseChangeCone D c i₀ Z
  let D' : αᵒᵖ ⥤ Scheme.{u} := G ⋙ E
  let c' : Cone D' := d.whisker G
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv G d).symm
    (baseChangeConeIsLimit D hc i₀ Z)
  let t' : D' ⟶ (Functor.const αᵒᵖ).obj S :=
    { app := fun b => (baseChangeStructureMap D i₀ Z).app (G.obj b) ≫ t.app i₀
      naturality := fun b b' g => by
        have hnat := (baseChangeStructureMap D i₀ Z).naturality (G.map g)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hnat ⊢
        rw [← Category.assoc, show D'.map g = E.map (G.map g) from rfl, hnat] }
  have hcomm' : c'.π ≫ t' = (Functor.const αᵒᵖ).map p := by
    ext b
    exact hp (G.obj b)
  have hcpt : ∀ b : α, CompactSpace (D'.obj (op b)) := fun b =>
    compactSpace_baseChangeDiagram_obj D i₀ Z (G.obj (op b))
  have haff : ∀ ⦃b b' : α⦄ (hbb' : b ≤ b'), IsAffineHom (D'.map (homOfLE hbb').op) :=
    fun _ _ hbb' => isAffineHom_baseChangeDiagram_map D i₀ Z (G.map (homOfLE hbb').op)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    (EventualLimit.eventually_isClosedImmersion_comp_π_app D' t' c' hc' p h hcomm')
  exact ⟨G.obj (op k), hk k le_rfl⟩

/-! ### Tag 0EX1 -/

/-- The leg of the base-change cone followed by the structure morphism of the base-change
diagram is the first projection followed by the leg of `c`. -/
private theorem baseChangeCone_π_app_comp_baseChangeStructureMap_app_assoc {I : Type v}
    [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) {i : I} (Z : Over (D.obj i)) (a : Over i)
    {W : Scheme.{u}} (k : D.obj i ⟶ W) :
    (baseChangeCone D c i Z).π.app a ≫ (baseChangeStructureMap D i Z).app a ≫ k =
      pullback.fst (c.π.app i) Z.hom ≫ c.π.app i ≫ k :=
  (congrArg (fun l => (baseChangeCone D c i Z).π.app a ≫ l)
      (Category.assoc (pullback.snd (D.map a.hom) Z.hom) Z.hom k)).trans
    ((baseChangeTransition_snd_assoc (D.map a.hom) (c.π.app i) (c.π.app a.left) (c.w a.hom) Z
      (Z.hom ≫ k)).trans (pullback.condition_assoc k).symm)

/-- If `Y` is a closed subscheme of the base change of a proper `Z` over a stage to a later stage
`a`, and `f : Y ⟶ c.pt` factors through the base change of `Z` to the limit, then `f` is proper
over `a.left`. -/
private theorem isProper_comp_π_app_of_isClosedImmersion {I : Type v} [Category.{v} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i : I} (Z : Over (D.obj i)) [IsProper Z.hom]
    {Y : Scheme.{u}} (f : Y ⟶ c.pt) (h : Y ⟶ pullback (c.π.app i) Z.hom)
    (hf : h ≫ pullback.fst (c.π.app i) Z.hom = f) (a : Over i)
    (ha : IsClosedImmersion (h ≫ (baseChangeCone D c i Z).π.app a)) :
    IsProper (f ≫ c.π.app a.left) := by
  have _hfst : IsProper (pullback.fst (D.map a.hom) Z.hom) := inferInstance
  have _hfin : IsFinite (h ≫ (baseChangeCone D c i Z).π.app a) := inferInstance
  have _hh : IsProper (h ≫ (baseChangeCone D c i Z).π.app a) := inferInstance
  have hcomp : (h ≫ (baseChangeCone D c i Z).π.app a) ≫
      pullback.fst (D.map a.hom) Z.hom = f ≫ c.π.app a.left :=
    (Category.assoc h ((baseChangeCone D c i Z).π.app a)
        (pullback.fst (D.map a.hom) Z.hom)).trans
      ((congrArg (fun k => h ≫ k) (baseChangeTransition_fst (D.map a.hom) (c.π.app i)
          (c.π.app a.left) (c.w a.hom) Z)).trans
        ((Category.assoc h (pullback.fst (c.π.app i) Z.hom) (c.π.app a.left)).symm.trans
          (congrArg (fun k => k ≫ c.π.app a.left) hf)))
  rw [← hcomp]
  exact MorphismProperty.comp_mem @IsProper (h ≫ (baseChangeCone D c i Z).π.app a)
    (pullback.fst (D.map a.hom) Z.hom) _hh _hfst

/-- If a morphism to the limit of an inverse system with affine transition morphisms is proper
over a stage, then it is proper over every later stage. -/
private theorem isProper_comp_π_app_of_hom {I : Type v} [Category.{v} I] {D : I ⥤ Scheme.{u}}
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D) {Y : Scheme.{u}}
    (f : Y ⟶ c.pt) {i j : I} (hj : j ⟶ i) (hi : IsProper (f ≫ c.π.app i)) :
    IsProper (f ≫ c.π.app j) := by
  have : IsProper ((f ≫ c.π.app j) ≫ D.map hj) := by rwa [Category.assoc, c.w hj]
  have := IsSeparated.of_isAffineHom (D.map hj)
  exact IsProper.of_comp (f ≫ c.π.app j) (D.map hj)

/-- **Stacks 0EX1.** Let `X = lim Xᵢ` be the limit of a cofiltered inverse system of quasi-compact
and quasi-separated schemes over `S` with affine transition morphisms. A proper morphism
`f : Y ⟶ X` whose source is locally of finite type over `S` is proper over some stage of the
system and over every later stage. -/
@[stacks 0EX1]
theorem eventually_isProper_comp_π_app_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    {S : Scheme.{u}} (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (pX : c.pt ⟶ S)
    (hpX : c.π ≫ t = (Functor.const I).map pX)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {Y : Scheme.{u}} (pY : Y ⟶ S) (f : Y ⟶ c.pt) (hf : f ≫ pX = pY)
    [LocallyOfFiniteType pY] [IsProper f] :
    ∃ i : I, ∀ (j : I) (_ : j ⟶ i), IsProper (f ≫ c.π.app j) := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have _hπ : IsAffineHom (c.π.app i₀) := isAffineHom_π_app_of_initiallySmall D c hc i₀
  have _hπsep : IsSeparated (c.π.app i₀) := IsSeparated.of_isAffineHom (c.π.app i₀)
  have : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀)
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  -- **Step 1** ([Stacks, Tag 09ZR]): factor `f` as a closed immersion into a proper morphism of
  -- finite presentation over the limit.
  obtain ⟨Y', g, ι, hι, hfac, hgproper, hgfp⟩ :=
    exists_isClosedImmersion_isProper_finitePresentation f
  have _hg : IsProper (Over.mk g).hom := hgproper
  -- **Step 2** (part (1) of [Stacks, Tag 01ZM], then Tags 01ZQ and 081F): a proper model of
  -- finite presentation over a stage.
  obtain ⟨i, Zi, hZifp, hZiproper, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit D c hc (Over.mk g) hgfp
  have _hZilfp : LocallyOfFinitePresentation Zi.hom := hZifp.1
  obtain ⟨_hZicpt, -⟩ := compactSpace_and_quasiSeparatedSpace_left_of_finitePresentation Zi hZifp
  have _heiso : IsIso e.hom.left := isIso_left_of_overIso e
  -- The closed immersion of `Y` into the base change of the model to the limit.
  let h : Y ⟶ pullback (c.π.app i) Zi.hom :=
    ι ≫ e.hom.left ≫ (pullbackSymmetry Zi.hom (c.π.app i)).hom
  have hdef : h = ι ≫ e.hom.left ≫ (pullbackSymmetry Zi.hom (c.π.app i)).hom := rfl
  have _hhclosed : IsClosedImmersion h := by rw [hdef]; infer_instance
  -- The first projection is the structure morphism of the base change of the model to the limit,
  -- read into the base `S` through `pX`.
  have hπt : c.π.app i ≫ t.app i = pX := by
    simpa using congrArg (fun η => η.app i) hpX
  have hp : ∀ a : Over i, (baseChangeCone D c i Zi).π.app a ≫
      (baseChangeStructureMap D i Zi).app a ≫ t.app i =
      pullback.fst (c.π.app i) Zi.hom ≫ pX := fun a => by
    rw [baseChangeCone_π_app_comp_baseChangeStructureMap_app_assoc, hπt]
  -- `Y` is of finite type over `S` through that structure morphism.
  have hbase : e.hom.left ≫ pullback.snd Zi.hom (c.π.app i) = g := Over.w e.hom
  have eqA : h ≫ pullback.fst (c.π.app i) Zi.hom = f := by
    rw [hdef, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst, hbase, hfac]
  have _hlft : LocallyOfFiniteType (h ≫ pullback.fst (c.π.app i) Zi.hom ≫ pX) := by
    rw [← Category.assoc, eqA, hf]
    infer_instance
  -- **Step 3** (part (1) of [Stacks, Tag 081B]): `Y` is a closed subscheme of the base change of
  -- the model to a late enough stage.
  obtain ⟨a, ha⟩ :=
    exists_isClosedImmersion_comp_baseChangeCone_π_app D t c hc i Zi h _hhclosed
      (pullback.fst (c.π.app i) Zi.hom ≫ pX) hp _hlft
  -- **Step 4**: properness at `a.left` and at every later stage.
  exact ⟨a.left, fun j hj => isProper_comp_π_app_of_hom c f hj
    (isProper_comp_π_app_of_isClosedImmersion D c Zi f h eqA a ha)⟩

end AlgebraicGeometry

end

end
