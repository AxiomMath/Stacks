module

public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux2
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# A Noetherian model of a proper morphism flat over an affine base

Let `X --f--> Y --q--> S` with `S` and `Y` affine, `q` of finite presentation, `f` proper and
`X ⟶ S` flat and locally of finite presentation. This file shows that the whole triangle is the
base change of a triangle `X₀ ⟶ Y₀ ⟶ S₀` with the same properties over a Noetherian affine `S₀`.
This is the reduction step of the proofs of [Stacks, Tags 0E7J] and [0E7L] ("write `S = lim Sᵢ`
as a cofiltered limit of affine Noetherian schemes ..."), assembled from
[Stacks, Tag 01ZM] parts (1) and (2), [Stacks, Tag 081F] and [Stacks, Tag 04AI].

## Main results

* `exists_stage_model`: over the limit of a cofiltered system of affine schemes with affine
  transitions, the triangle descends to a stage.
* `exists_noetherianModel`: the Noetherian model over an affine base.

## References

* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

section Stage

variable {I : Type u} [Category.{u} I] (E : I ⥤ Scheme.{u}) (c : Cone E)

/-- Base change along equal morphisms. -/
def overPullbackCongr {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) :
    Over.pullback a ≅ Over.pullback b := by
  subst h
  exact Iso.refl _

/-- Base change along `E.map e` followed by base change to the limit is base change to the
limit. -/
def overPullbackStageIso {j m : I} (e : m ⟶ j) :
    Over.pullback (E.map e) ⋙ Over.pullback (c.π.app m) ≅ Over.pullback (c.π.app j) :=
  (Over.pullbackComp (c.π.app m) (E.map e)).symm ≪≫ overPullbackCongr (c.w e)

/-- A base-change-stable property of the base change of any morphism from a slice object to
the terminal slice object is the property of the second projection out of the base change. -/
theorem prop_overPullback_map_toTerminal_iff (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {A W : Scheme.{u}} (g : W ⟶ A) {X : Over A} (τ : X ⟶ Over.mk (𝟙 A)) :
    P ((Over.pullback g).map τ).left ↔ P (pullback.snd X.hom g) := by
  have hw : ((Over.pullback g).map τ).left ≫ pullback.snd (𝟙 A) g =
      pullback.snd X.hom g := Over.w ((Over.pullback g).map τ)
  rw [← hw]
  exact (P.cancel_right_of_respectsIso _ _).symm

/-- A base-change-stable property of a base changed morphism persists at later stages. -/
theorem prop_overPullback_of_le {j₀ : I} {X Y : Over (E.obj j₀)} (f₀ : X ⟶ Y)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] {j k : I} (e : j ⟶ j₀)
    (g : k ⟶ j) (hp : P ((Over.pullback (E.map e)).map f₀).left) :
    P ((Over.pullback (E.map (g ≫ e))).map f₀).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [E.map_comp]
  refine (MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk
    ((Over.forget _).mapIso ((Over.pullbackComp (E.map g) (E.map e)).app X))
    ((Over.forget _).mapIso ((Over.pullbackComp (E.map g) (E.map e)).app Y))
    (congrArg (fun z ↦ z.left)
      ((Over.pullbackComp (E.map g) (E.map e)).hom.naturality f₀)).symm)).2 ?_
  exact MorphismProperty.overPullbackMap (P := P) (E.map g) _ hp

/-- Two identifications of `f ≫ q` and `q` with base changes along `π`, intertwining `f` with the
base change of `g`, exhibit `f` as a base change of `g.left`. -/
private theorem isPullback_left_of_overIso_comp {B T X Y : Scheme.{u}} {π : T ⟶ B}
    {X' Y' : Over B} {f : X ⟶ Y} {q : Y ⟶ T} (g : X' ⟶ Y')
    (ΨX : Over.mk (f ≫ q) ≅ (Over.pullback π).obj X')
    (ΨY : Over.mk q ≅ (Over.pullback π).obj Y')
    (hΨ : ΨX.hom ≫ (Over.pullback π).map g =
      (Over.homMk f rfl : Over.mk (f ≫ q) ⟶ Over.mk q) ≫ ΨY.hom) :
    IsPullback (ΨX.hom.left ≫ pullback.fst X'.hom π) f g.left
      (ΨY.hom.left ≫ pullback.fst Y'.hom π) := by
  have hsX : IsPullback (ΨX.hom.left ≫ pullback.fst X'.hom π) (f ≫ q) (g.left ≫ Y'.hom) π :=
    @Eq.subst _ (fun h => IsPullback (ΨX.hom.left ≫ pullback.fst X'.hom π) (f ≫ q) h π) _ _
      (Over.w g).symm (isPullback_left_fst_of_overIso X' ΨX)
  refine IsPullback.of_bot hsX ?_ (isPullback_left_fst_of_overIso Y' ΨY)
  have h : ΨX.hom.left ≫ ((Over.pullback π).map g).left = f ≫ ΨY.hom.left :=
    congrArg (fun u => u.left) hΨ
  rw [Category.assoc, ← overPullback_map_left_fst, ← Category.assoc, h, Category.assoc]

/-- A morphism property respecting isomorphisms passes from `f` to the base change of `g`, when
two identifications with base changes along `π` intertwine `f` with the base change of `g`. -/
private theorem prop_overPullback_map_of_overIso (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {B T X Y : Scheme.{u}} {π : T ⟶ B} {X' Y' : Over B} {f : X ⟶ Y} {q : Y ⟶ T}
    (g : X' ⟶ Y')
    (ΦX : Over.mk (f ≫ q) ≅ (Over.pullback π).obj X') (ΦY : Over.mk q ≅ (Over.pullback π).obj Y')
    (hΦ : ΦX.hom ≫ (Over.pullback π).map g =
      (Over.homMk f rfl : Over.mk (f ≫ q) ⟶ Over.mk q) ≫ ΦY.hom) (hf : P f) :
    P ((Over.pullback π).map g).left := by
  have : IsIso ΦX.hom.left := (Over.forget _).map_isIso ΦX.hom
  have : IsIso ΦY.hom.left := (Over.forget _).map_isIso ΦY.hom
  have h : ΦX.hom.left ≫ ((Over.pullback π).map g).left = f ≫ ΦY.hom.left :=
    congrArg (fun u => u.left) hΦ
  have h1 : P (f ≫ ΦY.hom.left) := (P.cancel_right_of_respectsIso _ _).mpr hf
  rw [← h] at h1
  exact (P.cancel_left_of_respectsIso _ _).mp h1

/-- Flat morphisms are stable under composition with isomorphisms. -/
private instance : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- A morphism between finitely presented schemes over `E.obj j` whose base change to the limit is
proper, with flat source over the limit, is proper with flat source after base change to a
later stage. -/
private theorem exists_isProper_flat_overPullback [IsCofiltered I] [∀ i, IsAffine (E.obj i)]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (E.map a)] (hc : IsLimit c) {j : I}
    (X₄ Y₄ : Over (E.obj j)) (hX₄ : FinitePresentation X₄.hom) (hY₄ : FinitePresentation Y₄.hom)
    (g : X₄ ⟶ Y₄) (hpr : IsProper ((Over.pullback (c.π.app j)).map g).left)
    (hfl : Flat (pullback.snd X₄.hom (c.π.app j))) :
    ∃ (m : I) (a : m ⟶ j), IsProper ((Over.pullback (E.map a)).map g).left ∧
      Flat (pullback.snd X₄.hom (E.map a)) := by
  have hqcqs : ∀ Z : Over (E.obj j), FinitePresentation Z.hom →
      CompactSpace Z.left ∧ QuasiSeparatedSpace Z.left := fun Z hZ ↦
    ⟨have := hZ.2.1; QuasiCompact.compactSpace_of_compactSpace Z.hom,
      have := hZ.2.2; quasiSeparatedSpace_of_quasiSeparated Z.hom⟩
  obtain ⟨_, _⟩ := hqcqs X₄ hX₄
  obtain ⟨_, _⟩ := hqcqs Y₄ hY₄
  have : LocallyOfFinitePresentation X₄.hom := hX₄.1
  have : LocallyOfFinitePresentation Y₄.hom := hY₄.1
  have : LocallyOfFiniteType g.left := by
    have : LocallyOfFiniteType (g.left ≫ Y₄.hom) := by rw [Over.w g]; infer_instance
    exact locallyOfFiniteType_of_comp g.left Y₄.hom
  let τ : X₄ ⟶ Over.mk (𝟙 (E.obj j)) := Over.homMk X₄.hom (Category.comp_id _)
  have hfl' : Flat ((Over.pullback (c.π.app j)).map τ).left := by
    rwa [prop_overPullback_map_toTerminal_iff (@Flat)]
  have : CompactSpace (Over.mk (𝟙 (E.obj j))).left := (inferInstance : CompactSpace (E.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (E.obj j))).left :=
    (inferInstance : QuasiSeparatedSpace (E.obj j))
  have : LocallyOfFinitePresentation τ.left := hX₄.1
  obtain ⟨k₁, b₁, hp₁⟩ := exists_isProper_baseChange_of_isLimit E c j hc X₄ Y₄ g
  obtain ⟨k₂, b₂, hf₂⟩ := exists_flat_baseChange_of_limitBaseChange E c j X₄
    (Over.mk (𝟙 (E.obj j))) τ hc
  obtain ⟨m, b, b', hbb⟩ := IsCofiltered.cospan b₁ b₂
  refine ⟨m, b ≫ b₁, prop_overPullback_of_le E g (@IsProper) b₁ b hp₁, ?_⟩
  have h := prop_overPullback_of_le E τ (@Flat) b₂ b' hf₂
  rwa [← hbb, prop_overPullback_map_toTerminal_iff (@Flat)] at h

/-- A model at stage `j` of a proper morphism `f` with `f ≫ q` flat, between finitely presented
schemes over `E.obj j`, can be refined to a model at a later stage that is proper and flat. -/
private theorem exists_stage_model_of_overIso [IsCofiltered I] [∀ i, IsAffine (E.obj i)]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (E.map a)] (hc : IsLimit c)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ c.pt) [IsProper f] [Flat (f ≫ q)] {j : I}
    (X₄ Y₄ : Over (E.obj j)) (hX₄ : FinitePresentation X₄.hom) (hY₄ : FinitePresentation Y₄.hom)
    (g : X₄ ⟶ Y₄) (ΦX : Over.mk (f ≫ q) ≅ (Over.pullback (c.π.app j)).obj X₄)
    (ΦY : Over.mk q ≅ (Over.pullback (c.π.app j)).obj Y₄)
    (hΦ : ΦX.hom ≫ (Over.pullback (c.π.app j)).map g =
      (Over.homMk f rfl : Over.mk (f ≫ q) ⟶ Over.mk q) ≫ ΦY.hom) :
    ∃ (i : I) (Y₀ X₀ : Scheme.{u}) (q₀ : Y₀ ⟶ E.obj i) (f₀ : X₀ ⟶ Y₀) (πY : Y ⟶ Y₀)
      (πX : X ⟶ X₀), LocallyOfFinitePresentation q₀ ∧ IsProper f₀ ∧ Flat (f₀ ≫ q₀) ∧
        IsPullback πY q q₀ (c.π.app i) ∧ IsPullback πX f f₀ πY := by
  have hfl : Flat (pullback.snd X₄.hom (c.π.app j)) := by
    have hw : ΦX.hom.left ≫ pullback.snd X₄.hom (c.π.app j) = f ≫ q := Over.w ΦX.hom
    have h1 : Flat (ΦX.hom.left ≫ pullback.snd X₄.hom (c.π.app j)) := by
      rw [hw]
      infer_instance
    have : IsIso ΦX.hom.left := (Over.forget _).map_isIso ΦX.hom
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat) _ _).mp h1
  obtain ⟨m, a, hpa, hfa⟩ := exists_isProper_flat_overPullback E c hc X₄ Y₄ hX₄ hY₄ g
    (prop_overPullback_map_of_overIso @IsProper g ΦX ΦY hΦ ‹_›) hfl
  let X₅ := (Over.pullback (E.map a)).obj X₄
  let Y₅ := (Over.pullback (E.map a)).obj Y₄
  let g₅ := (Over.pullback (E.map a)).map g
  let ΨX : Over.mk (f ≫ q) ≅ (Over.pullback (c.π.app m)).obj X₅ :=
    ΦX ≪≫ ((overPullbackStageIso E c a).app X₄).symm
  let ΨY : Over.mk q ≅ (Over.pullback (c.π.app m)).obj Y₅ :=
    ΦY ≪≫ ((overPullbackStageIso E c a).app Y₄).symm
  have hΨ : ΨX.hom ≫ (Over.pullback (c.π.app m)).map g₅ =
      (Over.homMk f rfl : Over.mk (f ≫ q) ⟶ Over.mk q) ≫ ΨY.hom := by
    have hn := (overPullbackStageIso E c a).inv.naturality g
    simp only [Functor.comp_map] at hn
    simp only [ΨX, ΨY, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, g₅]
    rw [← hn, reassoc_of% hΦ]
  refine ⟨m, Y₅.left, X₅.left, Y₅.hom, g₅.left, ΨY.hom.left ≫ pullback.fst Y₅.hom (c.π.app m),
    ΨX.hom.left ≫ pullback.fst X₅.hom (c.π.app m),
    (LimitFPObjectDescent.finitePresentation_overPullback (E.map a) Y₄ hY₄).1, hpa, ?_,
    isPullback_left_fst_of_overIso Y₅ ΨY, isPullback_left_of_overIso_comp g₅ ΨX ΨY hΨ⟩
  rw [Over.w g₅]
  exact hfa

/-- **A proper morphism, flat over the limit, descends to a stage.** Let `S = lim Sᵢ` be the
limit of a cofiltered system of affine schemes with affine transitions, `q : Y ⟶ S` of finite
presentation, and `f : X ⟶ Y` proper with `X ⟶ S` flat and of finite presentation. Then at some
stage `i` there are `q₀ : Y₀ ⟶ Sᵢ` of finite presentation and `f₀ : X₀ ⟶ Y₀` proper with
`X₀ ⟶ Sᵢ` flat, whose base change along `S ⟶ Sᵢ` is `X ⟶ Y ⟶ S`.

[Stacks, Tags 01ZM] parts (1) and (2) give the models of `Y`, of `X` and of `f`, and
[Stacks, Tags 081F] and [04AI] give properness and flatness at a later stage. -/
theorem exists_stage_model [IsCofiltered I] [∀ i, IsAffine (E.obj i)]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (E.map a)] (hc : IsLimit c)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ c.pt) [IsProper f]
    (hq : FinitePresentation q) (hfq : FinitePresentation (f ≫ q)) [Flat (f ≫ q)] :
    ∃ (i : I) (Y₀ X₀ : Scheme.{u}) (q₀ : Y₀ ⟶ E.obj i) (f₀ : X₀ ⟶ Y₀) (πY : Y ⟶ Y₀)
      (πX : X ⟶ X₀), LocallyOfFinitePresentation q₀ ∧ IsProper f₀ ∧ Flat (f₀ ≫ q₀) ∧
        IsPullback πY q q₀ (c.π.app i) ∧ IsPullback πX f f₀ πY := by
  classical
  -- models of `Y` and of `X` over `S`
  obtain ⟨i₁, Y₁, hY₁, ⟨eY₁⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation E c hc (Over.mk q) hq
  obtain ⟨i₂, X₂, hX₂, ⟨eX₂⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation E c hc (Over.mk (f ≫ q)) hfq
  let i₃ := IsCofiltered.min i₁ i₂
  let a₁ : i₃ ⟶ i₁ := IsCofiltered.minToLeft i₁ i₂
  let a₂ : i₃ ⟶ i₂ := IsCofiltered.minToRight i₁ i₂
  let Y₃ := (Over.pullback (E.map a₁)).obj Y₁
  let X₃ := (Over.pullback (E.map a₂)).obj X₂
  let eY₃ : Over.mk q ≅ (Over.pullback (c.π.app i₃)).obj Y₃ :=
    eY₁ ≪≫ ((overPullbackStageIso E c a₁).app Y₁).symm
  let eX₃ : Over.mk (f ≫ q) ≅ (Over.pullback (c.π.app i₃)).obj X₃ :=
    eX₂ ≪≫ ((overPullbackStageIso E c a₂).app X₂).symm
  have hY₃ : FinitePresentation Y₃.hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (E.map a₁) Y₁ hY₁
  have hX₃ : FinitePresentation X₃.hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (E.map a₂) X₂ hX₂
  -- the model of `f`
  let fO : Over.mk (f ≫ q) ⟶ Over.mk q := Over.homMk f rfl
  obtain ⟨j, e, g, α, β, -, -, hαβ⟩ := exists_morphism_after_baseChange E c hc i₃ X₃ Y₃ hX₃ hY₃
    (eX₃.inv ≫ fO ≫ eY₃.hom)
  let ΦX : Over.mk (f ≫ q) ≅ (Over.pullback (c.π.app j)).obj ((Over.pullback (E.map e)).obj X₃) :=
    eX₃ ≪≫ α.symm
  let ΦY : Over.mk q ≅ (Over.pullback (c.π.app j)).obj ((Over.pullback (E.map e)).obj Y₃) :=
    eY₃ ≪≫ β.symm
  have hΦ : ΦX.hom ≫ (Over.pullback (c.π.app j)).map g = fO ≫ ΦY.hom := by
    have h1 : (Over.pullback (c.π.app j)).map g = α.hom ≫ (eX₃.inv ≫ fO ≫ eY₃.hom) ≫ β.inv := by
      rw [← Category.assoc, hαβ]
      simp
    simp only [ΦX, ΦY, Iso.trans_hom, Iso.symm_hom, h1, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc]
  let X₄ := (Over.pullback (E.map e)).obj X₃
  let Y₄ := (Over.pullback (E.map e)).obj Y₃
  have hX₄ : FinitePresentation X₄.hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (E.map e) X₃ hX₃
  have hY₄ : FinitePresentation Y₄.hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (E.map e) Y₃ hY₃
  exact exists_stage_model_of_overIso E c hc f q X₄ Y₄ hX₄ hY₄ g ΦX ΦY hΦ

end Stage

/-- **A Noetherian model of a proper morphism flat over an affine base.** Let `S` be affine,
`q : Y ⟶ S` of finite presentation with `Y` affine, and `f : X ⟶ Y` proper with `X ⟶ S` flat
and locally of finite presentation. Then `X ⟶ Y ⟶ S` is the base change, along a morphism
`S ⟶ S₀` to a Noetherian affine scheme, of `X₀ ⟶ Y₀ ⟶ S₀` with `Y₀ ⟶ S₀` of finite
presentation, `X₀ ⟶ Y₀` proper and `X₀ ⟶ S₀` flat.

`S` is the limit of the spectra of the finitely generated `ℤ`-subalgebras of `Γ(S, ⊤)`
(`AlgebraicGeometry.isLimit_specAdjoinFinsetCone`), and `exists_stage_model` descends the
situation to a stage. -/
theorem exists_noetherianModel {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [IsAffine S]
    [IsAffine Y] [IsProper f] [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)] :
    ∃ (S₀ Y₀ X₀ : Scheme.{u}) (q₀ : Y₀ ⟶ S₀) (f₀ : X₀ ⟶ Y₀) (π : S ⟶ S₀) (πY : Y ⟶ Y₀)
      (πX : X ⟶ X₀), IsNoetherian S₀ ∧ IsAffine S₀ ∧ LocallyOfFinitePresentation q₀ ∧
        IsProper f₀ ∧ Flat (f₀ ≫ q₀) ∧ IsPullback πY q q₀ π ∧ IsPullback πX f f₀ πY := by
  let c := (specAdjoinFinsetCone Γ(S, ⊤)).extend S.isoSpec.hom
  have hc : IsLimit c := IsLimit.ofIsoLimit (isLimit_specAdjoinFinsetCone Γ(S, ⊤))
    (Cone.extendIso (specAdjoinFinsetCone Γ(S, ⊤))
      (S.isoSpec.symm : (specAdjoinFinsetCone Γ(S, ⊤)).pt ≅ S))
  have hq : FinitePresentation q := ⟨inferInstance, inferInstance, inferInstance⟩
  have hfq : FinitePresentation (f ≫ q) := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨i, Y₀, X₀, q₀, f₀, πY, πX, h₁, h₂, h₃, h₄, h₅⟩ :=
    exists_stage_model (specAdjoinFinsetDiagram Γ(S, ⊤)) c hc (q := q) f hq hfq
  exact ⟨_, Y₀, X₀, q₀, f₀, c.π.app i, πY, πX, isNoetherian_specAdjoinFinsetDiagram_obj _ i,
    isAffine_specAdjoinFinsetDiagram_obj _ i, h₁, h₂, h₃, h₄, h₅⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
