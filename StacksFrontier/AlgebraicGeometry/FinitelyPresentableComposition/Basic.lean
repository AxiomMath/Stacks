module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Composing two filtered colimits through finitely presentable objects

Let `A` be the colimit of a filtered system `D : I ⥤ C`, and suppose each `D.obj i` is itself the
colimit of a filtered system `E i : K i ⥤ C`.  Is `A` a filtered colimit of the objects
`(E i).obj k`?  Not from those two statements alone: the inner systems are chosen separately for
each `i`, so there is no transition map from a stage of `E i` to a stage of `E i'`, and without
such maps there is no diagram to take a colimit of.

The missing input is a **lifting property**: a morphism out of `(E i).obj k` into `D.obj i'`,
which is the colimit of `E i'`, has to factor through some `(E i').obj k'`, and two such morphisms
agreeing further up have to become equal at a later stage.  That is exactly what
`CategoryTheory.IsFinitelyPresentable` gives, through Mathlib's
`CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit` and
`CategoryTheory.IsFinitelyPresentable.exists_eq_of_isColimit`.  This file assumes nothing else —
and it assumes it only **along the cocones of the two systems**, as `PresentableAlong` and
`TwoStagePresentable`, not against every filtered colimit in the ambient category.  The weaker
form is what lets the composition be used where presentability is known only for the cocones at
hand; `twoStagePresentable_of_isFinitelyPresentable` recovers it from
`CategoryTheory.IsFinitelyPresentable`.

This is the categorical content of the step of [Stacks, Tag 0817] part (2) that cites
[Stacks, Tag 01BS].  There, `A` is an integral quasi-coherent algebra written as a filtered
colimit of the algebras `Sym(ℱ_i)/𝒥_i` ([Stacks, Tag 01PK]), each of which is a filtered colimit
of the finite and finitely presented algebras `Sym(ℱ_i)/(ℰ_{ik})` ([Stacks, Tag 086N]); the
lifting `ℰ_{ik} → ℰ_{i'k'}` over `𝒥_i → 𝒥_{i'}` is taken from [Stacks, Tag 01BS].  The statement
proved here is the general form of that composition, so the only thing it leaves for Tag 0817 is
the finite presentability of the stages — that is, tag 01BS itself.

## The index category

The index of the composed system cannot be `Σ i, K i` with a chosen lift for each transition: the
lifts are not canonical and do not compose.  It is instead the pairs `⟨i, k⟩` with **all**
morphisms of `C` between the corresponding stages that commute with the structure maps to `A`.
That is a full subcategory of `CategoryTheory.Over A` sitting on the objects of `Σ i, K i`, which
is what `CategoryTheory.InducedCategory` constructs, and the resulting index lies in the same
universe as `Σ i, K i`: no smallness hypothesis is needed and none is produced out of thin air.

## Main definitions

* `Stacks.FinitelyPresentableComposition.PresentableAlong`: an object is finitely presentable
  *along a single cocone* — morphisms into the vertex factor through a stage, and morphisms into a
  stage agreeing at the vertex are equalized later.
* `Stacks.FinitelyPresentableComposition.TwoStagePresentable`: the hypothesis the composition
  consumes, namely `PresentableAlong` of every inner stage along the outer cocone and along every
  inner cocone.

## Main results

* `Stacks.FinitelyPresentableComposition.presentableAlong_of_isFinitelyPresentable` and
  `twoStagePresentable_of_isFinitelyPresentable`: finite presentability implies both, so the
  hypothesis below is weaker than Mathlib's predicate and not a restatement of it.
* `Stacks.FinitelyPresentableComposition.exists_factor`: **the lifting property of the composed
  system.** Every morphism into `A` out of an object presentable along the two systems' cocones
  factors through some stage `(E i).obj k`.
* `Stacks.FinitelyPresentableComposition.exists_equalizing`: two such morphisms into one stage
  that agree in `A` become equal after a transition to a later stage.  This is the `cocone_maps`
  half of filteredness and the harder of the two.
* `Stacks.FinitelyPresentableComposition.isFiltered_index`: the index category of the composed
  system is filtered.
* `Stacks.FinitelyPresentableComposition.isColimit_coconeIndex`: its canonical cocone with vertex
  `A` is colimiting.
* `Stacks.FinitelyPresentableComposition.exists_isColimit_of_twoStage`: the packaged conclusion —
  `A` is the colimit of a filtered diagram in `Type w` all of whose objects are stages, so any
  property of the stages is inherited.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** Nothing here is a statement about
sheaves of modules or about ringed spaces, so nothing here is [Stacks, Tag 01BS]: that tag asserts
that `Hom(𝒢, -)` commutes with filtered colimits for a sheaf of modules `𝒢` of finite
presentation on a ringed space with a cofinal system of finite open coverings with quasi-compact
pairwise intersections, which in Mathlib's vocabulary is exactly
`CategoryTheory.IsFinitelyPresentable` of `𝒢` in `SheafOfModules`.  That tag implies the
hypothesis `hfp` below, which is the one thing this file assumes rather than proves; `hfp` is
strictly weaker, asking presentability only along the cocones of the two systems being composed.

The *generic* lifting property — a morphism into a filtered colimit factors through a stage — is
**already in Mathlib** as `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`, and is
not restated here.

Mathlib's `CategoryTheory.Limits.isIndObject_colimit` is the presheaf-level analogue of
`exists_isColimit_of_twoStage` and needs no presentability hypothesis, because colimits of
presheaves are computed pointwise.  It cannot be transported along the restricted Yoneda
embedding into the full subcategory of stages, since that embedding is faithful only when the
stages generate; presentability of the stages is what replaces that.

## References

* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.FinitelyPresentableComposition

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{w} C] {A : C}
  {I : Type w} [SmallCategory I] {D : I ⥤ C}
  (t : D ⟶ (Functor.const I).obj A)
  {K : I → Type w} [∀ i, SmallCategory (K i)]
  {E : ∀ i, K i ⥤ C} (s : ∀ i, E i ⟶ (Functor.const (K i)).obj (D.obj i))

/-- **`B` is finitely presentable along a cocone.**  Every morphism from `B` to the vertex factors
through a stage of the diagram, and two morphisms from `B` into one stage that agree at the vertex
are equalized by a pair of transitions into a common later stage.

This is exactly what `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit` and
`CategoryTheory.IsFinitelyPresentable.exists_eq_of_isColimit` give for one colimiting cocone over a
filtered diagram — `presentableAlong_of_isFinitelyPresentable` — and it is all the composition
below consumes.  Taking it as the hypothesis instead of `CategoryTheory.IsFinitelyPresentable`
itself matters: it lets the composition run in a category where presentability is known only
*along the particular cocones at hand*.  That is the situation of [Stacks, Tag 0817] part (2),
whose cocones have quasi-coherent stages and quasi-coherent vertices — so that the relative
spectrum turns them into limits of schemes affine over the base — while presentability against an
arbitrary filtered colimit of arbitrary algebra sheaves is not available. -/
structure PresentableAlong {J : Type w} [SmallCategory J] {F : J ⥤ C} (B : C)
    (c : Cocone F) : Prop where
  /-- Every morphism from `B` to the vertex of the cocone factors through a stage. -/
  exists_hom : ∀ f : B ⟶ c.pt, ∃ (j : J) (g : B ⟶ F.obj j), g ≫ c.ι.app j = f
  /-- Two morphisms from `B` into a stage that agree at the vertex are equalized by a pair of
  transitions into a common later stage. -/
  exists_eq : ∀ (j : J) (g₁ g₂ : B ⟶ F.obj j), g₁ ≫ c.ι.app j = g₂ ≫ c.ι.app j →
    ∃ (j' : J) (u v : j ⟶ j'), g₁ ≫ F.map u = g₂ ≫ F.map v

/-- A finitely presentable object is finitely presentable along every colimiting cocone over a
filtered diagram: this is Mathlib's
`CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit` together with
`CategoryTheory.IsFinitelyPresentable.exists_eq_of_isColimit`, packaged. -/
theorem presentableAlong_of_isFinitelyPresentable {J : Type w} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {B : C}
    (hB : IsFinitelyPresentable.{w} B) : PresentableAlong B c where
  exists_hom f := by
    have := hB
    exact IsFinitelyPresentable.exists_hom_of_isColimit hc f
  exists_eq _ g₁ g₂ h := by
    have := hB
    exact IsFinitelyPresentable.exists_eq_of_isColimit hc g₁ g₂ h

/-- **The presentability data the two-stage composition consumes**: every inner stage is finitely
presentable along the outer cocone and along each of the inner cocones.

It is implied by finite presentability of the inner stages,
`twoStagePresentable_of_isFinitelyPresentable`, and is strictly weaker: nothing is asked about
cocones other than the ones the composition is built from. -/
def TwoStagePresentable : Prop :=
  ∀ (i : I) (k : K i), PresentableAlong ((E i).obj k) (Cocone.mk A t) ∧
    ∀ i' : I, PresentableAlong ((E i).obj k) (Cocone.mk (D.obj i') (s i'))

/-- Finitely presentable inner stages are finitely presentable along the two systems' own
cocones. -/
theorem twoStagePresentable_of_isFinitelyPresentable [IsFiltered I] [∀ i, IsFiltered (K i)]
    (ht : IsColimit (Cocone.mk A t)) (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
    (hfp : ∀ (i : I) (k : K i), IsFinitelyPresentable.{w} ((E i).obj k)) :
    TwoStagePresentable t s := fun i k =>
  ⟨presentableAlong_of_isFinitelyPresentable ht (hfp i k),
    fun i' => presentableAlong_of_isFinitelyPresentable (hs i') (hfp i k)⟩

/-- A transition of the outer system commutes with the maps to `A`. -/
lemma map_comp_outer {i i' : I} (u : i ⟶ i') : D.map u ≫ t.app i' = t.app i := by
  simp

/-- A transition of the `i`-th inner system commutes with the maps to `D.obj i`. -/
lemma map_comp_inner (i : I) {k k' : K i} (φ : k ⟶ k') :
    (E i).map φ ≫ (s i).app k' = (s i).app k := by
  simp

/-- The stage `⟨i, k⟩` of the two-stage system, viewed as an object over `A`. -/
def stageOver (p : (i : I) × K i) : Over A :=
  Over.mk ((s p.1).app p.2 ≫ t.app p.1)

/-- The object underlying the stage `⟨i, k⟩` over `A` is `(E i).obj k`. -/
@[simp]
lemma stageOver_left (p : (i : I) × K i) : (stageOver t s p).left = (E p.1).obj p.2 := rfl

/-- The structure map of the stage `⟨i, k⟩` to `A` is the composite of the cocone maps. -/
@[simp]
lemma stageOver_hom (p : (i : I) × K i) :
    (stageOver t s p).hom = (s p.1).app p.2 ≫ t.app p.1 := rfl

/-- The index category of the composed system: the pairs `⟨i, k⟩`, with **all** morphisms of `C`
between the corresponding stages that commute with the structure maps to `A`. -/
abbrev Index : Type w := InducedCategory (Over A) (stageOver t s)

/-- The diagram of the composed system: `⟨i, k⟩ ↦ (E i).obj k`. -/
def diagram : Index t s ⥤ C := inducedFunctor (stageOver t s) ⋙ Over.forget A

/-- The composed diagram sends `⟨i, k⟩` to `(E i).obj k`. -/
@[simp]
lemma diagram_obj (p : Index t s) : (diagram t s).obj p = (E p.1).obj p.2 := rfl

/-- The composed diagram sends a morphism of stages over `A` to its underlying morphism. -/
@[simp]
lemma diagram_map {p q : Index t s} (f : p ⟶ q) : (diagram t s).map f = f.hom.left := rfl

/-- The canonical cocone of the composed diagram, with vertex `A`. -/
def coconeIndex : Cocone (diagram t s) :=
  (Over.forgetCocone A).whisker (inducedFunctor (stageOver t s))

/-- The vertex of the canonical cocone of the composed diagram is `A`. -/
@[simp]
lemma coconeIndex_pt : (coconeIndex t s).pt = A := rfl

/-- The leg of the canonical cocone at `⟨i, k⟩` is the composite of the cocone maps. -/
@[simp]
lemma coconeIndex_ι_app (p : Index t s) :
    (coconeIndex t s).ι.app p = (s p.1).app p.2 ≫ t.app p.1 := rfl

/-- A lift over a transition `u` of the outer system commutes with the maps to `A`. -/
private lemma comp_leg_eq {i i' : I} {k : K i} {k' : K i'} (u : i ⟶ i')
    (r : (E i).obj k ⟶ (E i').obj k') (hr : r ≫ (s i').app k' = (s i).app k ≫ D.map u) :
    r ≫ (s i').app k' ≫ t.app i' = (s i).app k ≫ t.app i := by
  rw [← Category.assoc, hr, Category.assoc, map_comp_outer]

section Lifting

variable [IsFiltered I] [∀ i, IsFiltered (K i)]
  (ht : IsColimit (Cocone.mk A t)) (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))

omit [IsFiltered I] [∀ i, IsFiltered (K i)] in
/-- **The lifting property of the composed system.**  A morphism into `A` out of an object that is
finitely presentable along the two systems' cocones factors through some stage of the two-stage
system.

Both factorisations are the `exists_hom` field of `PresentableAlong`, applied first to the outer
system and then to the inner one. -/
theorem exists_factor {B : C} (hBout : PresentableAlong B (Cocone.mk A t))
    (hBin : ∀ i, PresentableAlong B (Cocone.mk (D.obj i) (s i))) (f : B ⟶ A) :
    ∃ (i : I) (k : K i) (g : B ⟶ (E i).obj k), g ≫ (s i).app k ≫ t.app i = f := by
  obtain ⟨i, p, hp⟩ := hBout.exists_hom f
  obtain ⟨k, g, hg⟩ := (hBin i).exists_hom p
  refine ⟨i, k, g, ?_⟩
  rw [← Category.assoc, hg]
  exact hp

/-- **Two morphisms into one stage that agree in `A`, out of an object finitely presentable along
the two systems' cocones, are equalized by a transition to a later stage**, and the transition
commutes with the maps to `A`.

This is the step that makes the index category filtered, and it consumes the presentability
hypothesis twice over: once for `B`, to move the disagreement up the outer system, and once for
the stage `(E i).obj k`, to move it up the inner system of the new outer index. -/
theorem exists_equalizing {B : C} (hBout : PresentableAlong B (Cocone.mk A t))
    (hBin : ∀ i', PresentableAlong B (Cocone.mk (D.obj i') (s i'))) {i : I} {k : K i}
    (hikin : ∀ i', PresentableAlong ((E i).obj k) (Cocone.mk (D.obj i') (s i')))
    (g₁ g₂ : B ⟶ (E i).obj k)
    (hg : g₁ ≫ (s i).app k ≫ t.app i = g₂ ≫ (s i).app k ≫ t.app i) :
    ∃ (i' : I) (k' : K i') (h : (E i).obj k ⟶ (E i').obj k'),
      h ≫ (s i').app k' ≫ t.app i' = (s i).app k ≫ t.app i ∧ g₁ ≫ h = g₂ ≫ h := by
  have h1 : (g₁ ≫ (s i).app k) ≫ t.app i = (g₂ ≫ (s i).app k) ≫ t.app i := by
    simpa using hg
  obtain ⟨i₃, u, v, huv⟩ := hBout.exists_eq i (g₁ ≫ (s i).app k) (g₂ ≫ (s i).app k) h1
  -- Merge the two transitions `u, v : i ⟶ i₃` into one, so that the disagreement is killed by a
  -- single morphism of the outer system.
  have hw : (g₁ ≫ (s i).app k) ≫ D.map (u ≫ IsFiltered.coeqHom u v)
      = (g₂ ≫ (s i).app k) ≫ D.map (u ≫ IsFiltered.coeqHom u v) := by
    conv_rhs => rw [IsFiltered.coeq_condition u v]
    rw [D.map_comp, D.map_comp, ← Category.assoc, ← Category.assoc, huv]
  obtain ⟨k₄, r, hr⟩ := (hikin (IsFiltered.coeq u v)).exists_hom
    ((s i).app k ≫ D.map (u ≫ IsFiltered.coeqHom u v))
  have h2 : (g₁ ≫ r) ≫ (s (IsFiltered.coeq u v)).app k₄
      = (g₂ ≫ r) ≫ (s (IsFiltered.coeq u v)).app k₄ := by
    rw [Category.assoc, hr, Category.assoc, hr, ← Category.assoc, ← Category.assoc]
    exact hw
  obtain ⟨k₅, a, b, hab⟩ := (hBin (IsFiltered.coeq u v)).exists_eq k₄ (g₁ ≫ r) (g₂ ≫ r) h2
  refine ⟨IsFiltered.coeq u v, IsFiltered.coeq a b,
    r ≫ (E (IsFiltered.coeq u v)).map (a ≫ IsFiltered.coeqHom a b), ?_, ?_⟩
  · exact comp_leg_eq t s _ _ (by rw [Category.assoc, map_comp_inner, hr])
  · calc g₁ ≫ r ≫ (E (IsFiltered.coeq u v)).map (a ≫ IsFiltered.coeqHom a b)
        = ((g₁ ≫ r) ≫ (E (IsFiltered.coeq u v)).map a)
            ≫ (E (IsFiltered.coeq u v)).map (IsFiltered.coeqHom a b) := by
          rw [Functor.map_comp, Category.assoc, Category.assoc]
      _ = ((g₂ ≫ r) ≫ (E (IsFiltered.coeq u v)).map b)
            ≫ (E (IsFiltered.coeq u v)).map (IsFiltered.coeqHom a b) := by rw [hab]
      _ = g₂ ≫ r ≫ (E (IsFiltered.coeq u v)).map (b ≫ IsFiltered.coeqHom a b) := by
          rw [Functor.map_comp, Category.assoc, Category.assoc]
      _ = g₂ ≫ r ≫ (E (IsFiltered.coeq u v)).map (a ≫ IsFiltered.coeqHom a b) := by
          rw [IsFiltered.coeq_condition]

end Lifting

section Filtered

variable [IsFiltered I] [∀ i, IsFiltered (K i)]
  (ht : IsColimit (Cocone.mk A t)) (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
  (hfp : TwoStagePresentable t s)

/-- The index of the composed system is nonempty, both systems being filtered. -/
theorem nonempty_index : Nonempty (Index t s) := by
  have hi : Nonempty I := IsFiltered.nonempty
  have hk : Nonempty (K hi.some) := IsFiltered.nonempty
  exact ⟨⟨hi.some, hk.some⟩⟩

include hfp in
/-- Any two stages admit morphisms into a common stage, and any two parallel morphisms of stages
are equalized by a morphism into a later stage. -/
theorem isFilteredOrEmpty_index : IsFilteredOrEmpty (Index t s) where
  cocone_objs p q := by
    obtain ⟨i₁, k₁⟩ := p
    obtain ⟨i₂, k₂⟩ := q
    obtain ⟨m₁, r₁, hr₁⟩ := ((hfp i₁ k₁).2 (IsFiltered.max i₁ i₂)).exists_hom
      ((s i₁).app k₁ ≫ D.map (IsFiltered.leftToMax i₁ i₂))
    obtain ⟨m₂, r₂, hr₂⟩ := ((hfp i₂ k₂).2 (IsFiltered.max i₁ i₂)).exists_hom
      ((s i₂).app k₂ ≫ D.map (IsFiltered.rightToMax i₁ i₂))
    have h₁ : (r₁ ≫ (E (IsFiltered.max i₁ i₂)).map (IsFiltered.leftToMax m₁ m₂))
        ≫ (s (IsFiltered.max i₁ i₂)).app (IsFiltered.max m₁ m₂) ≫ t.app (IsFiltered.max i₁ i₂)
        = (s i₁).app k₁ ≫ t.app i₁ := by
      exact comp_leg_eq t s _ _ (by rw [Category.assoc, map_comp_inner, hr₁])
    have h₂ : (r₂ ≫ (E (IsFiltered.max i₁ i₂)).map (IsFiltered.rightToMax m₁ m₂))
        ≫ (s (IsFiltered.max i₁ i₂)).app (IsFiltered.max m₁ m₂) ≫ t.app (IsFiltered.max i₁ i₂)
        = (s i₂).app k₂ ≫ t.app i₂ := by
      exact comp_leg_eq t s _ _ (by rw [Category.assoc, map_comp_inner, hr₂])
    exact ⟨⟨IsFiltered.max i₁ i₂, IsFiltered.max m₁ m₂⟩,
      InducedCategory.homMk (Over.homMk
        (r₁ ≫ (E (IsFiltered.max i₁ i₂)).map (IsFiltered.leftToMax m₁ m₂)) h₁),
      InducedCategory.homMk (Over.homMk
        (r₂ ≫ (E (IsFiltered.max i₁ i₂)).map (IsFiltered.rightToMax m₁ m₂)) h₂), trivial⟩
  cocone_maps {p q} f g := by
    obtain ⟨i₁, k₁⟩ := p
    obtain ⟨i₂, k₂⟩ := q
    have hw : ∀ {p q : Index t s} (e : p ⟶ q),
        e.hom.left ≫ (s q.1).app q.2 ≫ t.app q.1 = (s p.1).app p.2 ≫ t.app p.1 := fun e => by
      simpa using Over.w e.hom
    obtain ⟨i', k', h, hleg, heq⟩ := exists_equalizing t s (hfp i₁ k₁).1 (hfp i₁ k₁).2
      (hfp i₂ k₂).2 f.hom.left g.hom.left ((hw f).trans (hw g).symm)
    refine ⟨⟨i', k'⟩, InducedCategory.homMk (Over.homMk h hleg), ?_⟩
    · apply InducedCategory.hom_ext
      apply Over.OverMorphism.ext
      exact heq

include hfp in
/-- **The index of the composed system is filtered.** -/
theorem isFiltered_index : IsFiltered (Index t s) :=
  { toIsFilteredOrEmpty := isFilteredOrEmpty_index t s hfp
    nonempty := nonempty_index t s }

end Filtered

section Colimit

variable [∀ i, IsFiltered (K i)] (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
  (hfp : TwoStagePresentable t s)
  (Z : Cocone (diagram t s))

/-- A cocone on the composed diagram restricts to a cocone on each inner system: a transition of
the inner system commutes with the maps to `A`, hence is a morphism of the index category. -/
def innerCocone (i : I) : Cocone (E i) where
  pt := Z.pt
  ι :=
    { app := fun k => Z.ι.app ⟨i, k⟩
      naturality := fun k k' φ => by
        have hφ : (E i).map φ ≫ (s i).app k' ≫ t.app i = (s i).app k ≫ t.app i := by
          rw [← Category.assoc, map_comp_inner]
        have hmor := Z.w (InducedCategory.homMk (F := stageOver t s)
          (X := ⟨i, k⟩) (Y := ⟨i, k'⟩) (Over.homMk ((E i).map φ) hφ))
        exact hmor.trans (Category.comp_id _).symm }

/-- The morphism out of `D.obj i` induced by a cocone on the composed diagram. -/
def innerDesc (i : I) : D.obj i ⟶ Z.pt := (hs i).desc (innerCocone t s Z i)

omit [∀ i, IsFiltered (K i)] in
/-- Precomposing `innerDesc` with the cocone map from `(E i).obj k` gives the leg of `Z` at
`⟨i, k⟩`. -/
@[simp]
lemma app_comp_innerDesc (i : I) (k : K i) :
    (s i).app k ≫ innerDesc t s hs Z i = Z.ι.app ⟨i, k⟩ :=
  (hs i).fac (innerCocone t s Z i) k

/-- A cocone on the composed diagram induces a cocone on the outer system.

Compatibility over a transition `u : i ⟶ i'` is where the presentability of the stages is used
once more: the map `(E i).obj k ⟶ D.obj i'` has to be factored through a stage of the `i'`-th
inner system before the cocone `Z` can be applied to it. -/
def outerCocone : Cocone D where
  pt := Z.pt
  ι :=
    { app := fun i => innerDesc t s hs Z i
      naturality := fun i i' u => by
        have key : D.map u ≫ innerDesc t s hs Z i' = innerDesc t s hs Z i := by
          refine (hs i).hom_ext fun k => ?_
          obtain ⟨k', r, hr⟩ := ((hfp i k).2 i').exists_hom ((s i).app k ≫ D.map u)
          have hmor : r ≫ (s i').app k' ≫ t.app i' = (s i).app k ≫ t.app i := by
            rw [← Category.assoc, hr, Category.assoc, map_comp_outer]
          have hw := Z.w (InducedCategory.homMk (F := stageOver t s)
            (X := ⟨i, k⟩) (Y := ⟨i', k'⟩) (Over.homMk r hmor))
          have hstage : (s i).app k ≫ D.map u ≫ innerDesc t s hs Z i' = Z.ι.app ⟨i, k⟩ := by
            rw [← Category.assoc, ← hr, Category.assoc, app_comp_innerDesc]
            exact hw
          rw [hstage, app_comp_innerDesc]
        exact key.trans (Category.comp_id _).symm }

end Colimit

section IsColimit

variable [IsFiltered I] [∀ i, IsFiltered (K i)]
  (ht : IsColimit (Cocone.mk A t)) (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
  (hfp : TwoStagePresentable t s)

/-- **The canonical cocone of the composed system is colimiting.**

The morphism out of `A` is built in two stages — down each inner system first, then along the
outer one — and both halves of the universal property are checked stagewise. -/
def isColimit_coconeIndex : IsColimit (coconeIndex t s) where
  desc Z := ht.desc (outerCocone t s hs hfp Z)
  fac Z p := by
    obtain ⟨i, k⟩ := p
    change ((s i).app k ≫ t.app i) ≫ ht.desc (outerCocone t s hs hfp Z) = Z.ι.app ⟨i, k⟩
    rw [Category.assoc, ht.fac (outerCocone t s hs hfp Z) i]
    exact app_comp_innerDesc t s hs Z i k
  uniq Z m hm := by
    refine ht.hom_ext fun i => ?_
    change t.app i ≫ m = t.app i ≫ ht.desc (outerCocone t s hs hfp Z)
    rw [ht.fac (outerCocone t s hs hfp Z) i]
    refine (hs i).hom_ext fun k => ?_
    exact (Category.assoc _ _ _).symm.trans
      ((hm ⟨i, k⟩).trans (app_comp_innerDesc t s hs Z i k).symm)

include ht hs hfp in
/-- **A filtered colimit of filtered colimits of finitely presentable objects is a filtered
colimit of those objects.**

If `A` is the colimit of a filtered system `D` over an index in `Type w`, each `D.obj i` is the
colimit of a filtered system `E i` over an index in `Type w`, and every stage `(E i).obj k` is
finitely presentable, then `A` is the colimit of a filtered diagram over an index in `Type w`
every one of whose objects is a stage — so any property `P` of the stages holds throughout the
new diagram.

This is the composition step that [Stacks, Tag 0817] part (2) needs and that part (1) together
with [Stacks, Tag 086N] does not supply: tag 086N is a bare existential, giving a system for each
`D.obj i` with no compatibility between the choices for `i` and for `i'`.  The hypothesis `hfp` is
what replaces that compatibility, and for algebra sheaves it is implied by [Stacks, Tag 01BS]. -/
theorem exists_isColimit_of_twoStage (P : C → Prop)
    (hP : ∀ (i : I) (k : K i), P ((E i).obj k)) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J) (G : J ⥤ C)
      (ι : G ⟶ (Functor.const J).obj A) (_ : IsColimit (Cocone.mk A ι)),
      ∀ j, P (G.obj j) :=
  ⟨Index t s, inferInstance, isFiltered_index t s hfp, diagram t s, (coconeIndex t s).ι,
    isColimit_coconeIndex t s ht hs hfp, fun p => hP p.1 p.2⟩

end IsColimit

end Stacks.FinitelyPresentableComposition

end
