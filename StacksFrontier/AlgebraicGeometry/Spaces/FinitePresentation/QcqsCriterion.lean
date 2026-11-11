module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.AffineCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The quasi-compact quasi-separated criterion for relative limit preservation

Relative limit preservation of a morphism of algebraic spaces over a scheme `S` is tested on
cofiltered inverse limits of affine objects of the big fppf site; this file replaces those by
cofiltered inverse limits of quasi-compact and quasi-separated algebraic spaces with affine
transition morphisms, Stacks 0CP4.

## Main definitions

* `AlgebraicGeometry.Space.AffineLimitSquare`: the affine-limit comparison square is
  cartesian for every sufficiently small cofiltered system of affine objects.
* `AlgebraicGeometry.Space.QcqsLimitSquare`: the comparison square of morphism sets is
  cartesian for every sufficiently small cofiltered system of quasi-compact and
  quasi-separated algebraic spaces with affine transition morphisms.

## Main results

* `AlgebraicGeometry.Space.affineLimitSquare_iff_qcqsLimitSquare`: the two conditions agree.
  Stacks 0CP4 itself, the equivalence with local finite presentation, is
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae_qcqsLimitSquare` in
  `StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterionTfae`.
* `AlgebraicGeometry.Space.affineLimitSquare_of_qcqsLimitSquare`: the easy implication, which
  needs no hypothesis on the source and target.
* `AlgebraicGeometry.Space.qcqsLimitSquare_of_relativelyLimitPreserving` and
  `AlgebraicGeometry.Space.qcqsLimitSquare_of_isLocallyOfFinitePresentation`: the condition
  holds for a relatively limit preserving morphism, hence for one which is locally of finite
  presentation.

## Implementation notes

Both conditions are restricted to index categories whose object type and morphism types are
smaller than the cofinality of the site's size cutoff, as in Stacks 07SF and every statement
about inverse limits in this chapter: without such a bound the limit of the system need not
be an object of the site at all, and the condition is then refuted by an increasing chain of
fields whose sizes are cofinal in the cutoff. For the same reason the index category is taken
in the universe of the schemes, so that its cardinality is expressible.

Both implications are proved through an elementwise description of the comparison square: the
square of sets is cartesian exactly when two stagewise conditions, injectivity and
surjectivity, hold. The quasi-compact condition is then transported to the affine one through
the Yoneda embedding of the site into presheaves.

The implication from the affine condition uses that the source and target are *sheaves*: a
section over an affine étale chart of a stage descends to the stage only because the stage is
the quotient of the chart by its self-intersection. This is the hypothesis `hX`, `hY` of
`AlgebraicGeometry.Space.affineLimitSquare_iff_qcqsLimitSquare`; Stacks states 0CP4 for a
morphism of algebraic spaces, and it is their sheaf condition which is used. The two chart
systems of Stacks 07SF at a stage — one along an affine étale cover of the stage, one along
an affine étale cover of the self-intersection of that cover — replace the two-stage
separated-then-general induction of the source: the second system is already the system of
test objects for the self-intersections of the first.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)

The same criterion under the chapter's standing convention of Section 70.2 (tag 07SD), which
asks nothing of the index, is
`AlgebraicGeometry.Space.isPullback_qcqsLimitSquare_of_siteContainsBaseChangeLimits`, with its
consequence `AlgebraicGeometry.Space.isPullback_qcqsLimitSquare_of_isLocallyOfFinitePresentation`.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u v z z'

namespace AlgebraicGeometry.Space

/-! ### An elementwise description of the comparison square -/

section Elementwise

variable {K : Type z} [Category.{z'} K] {I : Type u} [Category.{u} I]

/-- Injectivity of the comparison map of a cone, stagewise: two sections over a stage which
agree over the apex and whose images eventually agree already agree at some stage. -/
private def ColimInj (D : I ⥤ K) (c : Cone D) {F G : Kᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (i : I) (x₁ x₂ : F.obj (op (D.obj i))),
    F.map (c.π.app i).op x₁ = F.map (c.π.app i).op x₂ →
    ∀ (j : I) (g : j ⟶ i),
      G.map (D.map g).op (a.app (op (D.obj i)) x₁) =
        G.map (D.map g).op (a.app (op (D.obj i)) x₂) →
      ∃ (k : I) (h : k ⟶ i), F.map (D.map h).op x₁ = F.map (D.map h).op x₂

/-- Surjectivity of the comparison map of a cone, stagewise: a section over the apex whose
image comes from a stage is itself the restriction of a section over some stage. -/
private def ColimSurj (D : I ⥤ K) (c : Cone D) {F G : Kᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (i : I) (x : F.obj (op c.pt)) (y : G.obj (op (D.obj i))),
    a.app (op c.pt) x = G.map (c.π.app i).op y →
      ∃ (j : I) (g : j ⟶ i) (z : F.obj (op (D.obj j))),
        F.map (c.π.app j).op z = x ∧ a.app (op (D.obj j)) z = G.map (D.map g).op y

variable [HasColimitsOfShape Iᵒᵖ (Type v)]

/-- The comparison map of a cone sends the class of a section over a stage to its
restriction to the apex. -/
private theorem desc_ι {D : I ⥤ K} (c : Cone D) (F : Kᵒᵖ ⥤ Type v) (i : Iᵒᵖ)
    (x : (D.op ⋙ F).obj i) :
    colimit.desc (D.op ⋙ F) (F.mapCocone c.op) (colimit.ι (D.op ⋙ F) i x) =
      F.map (c.π.app i.unop).op x := by
  change (colimit.ι (D.op ⋙ F) i ≫ colimit.desc (D.op ⋙ F) (F.mapCocone c.op)) x = _
  rw [colimit.ι_desc]
  rfl

/-- The map of colimits induced by a transformation acts on classes through the
transformation. -/
private theorem colimMap_ι (D : I ⥤ K) {F G : Kᵒᵖ ⥤ Type v} (a : F ⟶ G) (i : Iᵒᵖ)
    (x : (D.op ⋙ F).obj i) :
    colimMap (Functor.whiskerLeft D.op a) (colimit.ι (D.op ⋙ F) i x) =
      colimit.ι (D.op ⋙ G) i (a.app (op (D.obj i.unop)) x) := by
  change (colimit.ι (D.op ⋙ F) i ≫ colimMap (Functor.whiskerLeft D.op a)) x = _
  rw [ι_colimMap]
  rfl

/-- Restricting a section to a later stage does not change its class in the colimit. -/
private theorem ι_eq_of_map (D : I ⥤ K) (F : Kᵒᵖ ⥤ Type v) {i j : I} (g : j ⟶ i)
    (x : F.obj (op (D.obj i))) :
    colimit.ι (D.op ⋙ F) (op j) (F.map (D.map g).op x) =
      colimit.ι (D.op ⋙ F) (op i) x :=
  colimit.w_apply (D.op ⋙ F) (Quiver.Hom.op g) x

variable [IsCofiltered I]

/-- Two sections over one stage have the same class in the colimit exactly when they agree
over some later stage. -/
private theorem ι_eq_iff (D : I ⥤ K) (F : Kᵒᵖ ⥤ Type v) (i : Iᵒᵖ)
    (x₁ x₂ : (D.op ⋙ F).obj i) :
    colimit.ι (D.op ⋙ F) i x₁ = colimit.ι (D.op ⋙ F) i x₂ ↔
      ∃ (j : Iᵒᵖ) (g : i ⟶ j), (D.op ⋙ F).map g x₁ = (D.op ⋙ F).map g x₂ :=
  Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (D.op ⋙ F)) x₁ x₂

/-- Two sections over two stages have the same class in the colimit exactly when they agree
over some common later stage. -/
private theorem ι_eq_iff₂ (D : I ⥤ K) (F : Kᵒᵖ ⥤ Type v) {i j : Iᵒᵖ}
    (x : (D.op ⋙ F).obj i) (y : (D.op ⋙ F).obj j) :
    colimit.ι (D.op ⋙ F) i x = colimit.ι (D.op ⋙ F) j y ↔
      ∃ (k : Iᵒᵖ) (p : i ⟶ k) (q : j ⟶ k),
        (D.op ⋙ F).map p x = (D.op ⋙ F).map q y :=
  Types.FilteredColimit.isColimit_eq_iff (D.op ⋙ F) (colimit.isColimit (D.op ⋙ F))

/-- The comparison square of a cone is cartesian exactly when the two elementwise conditions
`AlgebraicGeometry.Space.ColimInj` and `AlgebraicGeometry.Space.ColimSurj` hold. -/
private theorem isPullback_colim_iff (D : I ⥤ K) (c : Cone D) {F G : Kᵒᵖ ⥤ Type v}
    (a : F ⟶ G) :
    IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
        (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
        (colimit.desc (D.op ⋙ G) (G.mapCocone c.op)) ↔
      ColimInj D c a ∧ ColimSurj D c a := by
  have hw : colimit.desc (D.op ⋙ F) (F.mapCocone c.op) ≫ a.app (op c.pt) =
      colimMap (Functor.whiskerLeft D.op a) ≫
        colimit.desc (D.op ⋙ G) (G.mapCocone c.op) := by
    refine colimit.hom_ext fun i => ?_
    rw [← Category.assoc, colimit.ι_desc, ← Category.assoc, ι_colimMap, Category.assoc,
      colimit.ι_desc]
    exact a.naturality (c.π.app i.unop).op
  rw [Types.isPullback_iff]
  constructor
  · rintro ⟨-, hinj, hsurj⟩
    refine ⟨fun i x₁ x₂ hx j g hg => ?_, fun i x y hxy => ?_⟩
    · have he : colimit.ι (D.op ⋙ F) (op i) x₁ = colimit.ι (D.op ⋙ F) (op i) x₂ := by
        refine hinj _ _ ⟨?_, ?_⟩
        · rw [desc_ι, desc_ι]
          exact hx
        · rw [colimMap_ι, colimMap_ι, ← ι_eq_of_map D G g, ← ι_eq_of_map D G g]
          exact congrArg _ hg
      obtain ⟨k, h, hk⟩ := (ι_eq_iff D F (op i) x₁ x₂).mp he
      exact ⟨k.unop, h.unop, hk⟩
    · have hz : a.app (op c.pt) x =
          colimit.desc (D.op ⋙ G) (G.mapCocone c.op)
            (colimit.ι (D.op ⋙ G) (op i) y) := by
        rw [desc_ι]
        exact hxy
      obtain ⟨e, he₁, he₂⟩ := hsurj x (colimit.ι (D.op ⋙ G) (op i) y) hz
      obtain ⟨j', w, hjw⟩ :=
        Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ F)) e
      rw [colimit.cocone_ι] at hjw
      subst hjw
      rw [desc_ι] at he₁
      rw [colimMap_ι] at he₂
      obtain ⟨k, p, q, hk⟩ := (ι_eq_iff₂ D G _ y).mp he₂
      refine ⟨k.unop, q.unop, F.map (D.map p.unop).op w, ?_, ?_⟩
      · refine Eq.trans ?_ he₁
        change (F.map (D.map p.unop).op ≫ F.map (c.π.app k.unop).op) w = _
        rw [← F.map_comp]
        exact congrArg (fun φ => F.map φ w) (congrArg Quiver.Hom.op (c.w p.unop))
      · refine Eq.trans ?_ hk
        change (F.map (D.map p.unop).op ≫ a.app (op (D.obj k.unop))) w =
          (a.app (op (D.obj j'.unop)) ≫ G.map (D.map p.unop).op) w
        rw [a.naturality (D.map p.unop).op]
  · rintro ⟨hinj, hsurj⟩
    refine ⟨hw, fun e₁ e₂ h => ?_, fun x z hxz => ?_⟩
    · obtain ⟨i, x₁, x₂, h₁', h₂'⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
        (colimit.isColimit (D.op ⋙ F)) e₁ e₂
      rw [colimit.cocone_ι] at h₁' h₂'
      subst h₁'
      subst h₂'
      obtain ⟨hd, hc⟩ := h
      rw [desc_ι, desc_ι] at hd
      rw [colimMap_ι, colimMap_ι] at hc
      obtain ⟨k, g, hk⟩ := (ι_eq_iff D G i _ _).mp hc
      obtain ⟨m, t, ht⟩ := hinj i.unop x₁ x₂ hd k.unop g.unop hk
      rw [← ι_eq_of_map D F t x₁, ← ι_eq_of_map D F t x₂]
      exact congrArg _ ht
    · obtain ⟨i, y, hiy⟩ :=
        Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ G)) z
      rw [colimit.cocone_ι] at hiy
      subst hiy
      rw [desc_ι] at hxz
      obtain ⟨j, g, w, hw₁, hw₂⟩ := hsurj i.unop x y hxz
      refine ⟨colimit.ι (D.op ⋙ F) (op j) w, ?_, ?_⟩
      · rw [desc_ι]
        exact hw₁
      · rw [colimMap_ι]
        refine Eq.trans ?_ (ι_eq_of_map D G g y)
        exact congrArg _ hw₂

end Elementwise

/-! ### Transport of the elementwise conditions -/

section Ulift

variable {K : Type z} [Category.{z'} K] {I : Type u} [Category.{u} I] {D : I ⥤ K}
  {c : Cone D} {F G : Kᵒᵖ ⥤ Type v} (a : F ⟶ G)

universe v'

/-- Lifting the values of a transformation to a larger universe does not change the
stagewise injectivity condition. -/
private theorem colimInj_uliftFunctor_iff :
    ColimInj D c (Functor.whiskerRight a uliftFunctor.{v', v}) ↔ ColimInj D c a := by
  constructor
  · intro h i x₁ x₂ hx j g hg
    obtain ⟨k, p, hp⟩ := h i (ULift.up x₁) (ULift.up x₂) (ULift.ext hx) j g
      (ULift.ext hg)
    exact ⟨k, p, congrArg ULift.down hp⟩
  · intro h i x₁ x₂ hx j g hg
    obtain ⟨k, p, hp⟩ := h i x₁.down x₂.down (congrArg ULift.down hx) j g
      (congrArg ULift.down hg)
    exact ⟨k, p, ULift.ext hp⟩

/-- Lifting the values of a transformation to a larger universe does not change the
stagewise surjectivity condition. -/
private theorem colimSurj_uliftFunctor_iff :
    ColimSurj D c (Functor.whiskerRight a uliftFunctor.{v', v}) ↔ ColimSurj D c a := by
  constructor
  · intro h i x y hxy
    obtain ⟨j, g, z, hz₁, hz₂⟩ := h i (ULift.up x) (ULift.up y) (ULift.ext hxy)
    exact ⟨j, g, z.down, congrArg ULift.down hz₁, congrArg ULift.down hz₂⟩
  · intro h i x y hxy
    obtain ⟨j, g, z, hz₁, hz₂⟩ := h i x.down y.down (congrArg ULift.down hxy)
    exact ⟨j, g, ULift.up z, ULift.ext hz₁, ULift.ext hz₂⟩

end Ulift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_QcqsCriterion :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_QcqsCriterion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site times out at the default
/-- Limits of `u`-small diagrams of presheaves on the big fppf site (instance search times out
without this shortcut). -/
private instance (priority := high) hasLimitsOfShape_presheaf (I : Type u) [Category.{u} I] :
    HasLimitsOfShape I ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### The Yoneda translation of the elementwise conditions -/

section YonedaTransport

variable {I : Type u} [Category.{u} I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)

/-- The affine-limit comparison square of a transformation is cartesian for every
sufficiently small cofiltered inverse system of affine objects of the site. -/
def AffineLimitSquare (f : X ⟶ Y) : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
      #I < B.cutoff.ord.cof → (∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) →
      IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      IsPullback
        (colimit.desc (D.op ⋙ X ⋙ uliftFunctor.{u, u})
          ((X ⋙ uliftFunctor.{u, u}).mapCocone c.op))
        (colimMap (Functor.whiskerLeft D.op (Functor.whiskerRight f uliftFunctor.{u, u})))
        (uliftFunctor.{u, u}.map (f.app (op c.pt)))
        (colimit.desc (D.op ⋙ Y ⋙ uliftFunctor.{u, u})
          ((Y ⋙ uliftFunctor.{u, u}).mapCocone c.op))

/-- The comparison square of morphism sets is cartesian for every sufficiently small
cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces with affine
transition morphisms. -/
def QcqsLimitSquare (f : X ⟶ Y) : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D),
      #I < B.cutoff.ord.cof → (∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
      (∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) →
      IsLimit c →
      IsAlgebraicSpace B S hS c.pt →
      IsPullback
        (colimit.desc (D.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1})
          ((yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
        (colimMap (Functor.whiskerLeft D.op
          (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})))
        (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map f).app (op c.pt)))
        (colimit.desc (D.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1})
          ((yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))

/-- Precomposing a scheme-valued section with a morphism of the site restricts it. -/
private theorem yonedaEquiv_precomp (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {T T' : BigFppfOver B S hS} (φ : T' ⟶ T) (ξ : yoneda.obj T ⟶ Z) :
    yonedaEquiv (yoneda.map φ ≫ ξ) = Z.map φ.op (yonedaEquiv ξ) :=
  (yonedaEquiv_naturality ξ φ).symm

/-- The stagewise injectivity condition for the Yoneda images of two presheaves is the
stagewise injectivity condition for the presheaves themselves. -/
private theorem colimInj_yoneda_iff (f : X ⟶ Y) :
    ColimInj (D ⋙ yoneda) (yoneda.mapCone c) (yoneda.map f) ↔ ColimInj D c f := by
  have hunfold : ColimInj (D ⋙ yoneda) (yoneda.mapCone c) (yoneda.map f) ↔
      ∀ (i : I) (ξ₁ ξ₂ : yoneda.obj (D.obj i) ⟶ X),
        yoneda.map (c.π.app i) ≫ ξ₁ = yoneda.map (c.π.app i) ≫ ξ₂ →
        ∀ (j : I) (g : j ⟶ i),
          yoneda.map (D.map g) ≫ ξ₁ ≫ f = yoneda.map (D.map g) ≫ ξ₂ ≫ f →
          ∃ (k : I) (h : k ⟶ i),
            yoneda.map (D.map h) ≫ ξ₁ = yoneda.map (D.map h) ≫ ξ₂ := Iff.rfl
  rw [hunfold]
  constructor
  · intro h i x₁ x₂ hx j g hg
    have h1 : yoneda.map (c.π.app i) ≫ yonedaEquiv.symm x₁ =
        yoneda.map (c.π.app i) ≫ yonedaEquiv.symm x₂ := by
      refine yonedaEquiv.injective ?_
      rwa [yonedaEquiv_precomp, yonedaEquiv_precomp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    have h2 : yoneda.map (D.map g) ≫ yonedaEquiv.symm x₁ ≫ f =
        yoneda.map (D.map g) ≫ yonedaEquiv.symm x₂ ≫ f := by
      refine yonedaEquiv.injective ?_
      rwa [yonedaEquiv_precomp, yonedaEquiv_precomp, yonedaEquiv_comp, yonedaEquiv_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨k, p, hp⟩ := h i (yonedaEquiv.symm x₁) (yonedaEquiv.symm x₂) h1 j g h2
    refine ⟨k, p, ?_⟩
    have hq := congrArg yonedaEquiv hp
    rwa [yonedaEquiv_precomp, yonedaEquiv_precomp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at hq
  · intro h i ξ₁ ξ₂ hx j g hg
    have h1 : X.map (c.π.app i).op (yonedaEquiv ξ₁) =
        X.map (c.π.app i).op (yonedaEquiv ξ₂) := by
      rw [← yonedaEquiv_precomp, ← yonedaEquiv_precomp]
      exact congrArg yonedaEquiv hx
    have h2 : Y.map (D.map g).op (f.app (op (D.obj i)) (yonedaEquiv ξ₁)) =
        Y.map (D.map g).op (f.app (op (D.obj i)) (yonedaEquiv ξ₂)) := by
      rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, ← yonedaEquiv_precomp,
        ← yonedaEquiv_precomp]
      exact congrArg yonedaEquiv hg
    obtain ⟨k, p, hp⟩ := h i (yonedaEquiv ξ₁) (yonedaEquiv ξ₂) h1 j g h2
    refine ⟨k, p, yonedaEquiv.injective ?_⟩
    rwa [yonedaEquiv_precomp, yonedaEquiv_precomp]

/-- The stagewise surjectivity condition for the Yoneda images of two presheaves is the
stagewise surjectivity condition for the presheaves themselves. -/
private theorem colimSurj_yoneda_iff (f : X ⟶ Y) :
    ColimSurj (D ⋙ yoneda) (yoneda.mapCone c) (yoneda.map f) ↔ ColimSurj D c f := by
  have hunfold : ColimSurj (D ⋙ yoneda) (yoneda.mapCone c) (yoneda.map f) ↔
      ∀ (i : I) (ξ : yoneda.obj c.pt ⟶ X) (η : yoneda.obj (D.obj i) ⟶ Y),
        ξ ≫ f = yoneda.map (c.π.app i) ≫ η →
        ∃ (j : I) (g : j ⟶ i) (ζ : yoneda.obj (D.obj j) ⟶ X),
          yoneda.map (c.π.app j) ≫ ζ = ξ ∧ ζ ≫ f = yoneda.map (D.map g) ≫ η := Iff.rfl
  rw [hunfold]
  constructor
  · intro h i x y hxy
    have h1 : yonedaEquiv.symm x ≫ f = yoneda.map (c.π.app i) ≫ yonedaEquiv.symm y := by
      refine yonedaEquiv.injective ?_
      rwa [yonedaEquiv_comp, yonedaEquiv_precomp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    obtain ⟨j, g, ζ, hz₁, hz₂⟩ := h i (yonedaEquiv.symm x) (yonedaEquiv.symm y) h1
    refine ⟨j, g, yonedaEquiv ζ, ?_, ?_⟩
    · have hq := congrArg yonedaEquiv hz₁
      rwa [yonedaEquiv_precomp, Equiv.apply_symm_apply] at hq
    · have hq := congrArg yonedaEquiv hz₂
      rwa [yonedaEquiv_comp, yonedaEquiv_precomp, Equiv.apply_symm_apply] at hq
  · intro h i ξ η hξη
    have h1 : f.app (op c.pt) (yonedaEquiv ξ) = Y.map (c.π.app i).op (yonedaEquiv η) := by
      rw [← yonedaEquiv_comp, ← yonedaEquiv_precomp]
      exact congrArg yonedaEquiv hξη
    obtain ⟨j, g, z, hz₁, hz₂⟩ := h i (yonedaEquiv ξ) (yonedaEquiv η) h1
    refine ⟨j, g, yonedaEquiv.symm z, yonedaEquiv.injective ?_, yonedaEquiv.injective ?_⟩
    · rwa [yonedaEquiv_precomp, Equiv.apply_symm_apply]
    · rwa [yonedaEquiv_comp, yonedaEquiv_precomp, Equiv.apply_symm_apply]

end YonedaTransport

/-! ### The quasi-compact criterion implies the affine criterion -/

/-- A cofiltered inverse system of affine objects of the site whose underlying schemes have
a given limit cone has that cone as a limit in the site as well. -/
private noncomputable def isLimit_of_isLimit_toScheme {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigFppfOver B S hS) {c : Cone D} (hSize : #I < B.cutoff.ord.cof)
    (hAff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) : IsLimit c := by
  have _ : HasLimit D := BigFppfOver.hasLimit_of_isAffine D hAff hSize
  have _ : PreservesLimit D (BigFppfOver.toScheme B S hS) :=
    BigFppfOver.preservesLimit_toScheme D hAff hSize
  have _ : ReflectsLimit D (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms D (BigFppfOver.toScheme B S hS)
  exact isLimitOfReflects (BigFppfOver.toScheme B S hS) hc

/-- A morphism between affine objects of the site is an affine morphism of algebraic
spaces. -/
private theorem isAffineHom_yoneda_map {T T' : BigFppfOver B S hS} (φ : T ⟶ T')
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    IsAffineHom B S hS (yoneda.map φ) := by
  have _ := hT
  have _ := hT'
  exact isAffineHom_of_presheaf
    ((presheaf_yoneda_map_iff B S hS
        (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance φ).mpr
      (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))

/-! ### Naturality of the projections of a chart system -/

section ChartNaturality

variable {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- The comparison square for cofiltered limits of quasi-compact and quasi-separated
algebraic spaces specializes to the one for cofiltered limits of affine objects. -/
theorem affineLimitSquare_of_qcqsLimitSquare (f : X ⟶ Y)
    (h : QcqsLimitSquare B S hS hZ f) : AffineLimitSquare B S hS f := by
  intro I _ _ D c hSize hHomSize hsl hAff hAffpt
  have hc : IsLimit c := isLimit_of_isLimit_toScheme B S hS D hSize hAff hsl
  have hB := h I (D ⋙ yoneda) (yoneda.mapCone c) hSize hHomSize
    (fun i => isAlgebraicSpace_yoneda B S hS (D.obj i))
    (fun i => isQuasiCompactSpace_yoneda_of_isAffine B S hS (D.obj i) (hAff i))
    (fun i => isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ (D.obj i) (hAff i))
    (fun {i j} a => isAffineHom_yoneda_map B S hS (D.map a) (hAff i) (hAff j))
    (isLimitOfPreserves yoneda hc) (isAlgebraicSpace_yoneda B S hS c.pt)
  have hB' := (isPullback_colim_iff (D ⋙ yoneda) (yoneda.mapCone c)
    (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})).mp hB
  exact (isPullback_colim_iff D c (Functor.whiskerRight f uliftFunctor.{u, u})).mpr
    ⟨(colimInj_uliftFunctor_iff f).mpr
        ((colimInj_yoneda_iff B S hS D c f).mp
          ((colimInj_uliftFunctor_iff (yoneda.map f)).mp hB'.1)),
      (colimSurj_uliftFunctor_iff f).mpr
        ((colimSurj_yoneda_iff B S hS D c f).mp
          ((colimSurj_uliftFunctor_iff (yoneda.map f)).mp hB'.2))⟩

/-- Projecting a chart to its own stage is natural in the stage. -/
private theorem stageMap_naturality (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map (C.siteDiagram.map g) ≫ C.stageMap k = C.stageMap j ≫ D.map g.left := by
  have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g :=
    C.iso.hom.naturality g
  change yoneda.map (C.siteDiagram.map g) ≫
      C.iso.hom.app k ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ k =
    (C.iso.hom.app j ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ j) ≫ D.map g.left
  rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_fst,
    Category.assoc]

/-- Projecting a chart to the chosen point of the base stage is natural in the stage. -/
private theorem baseMap_naturality (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map (C.siteDiagram.map g) ≫ C.baseMap k = C.baseMap j := by
  have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g :=
    C.iso.hom.naturality g
  change yoneda.map (C.siteDiagram.map g) ≫
      C.iso.hom.app k ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ k =
    C.iso.hom.app j ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ j
  rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_snd]

end ChartNaturality

/-! ### The self-intersection of a base-changed atlas -/

section PullbackAlgebra

/-- The chart of a base-changed atlas of the self-intersection covers the self-intersection
of the base-changed atlas, as a base change of the covering of the self-intersection.

Here `A` is the base change of the atlas `U` of `Di` along `m : Dj ⟶ Di`, `R` is the
self-intersection of `U` over `Di`, `R'` is the self-intersection of `A` over `Dj`, `W`
covers `R` by `ω`, and `Bo` is the base change of `W` along `m`. -/
private theorem exists_lift_isPullback {𝒞 : Type z} [Category.{z'} 𝒞]
    {Di Dj U A R R' W Bo : 𝒞}
    {m : Dj ⟶ Di} {f₀ : U ⟶ Di} {uj : A ⟶ Dj} {vj : A ⟶ U}
    (pbU : IsPullback uj vj m f₀)
    {σ τ : R ⟶ U} (pbR : IsPullback σ τ f₀ f₀)
    {σ' τ' : R' ⟶ A} (pbA : IsPullback σ' τ' uj uj)
    {ω : W ⟶ R} {pj : Bo ⟶ Dj} {qj : Bo ⟶ W}
    (pbW : IsPullback pj qj m (ω ≫ σ ≫ f₀))
    {aj bj : Bo ⟶ A}
    (ha₁ : aj ≫ uj = pj) (ha₂ : aj ≫ vj = qj ≫ ω ≫ σ)
    (hb₁ : bj ≫ uj = pj) (hb₂ : bj ≫ vj = qj ≫ ω ≫ τ) :
    ∃ (r : R' ⟶ R) (ρ : Bo ⟶ R'), IsPullback ρ qj r ω ∧ ρ ≫ σ' = aj ∧ ρ ≫ τ' = bj := by
  have hrw : (σ' ≫ vj) ≫ f₀ = (τ' ≫ vj) ≫ f₀ := by
    rw [Category.assoc, Category.assoc, ← pbU.w, ← Category.assoc, ← Category.assoc, pbA.w]
  obtain ⟨r, hrσ, hrτ⟩ : ∃ r : R' ⟶ R, r ≫ σ = σ' ≫ vj ∧ r ≫ τ = τ' ≫ vj :=
    ⟨pbR.lift _ _ hrw, pbR.lift_fst _ _ _, pbR.lift_snd _ _ _⟩
  have hQ1 : IsPullback σ' (τ' ≫ vj) (uj ≫ m) f₀ := pbA.paste_vert pbU
  have hs1 : IsPullback r σ' σ vj := by
    refine IsPullback.of_right ?_ hrσ pbR.flip
    rw [hrτ, ← pbU.w]
    exact hQ1.flip
  have hstep3 : IsPullback (σ' ≫ uj) r m (σ ≫ f₀) := (hs1.paste_vert pbU.flip).flip
  have hρcomm : pj ≫ m = (qj ≫ ω) ≫ σ ≫ f₀ := by
    rw [Category.assoc]
    exact pbW.w
  obtain ⟨ρ, hρ₁, hρ₂⟩ : ∃ ρ : Bo ⟶ R', ρ ≫ (σ' ≫ uj) = pj ∧ ρ ≫ r = qj ≫ ω :=
    ⟨hstep3.lift pj (qj ≫ ω) hρcomm, hstep3.lift_fst _ _ _, hstep3.lift_snd _ _ _⟩
  refine ⟨r, ρ, ?_, pbU.hom_ext ?_ ?_, pbU.hom_ext ?_ ?_⟩
  · refine IsPullback.of_right ?_ hρ₂ hstep3
    rw [hρ₁]
    exact pbW
  · rw [Category.assoc, hρ₁, ha₁]
  · rw [Category.assoc, ← hrσ, ← Category.assoc, hρ₂, ha₂, Category.assoc]
  · rw [Category.assoc, ← pbA.w, hρ₁, hb₁]
  · rw [Category.assoc, ← hrτ, ← Category.assoc, hρ₂, hb₂, Category.assoc]

/-- The bottom edge of a cartesian square may be replaced by an equal morphism. -/
private theorem isPullback_congr_bottom {𝒞 : Type z} [Category.{z'} 𝒞] {P X Y Z : 𝒞}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g g' : Y ⟶ Z} (h : IsPullback fst snd f g)
    (e : g = g') : IsPullback fst snd f g' := e ▸ h

end PullbackAlgebra

/-! ### Atlas data at a stage -/

section StageAtlas

variable {I : Type u} [Category.{u} I]

/-- An affine étale atlas of a stage of an inverse system, together with a represented
self-intersection of that atlas and an affine étale atlas of the self-intersection. -/
private structure StageData (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₀ : I) where
  /-- An affine object of the site covering the stage. -/
  U₀ : BigAffineFppf B S hS
  /-- The covering morphism. -/
  f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀
  /-- The covering morphism is surjective. -/
  surj₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀
  /-- The covering morphism is étale. -/
  etale₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀
  /-- An object of the site representing the self-intersection of the atlas. -/
  R₀ : BigFppfOver B S hS
  /-- Its first projection to the atlas. -/
  s₀ : R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀
  /-- Its second projection to the atlas. -/
  t₀ : R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀
  /-- The two projections exhibit the self-intersection of the atlas. -/
  isPullback₀ : IsPullback (yoneda.map s₀) (yoneda.map t₀) f₀ f₀
  /-- An affine object of the site covering the self-intersection. -/
  W₀ : BigAffineFppf B S hS
  /-- The covering morphism of the self-intersection. -/
  w₀ : (BigAffineFppf.inclusion B S hS).obj W₀ ⟶ R₀
  /-- It is surjective. -/
  surjW : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map w₀)
  /-- It is étale. -/
  etaleW : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map w₀)
  /-- The first test projection of the self-intersection atlas to the atlas. -/
  α : (BigAffineFppf.inclusion B S hS).obj W₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀
  /-- The second test projection of the self-intersection atlas to the atlas. -/
  β : (BigAffineFppf.inclusion B S hS).obj W₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀
  /-- The first test projection is the covering followed by the first projection. -/
  hα : yoneda.map α = yoneda.map w₀ ≫ yoneda.map s₀
  /-- The second test projection is the covering followed by the second projection. -/
  hβ : yoneda.map β = yoneda.map w₀ ≫ yoneda.map t₀
  /-- Both test projections give the same scheme-valued point of the stage. -/
  hαβ : yoneda.map α ≫ f₀ = yoneda.map β ≫ f₀

/-- A quasi-compact and quasi-separated algebraic space stage carries atlas data: Stacks
03H6 provides the affine étale cover, Stacks 0AHR makes its self-intersection
quasi-compact, and Stacks 03H6 applies to that self-intersection in turn. -/
private theorem nonempty_stageData (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₀ : I)
    (hD : IsAlgebraicSpace B S hS (D.obj i₀))
    (hqc : IsQuasiCompactSpace B S hS (D.obj i₀))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i₀)) :
    Nonempty (StageData B S hS D i₀) := by
  obtain ⟨U, f₀, hUaff, hsurj, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i₀) hD).mp hqc
  obtain ⟨R₀, hR₀, ⟨e⟩⟩ :=
    (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ (D.obj i₀) hD).mp
      hqs U U f₀ f₀ hUaff hUaff
  have hpb : IsPullback (yoneda.map (yoneda.preimage (e.hom ≫ pullback.fst f₀ f₀)))
      (yoneda.map (yoneda.preimage (e.hom ≫ pullback.snd f₀ f₀))) f₀ f₀ := by
    rw [yoneda.map_preimage, yoneda.map_preimage]
    exact (IsPullback.of_hasPullback f₀ f₀).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  obtain ⟨W, w, hWaff, hwsurj, hwetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (yoneda.obj R₀)
      (isAlgebraicSpace_yoneda B S hS R₀)).mp (isQuasiCompactSpace_yoneda_obj B S hS hR₀)
  exact ⟨{ U₀ := ⟨U, hUaff⟩, f₀ := f₀, surj₀ := hsurj
           etale₀ := (isEtale_iff_presheaf_of_yoneda B S hS f₀).mp hetale
           R₀ := R₀, s₀ := _, t₀ := _, isPullback₀ := hpb
           W₀ := ⟨W, hWaff⟩, w₀ := yoneda.preimage w
           surjW := by rwa [yoneda.map_preimage]
           etaleW := by
             rw [yoneda.map_preimage]
             exact (isEtale_iff_presheaf_of_yoneda B S hS w).mp hwetale
           α := yoneda.preimage w ≫ yoneda.preimage (e.hom ≫ pullback.fst f₀ f₀)
           β := yoneda.preimage w ≫ yoneda.preimage (e.hom ≫ pullback.snd f₀ f₀)
           hα := Functor.map_comp _ _ _
           hβ := Functor.map_comp _ _ _
           hαβ := by
             rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
               hpb.w] }⟩

end StageAtlas


/-! ### The two chart systems at a stage and their test maps -/

section Descent

variable {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₀ : I)

/-- The chart system of the inverse system at the stage, along its affine étale atlas. -/
private noncomputable def chartU
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    : AffineChartSystem B S hS i₀ D sd.U₀ sd.f₀ :=
  affineChartSystem B S hS i₀ D sd.U₀ sd.f₀ hAffine

/-- The chart system of the inverse system at the stage, along the atlas of the
self-intersection of its affine étale atlas. -/
private noncomputable def chartW
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    : AffineChartSystem B S hS i₀ D sd.W₀ (yoneda.map sd.α ≫ sd.f₀) :=
  affineChartSystem B S hS i₀ D sd.W₀ (yoneda.map sd.α ≫ sd.f₀) hAffine

/-- The first test map, from a chart of the self-intersection atlas to the corresponding
chart of the atlas. -/
private noncomputable def testFst
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    yoneda.obj ((chartW B S hS D i₀ sd hAffine).siteDiagram.obj j) ⟶
      yoneda.obj ((chartU B S hS D i₀ sd hAffine).siteDiagram.obj j) :=
  ((chartU B S hS D i₀ sd hAffine).isPullback j).lift
    ((chartW B S hS D i₀ sd hAffine).stageMap j)
    ((chartW B S hS D i₀ sd hAffine).baseMap j ≫ yoneda.map sd.α)
    (by
      rw [Category.assoc]
      exact ((chartW B S hS D i₀ sd hAffine).isPullback j).w)

/-- The second test map, from a chart of the self-intersection atlas to the corresponding
chart of the atlas. -/
private noncomputable def testSnd
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    yoneda.obj ((chartW B S hS D i₀ sd hAffine).siteDiagram.obj j) ⟶
      yoneda.obj ((chartU B S hS D i₀ sd hAffine).siteDiagram.obj j) :=
  ((chartU B S hS D i₀ sd hAffine).isPullback j).lift
    ((chartW B S hS D i₀ sd hAffine).stageMap j)
    ((chartW B S hS D i₀ sd hAffine).baseMap j ≫ yoneda.map sd.β)
    (by
      rw [Category.assoc, ← sd.hαβ]
      exact ((chartW B S hS D i₀ sd hAffine).isPullback j).w)

/-- The first test map lies over the stage. -/
private theorem testFst_stageMap
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    testFst B S hS D i₀ sd hAffine j ≫ (chartU B S hS D i₀ sd hAffine).stageMap j =
      (chartW B S hS D i₀ sd hAffine).stageMap j :=
  IsPullback.lift_fst _ _ _ _

/-- The first test map covers the first test projection. -/
private theorem testFst_baseMap
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    testFst B S hS D i₀ sd hAffine j ≫ (chartU B S hS D i₀ sd hAffine).baseMap j =
      (chartW B S hS D i₀ sd hAffine).baseMap j ≫ yoneda.map sd.α :=
  IsPullback.lift_snd _ _ _ _

/-- The second test map lies over the stage. -/
private theorem testSnd_stageMap
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    testSnd B S hS D i₀ sd hAffine j ≫ (chartU B S hS D i₀ sd hAffine).stageMap j =
      (chartW B S hS D i₀ sd hAffine).stageMap j :=
  IsPullback.lift_fst _ _ _ _

/-- The second test map covers the second test projection. -/
private theorem testSnd_baseMap
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    testSnd B S hS D i₀ sd hAffine j ≫ (chartU B S hS D i₀ sd hAffine).baseMap j =
      (chartW B S hS D i₀ sd hAffine).baseMap j ≫ yoneda.map sd.β :=
  IsPullback.lift_snd _ _ _ _

/-- The first test map is natural in the stage. -/
private theorem testFst_naturality
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map ((chartW B S hS D i₀ sd hAffine).siteDiagram.map g) ≫
        testFst B S hS D i₀ sd hAffine k =
      testFst B S hS D i₀ sd hAffine j ≫
        yoneda.map ((chartU B S hS D i₀ sd hAffine).siteDiagram.map g) := by
  refine ((chartU B S hS D i₀ sd hAffine).isPullback k).hom_ext ?_ ?_
  · rw [Category.assoc, testFst_stageMap, stageMap_naturality,
      Category.assoc, stageMap_naturality, ← Category.assoc,
      testFst_stageMap]
  · rw [Category.assoc, testFst_baseMap, ← Category.assoc, baseMap_naturality,
      Category.assoc, baseMap_naturality, testFst_baseMap]

/-- The second test map is natural in the stage. -/
private theorem testSnd_naturality
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map ((chartW B S hS D i₀ sd hAffine).siteDiagram.map g) ≫
        testSnd B S hS D i₀ sd hAffine k =
      testSnd B S hS D i₀ sd hAffine j ≫
        yoneda.map ((chartU B S hS D i₀ sd hAffine).siteDiagram.map g) := by
  refine ((chartU B S hS D i₀ sd hAffine).isPullback k).hom_ext ?_ ?_
  · rw [Category.assoc, testSnd_stageMap, stageMap_naturality,
      Category.assoc, stageMap_naturality, ← Category.assoc,
      testSnd_stageMap]
  · rw [Category.assoc, testSnd_baseMap, ← Category.assoc, baseMap_naturality,
      Category.assoc, baseMap_naturality, testSnd_baseMap]

/-- Every chart of the atlas is a surjective chart of its stage. -/
private theorem stageMap_surj
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
      ((chartU B S hS D i₀ sd hAffine).stageMap j) :=
  presheaf_of_isPullback B S hS ((chartU B S hS D i₀ sd hAffine).isPullback j).flip sd.surj₀

/-- Every chart of the atlas is an étale chart of its stage. -/
private theorem stageMap_etale
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (j : Over i₀) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
      ((chartU B S hS D i₀ sd hAffine).stageMap j) :=
  presheaf_of_isPullback B S hS ((chartU B S hS D i₀ sd hAffine).isPullback j).flip sd.etale₀

/-- A section over a chart of the atlas which the two test maps identify descends to the
corresponding stage of the inverse system. -/
private theorem exists_desc
    (sd : StageData B S hS D i₀)
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (j : Over i₀)
    (ξ : yoneda.obj ((chartU B S hS D i₀ sd hAffine).siteDiagram.obj j) ⟶ X)
    (hξ : testFst B S hS D i₀ sd hAffine j ≫ ξ = testSnd B S hS D i₀ sd hAffine j ≫ ξ) :
    ∃ z : D.obj j.left ⟶ X, (chartU B S hS D i₀ sd hAffine).stageMap j ≫ z = ξ := by
  obtain ⟨R', s', t', pbA⟩ := exists_kernelPair_of_etale_atlas B S hS
    ((chartU B S hS D i₀ sd hAffine).stageMap j) (stageMap_etale B S hS D i₀ sd hAffine j)
  have pbW : IsPullback ((chartW B S hS D i₀ sd hAffine).stageMap j)
      ((chartW B S hS D i₀ sd hAffine).baseMap j) (D.map j.hom)
      (yoneda.map sd.w₀ ≫ yoneda.map sd.s₀ ≫ sd.f₀) :=
    isPullback_congr_bottom ((chartW B S hS D i₀ sd hAffine).isPullback j)
      (by rw [← Category.assoc, ← sd.hα])
  obtain ⟨r, ρ, hρpb, hρa, hρb⟩ := exists_lift_isPullback
    ((chartU B S hS D i₀ sd hAffine).isPullback j) sd.isPullback₀ pbA pbW
    (testFst_stageMap B S hS D i₀ sd hAffine j)
    (by rw [testFst_baseMap, ← sd.hα])
    (testSnd_stageMap B S hS D i₀ sd hAffine j)
    (by rw [testSnd_baseMap, ← sd.hβ])
  have hst : yoneda.map s' ≫ ξ = yoneda.map t' ≫ ξ := by
    refine hom_ext_of_etale_atlas B S hS (isAlgebraicSpace_yoneda B S hS R').isSheaf hXsh
      ρ (presheaf_of_isPullback B S hS hρpb.flip sd.surjW)
      (presheaf_of_isPullback B S hS hρpb.flip sd.etaleW) ?_
    rwa [← Category.assoc, ← Category.assoc, hρa, hρb]
  obtain ⟨z, hz, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
    (hD j.left).isSheaf ((chartU B S hS D i₀ sd hAffine).stageMap j) pbA
    (stageMap_surj B S hS D i₀ sd hAffine j) (stageMap_etale B S hS D i₀ sd hAffine j)
    hXsh ξ hst
  exact ⟨z, hz⟩

end Descent

/-! ### The affine criterion on the charts of a stage -/

/-- A slice of an index category has no more morphisms than the category itself. -/
private theorem mk_over_hom_lt {I : Type u} [Category.{u} I]
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) (i₀ : I) (j k : Over i₀) :
    #(j ⟶ k) < B.cutoff.ord.cof :=
  (Cardinal.mk_le_of_injective (show Function.Injective (fun f : j ⟶ k => f.left) from
    fun _ _ h => Over.OverMorphism.ext h)).trans_lt (hHomSize j.left k.left)

/-- The affine criterion along a chart system of a stage and a limit bridge of it: the
comparison map of morphism sets along the charts is injective and surjective stagewise. -/
private def ChartCriterion {I : Type u} [Category.{u} I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge) (f : X ⟶ Y) : Prop :=
  (∀ (j : Over i₀) (ξ₁ ξ₂ : yoneda.obj (C.siteDiagram.obj j) ⟶ X),
      yoneda.map (L.cone.π.app j) ≫ ξ₁ = yoneda.map (L.cone.π.app j) ≫ ξ₂ →
      ∀ (k : Over i₀) (g : k ⟶ j),
        yoneda.map (C.siteDiagram.map g) ≫ ξ₁ ≫ f =
          yoneda.map (C.siteDiagram.map g) ≫ ξ₂ ≫ f →
        ∃ (m : Over i₀) (h : m ⟶ j),
          yoneda.map (C.siteDiagram.map h) ≫ ξ₁ =
            yoneda.map (C.siteDiagram.map h) ≫ ξ₂) ∧
    ∀ (j : Over i₀) (ξ : yoneda.obj L.cone.pt ⟶ X)
        (η : yoneda.obj (C.siteDiagram.obj j) ⟶ Y),
      ξ ≫ f = yoneda.map (L.cone.π.app j) ≫ η →
      ∃ (k : Over i₀) (g : k ⟶ j) (ζ : yoneda.obj (C.siteDiagram.obj k) ⟶ X),
        yoneda.map (L.cone.π.app k) ≫ ζ = ξ ∧
          ζ ≫ f = yoneda.map (C.siteDiagram.map g) ≫ η

/-- Every chart system of a stage of the inverse system `D` has a limit bridge along which the
affine criterion holds. -/
private def ChartBridges {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : X ⟶ Y) : Prop :=
  ∀ (i₀ : I) {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    (C : AffineChartSystem B S hS i₀ D U₀ f₀), ∃ L : C.LimitBridge, ChartCriterion B S hS L f

/-- The affine-limit comparison square of a chart system and a limit bridge of it gives the
affine criterion along the charts. -/
private theorem chartCriterion_of_isPullback {f : X ⟶ Y}
    {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
    (hsq : IsPullback
      (colimit.desc (C.siteDiagram.op ⋙ X ⋙ uliftFunctor.{u, u})
        ((X ⋙ uliftFunctor.{u, u}).mapCocone L.cone.op))
      (colimMap (Functor.whiskerLeft C.siteDiagram.op
        (Functor.whiskerRight f uliftFunctor.{u, u})))
      (uliftFunctor.{u, u}.map (f.app (op L.cone.pt)))
      (colimit.desc (C.siteDiagram.op ⋙ Y ⋙ uliftFunctor.{u, u})
        ((Y ⋙ uliftFunctor.{u, u}).mapCocone L.cone.op))) :
    ChartCriterion B S hS L f := by
  have h := (isPullback_colim_iff C.siteDiagram L.cone
    (Functor.whiskerRight f uliftFunctor.{u, u})).mp hsq
  exact ⟨(colimInj_yoneda_iff B S hS C.siteDiagram L.cone f).mpr
      ((colimInj_uliftFunctor_iff f).mp h.1),
    (colimSurj_yoneda_iff B S hS C.siteDiagram L.cone f).mpr
      ((colimSurj_uliftFunctor_iff f).mp h.2)⟩

/-- The affine criterion, applied to a chart system of a stage and its limit. -/
private theorem chart_square {f : X ⟶ Y} (hA : AffineLimitSquare B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
    (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) :
    ChartCriterion B S hS L f :=
  chartCriterion_of_isPullback B S hS L
    (hA (Over i₀) C.siteDiagram L.cone (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀)
      (mk_over_hom_lt B hHomSize i₀) L.schemeIsLimit C.isAffine_obj L.isAffine_pt)

/-- The stagewise injectivity condition for the Yoneda image of a transformation, written
with morphisms of presheaves. -/
private theorem colimInj_presheaf_iff {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (f : X ⟶ Y) :
    ColimInj D c (yoneda.map f) ↔
      ∀ (i : I) (ξ₁ ξ₂ : D.obj i ⟶ X),
        c.π.app i ≫ ξ₁ = c.π.app i ≫ ξ₂ →
        ∀ (j : I) (g : j ⟶ i), D.map g ≫ ξ₁ ≫ f = D.map g ≫ ξ₂ ≫ f →
        ∃ (k : I) (h : k ⟶ i), D.map h ≫ ξ₁ = D.map h ≫ ξ₂ := Iff.rfl

/-- The stagewise surjectivity condition for the Yoneda image of a transformation, written
with morphisms of presheaves. -/
private theorem colimSurj_presheaf_iff {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (f : X ⟶ Y) :
    ColimSurj D c (yoneda.map f) ↔
      ∀ (i : I) (x : c.pt ⟶ X) (y : D.obj i ⟶ Y),
        x ≫ f = c.π.app i ≫ y →
        ∃ (j : I) (g : j ⟶ i) (z : D.obj j ⟶ X),
          c.π.app j ≫ z = x ∧ z ≫ f = D.map g ≫ y := Iff.rfl

/-! ### The affine criterion implies the quasi-compact criterion -/

/-! ### The criterion -/

/-- Stagewise injectivity of the comparison map, for a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms. -/
private theorem colimInj_limit {f : X ⟶ Y}
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hbr : ChartBridges B S hS D f)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) (x₁ x₂ : D.obj i₀ ⟶ X) (hx : limit.π D i₀ ≫ x₁ = limit.π D i₀ ≫ x₂)
    (j : I) (g : j ⟶ i₀) (hg : D.map g ≫ x₁ ≫ f = D.map g ≫ x₂ ≫ f) :
    ∃ (k : I) (h : k ⟶ i₀), D.map h ≫ x₁ = D.map h ≫ x₂ := by
  obtain ⟨sd⟩ := nonempty_stageData B S hS hZ D i₀ (hD i₀) (hqc i₀) (hqs i₀)
  set CU := chartU B S hS D i₀ sd hAffine
  obtain ⟨LU, hinj, -⟩ := hbr i₀ CU
  have hπ : yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      LU.toLimit ≫ limit.π D i₀ :=
    (LU.toLimit_comp_limitπ (Over.mk (𝟙 i₀))).symm
  have h1 : yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫
        CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₁ =
      yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫
        CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₂ := by
    rw [← Category.assoc, ← Category.assoc, hπ, Category.assoc, Category.assoc, hx]
  set hg0 : Over.mk g ⟶ Over.mk (𝟙 i₀) := Over.homMk g (Category.comp_id g) with hhg0
  have hnat : yoneda.map (CU.siteDiagram.map hg0) ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      CU.stageMap (Over.mk g) ≫ D.map g :=
    stageMap_naturality B S hS CU hg0
  have hstep : ∀ xx : D.obj i₀ ⟶ X,
      yoneda.map (CU.siteDiagram.map hg0) ≫ (CU.stageMap (Over.mk (𝟙 i₀)) ≫ xx) ≫ f =
        CU.stageMap (Over.mk g) ≫ D.map g ≫ xx ≫ f := fun xx => by
    rw [Category.assoc, ← Category.assoc, hnat, Category.assoc]
  have h2 : yoneda.map (CU.siteDiagram.map hg0) ≫
        (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₁) ≫ f =
      yoneda.map (CU.siteDiagram.map hg0) ≫
        (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₂) ≫ f := by
    rw [hstep x₁, hstep x₂, hg]
  obtain ⟨m, h', hm⟩ := hinj (Over.mk (𝟙 i₀)) (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₁)
    (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₂) h1 (Over.mk g) hg0 h2
  refine ⟨m.left, h'.left, ?_⟩
  refine hom_ext_of_etale_atlas B S hS (hD m.left).isSheaf hXsh (CU.stageMap m)
    (stageMap_surj B S hS D i₀ sd hAffine m) (stageMap_etale B S hS D i₀ sd hAffine m) ?_
  have hn : yoneda.map (CU.siteDiagram.map h') ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      CU.stageMap m ≫ D.map h'.left := stageMap_naturality B S hS CU h'
  rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc]
  exact hm

/-- Stagewise surjectivity of the comparison map, for a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms. -/
private theorem colimSurj_limit {f : X ⟶ Y}
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hbr : ChartBridges B S hS D f)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) (x : limit D ⟶ X) (y : D.obj i₀ ⟶ Y)
    (hxy : x ≫ f = limit.π D i₀ ≫ y) :
    ∃ (j : I) (g : j ⟶ i₀) (z : D.obj j ⟶ X),
      limit.π D j ≫ z = x ∧ z ≫ f = D.map g ≫ y := by
  obtain ⟨sd⟩ := nonempty_stageData B S hS hZ D i₀ (hD i₀) (hqc i₀) (hqs i₀)
  set CU := chartU B S hS D i₀ sd hAffine
  set CW := chartW B S hS D i₀ sd hAffine
  obtain ⟨LU, -, hsurjU⟩ := hbr i₀ CU
  obtain ⟨LW, hinjW, -⟩ := hbr i₀ CW
  have hπ0 : LU.toLimit ≫ limit.π D i₀ =
      yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫ CU.stageMap (Over.mk (𝟙 i₀)) :=
    LU.toLimit_comp_limitπ (Over.mk (𝟙 i₀))
  have hc1 : (LU.toLimit ≫ x) ≫ f =
      yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫
        CU.stageMap (Over.mk (𝟙 i₀)) ≫ y := by
    rw [Category.assoc, hxy, ← Category.assoc, hπ0, Category.assoc]
  obtain ⟨k₁, h₁, ξ, hξ₁, hξ₂⟩ := hsurjU (Over.mk (𝟙 i₀)) (LU.toLimit ≫ x)
    (CU.stageMap (Over.mk (𝟙 i₀)) ≫ y) hc1
  have hnat1 : yoneda.map (CU.siteDiagram.map h₁) ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      CU.stageMap k₁ ≫ D.map h₁.left := stageMap_naturality B S hS CU h₁
  have hξ₂' : ξ ≫ f = CU.stageMap k₁ ≫ D.map h₁.left ≫ y := by
    rw [hξ₂, ← Category.assoc, hnat1, Category.assoc]
  have hwA : LW.toLimit ≫ limit.π D i₀ = (LW.toBase ≫ yoneda.map sd.α) ≫ sd.f₀ := by
    rw [Category.assoc]
    exact LW.isPullback.w
  have hwB : LW.toLimit ≫ limit.π D i₀ = (LW.toBase ≫ yoneda.map sd.β) ≫ sd.f₀ := by
    rw [Category.assoc, ← sd.hαβ]
    exact LW.isPullback.w
  obtain ⟨AA, hAA1, hAA2⟩ : ∃ AA : yoneda.obj LW.cone.pt ⟶ yoneda.obj LU.cone.pt,
      AA ≫ LU.toLimit = LW.toLimit ∧ AA ≫ LU.toBase = LW.toBase ≫ yoneda.map sd.α :=
    ⟨LU.isPullback.lift _ _ hwA, LU.isPullback.lift_fst _ _ _, LU.isPullback.lift_snd _ _ _⟩
  obtain ⟨BB, hBB1, hBB2⟩ : ∃ BB : yoneda.obj LW.cone.pt ⟶ yoneda.obj LU.cone.pt,
      BB ≫ LU.toLimit = LW.toLimit ∧ BB ≫ LU.toBase = LW.toBase ≫ yoneda.map sd.β :=
    ⟨LU.isPullback.lift _ _ hwB, LU.isPullback.lift_fst _ _ _, LU.isPullback.lift_snd _ _ _⟩
  have hkeyA : ∀ m : Over i₀, AA ≫ yoneda.map (LU.cone.π.app m) =
      yoneda.map (LW.cone.π.app m) ≫ testFst B S hS D i₀ sd hAffine m := fun m => by
    refine (CU.isPullback m).hom_ext ?_ ?_
    · rw [Category.assoc, ← LU.toLimit_comp_limitπ m, ← Category.assoc, hAA1,
        LW.toLimit_comp_limitπ m, Category.assoc, testFst_stageMap]
    · rw [Category.assoc, LU.baseMap_comp m, hAA2, Category.assoc, testFst_baseMap,
        ← Category.assoc, LW.baseMap_comp m]
  have hkeyB : ∀ m : Over i₀, BB ≫ yoneda.map (LU.cone.π.app m) =
      yoneda.map (LW.cone.π.app m) ≫ testSnd B S hS D i₀ sd hAffine m := fun m => by
    refine (CU.isPullback m).hom_ext ?_ ?_
    · rw [Category.assoc, ← LU.toLimit_comp_limitπ m, ← Category.assoc, hBB1,
        LW.toLimit_comp_limitπ m, Category.assoc, testSnd_stageMap]
    · rw [Category.assoc, LU.baseMap_comp m, hBB2, Category.assoc, testSnd_baseMap,
        ← Category.assoc, LW.baseMap_comp m]
  have hi1 : yoneda.map (LW.cone.π.app k₁) ≫ testFst B S hS D i₀ sd hAffine k₁ ≫ ξ =
      yoneda.map (LW.cone.π.app k₁) ≫ testSnd B S hS D i₀ sd hAffine k₁ ≫ ξ := by
    rw [← Category.assoc, ← hkeyA k₁, ← Category.assoc, ← hkeyB k₁, Category.assoc,
      Category.assoc, hξ₁, ← Category.assoc, ← Category.assoc, hAA1, hBB1]
  have hcomp : ∀ t : yoneda.obj (CW.siteDiagram.obj k₁) ⟶ yoneda.obj (CU.siteDiagram.obj k₁),
      t ≫ CU.stageMap k₁ = CW.stageMap k₁ →
        (t ≫ ξ) ≫ f = CW.stageMap k₁ ≫ D.map h₁.left ≫ y := by
    intro t ht
    rw [Category.assoc, hξ₂', ← Category.assoc, ht]
  have hi2 : (testFst B S hS D i₀ sd hAffine k₁ ≫ ξ) ≫ f =
      (testSnd B S hS D i₀ sd hAffine k₁ ≫ ξ) ≫ f := by
    rw [hcomp _ (testFst_stageMap B S hS D i₀ sd hAffine k₁),
      hcomp _ (testSnd_stageMap B S hS D i₀ sd hAffine k₁)]
  obtain ⟨k₂, h₂, hk₂⟩ := hinjW k₁ (testFst B S hS D i₀ sd hAffine k₁ ≫ ξ)
    (testSnd B S hS D i₀ sd hAffine k₁ ≫ ξ) hi1 k₁ (𝟙 k₁) (by rw [hi2])
  have hdesc : testFst B S hS D i₀ sd hAffine k₂ ≫
        (yoneda.map (CU.siteDiagram.map h₂) ≫ ξ) =
      testSnd B S hS D i₀ sd hAffine k₂ ≫
        (yoneda.map (CU.siteDiagram.map h₂) ≫ ξ) := by
    rw [← Category.assoc, ← testFst_naturality, ← Category.assoc, ← testSnd_naturality,
      Category.assoc, Category.assoc]
    exact hk₂
  obtain ⟨z, hz⟩ := exists_desc B S hS D i₀ sd hAffine hXsh hD k₂
    (yoneda.map (CU.siteDiagram.map h₂) ≫ ξ) hdesc
  refine ⟨k₂.left, h₂.left ≫ h₁.left, z, ?_, ?_⟩
  · refine hom_ext_of_etale_atlas B S hS (isSheaf_limit B S hS D fun i => (hD i).isSheaf)
      hXsh LU.toLimit (presheaf_of_isPullback B S hS LU.isPullback.flip sd.surj₀)
      (presheaf_of_isPullback B S hS LU.isPullback.flip sd.etale₀) ?_
    rw [← Category.assoc, LU.toLimit_comp_limitπ k₂, Category.assoc, hz, ← Category.assoc,
      ← Functor.map_comp, LU.cone.w h₂, hξ₁]
  · refine hom_ext_of_etale_atlas B S hS (hD k₂.left).isSheaf hYsh (CU.stageMap k₂)
      (stageMap_surj B S hS D i₀ sd hAffine k₂)
      (stageMap_etale B S hS D i₀ sd hAffine k₂) ?_
    rw [← Category.assoc, hz, Category.assoc, hξ₂', ← Category.assoc,
      stageMap_naturality, Category.assoc, D.map_comp, Category.assoc]

/-- The comparison square of morphism sets out of the stages of a cofiltered system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms and out of
a limit of it is cartesian, once every chart system of a stage has a limit bridge along which
the affine criterion holds. -/
private theorem isPullback_of_chartBridges {f : X ⟶ Y}
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hbr : ChartBridges B S hS D f)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (c : Cone D) (hc : IsLimit c) :
    IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op
        (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})))
      (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map f).app (op c.pt)))
      (colimit.desc (D.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op)) := by
  obtain ⟨e, he⟩ : ∃ e : c.pt ≅ limit D, ∀ m : I, e.hom ≫ limit.π D m = c.π.app m :=
    ⟨hc.conePointUniqueUpToIso (limit.isLimit D), fun m => by
      simp⟩
  refine (isPullback_colim_iff D c
    (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})).mpr
    ⟨(colimInj_uliftFunctor_iff (yoneda.map f)).mpr ?_,
      (colimSurj_uliftFunctor_iff (yoneda.map f)).mpr ?_⟩
  · refine (colimInj_presheaf_iff B S hS D c f).mpr fun i x₁ x₂ hx j g hg => ?_
    have hx' : limit.π D i ≫ x₁ = limit.π D i ≫ x₂ := by
      have hπ : limit.π D i = e.inv ≫ c.π.app i := by
        rw [← he i, ← Category.assoc, e.inv_hom_id, Category.id_comp]
      rw [hπ, Category.assoc, Category.assoc, hx]
    exact colimInj_limit B S hS hZ hXsh D hbr hD hqc hqs hAffine i x₁ x₂ hx' j g hg
  · refine (colimSurj_presheaf_iff B S hS D c f).mpr fun i x y hxy => ?_
    have hxy' : (e.inv ≫ x) ≫ f = limit.π D i ≫ y := by
      rw [Category.assoc, hxy, ← he i, Category.assoc, ← Category.assoc e.inv e.hom,
        e.inv_hom_id]
      exact Category.id_comp _
    obtain ⟨j, g, z, hz₁, hz₂⟩ := colimSurj_limit B S hS hZ hXsh hYsh D hbr hD hqc hqs hAffine
      i (e.inv ≫ x) y hxy'
    refine ⟨j, g, z, ?_, hz₂⟩
    rw [← he j, Category.assoc, hz₁, ← Category.assoc, e.hom_inv_id]
    exact Category.id_comp _

/-- For a morphism of algebraic spaces over `S`, the affine-limit comparison square is
cartesian for every sufficiently small cofiltered inverse system of affine objects exactly when
the comparison square of morphism sets is cartesian for every sufficiently small cofiltered
inverse system of quasi-compact and quasi-separated algebraic spaces with affine transition
morphisms.

This relates two size-bounded forms of condition (3) of Stacks 0CP4 to each other only. Stacks
0CP4 itself, the equivalence of (3) with local finite presentation and relative limit
preservation, is `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae_qcqsLimitSquare`,
where (3) is read under the chapter's standing convention (tag 07SD). -/
theorem affineLimitSquare_iff_qcqsLimitSquare (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    AffineLimitSquare B S hS f ↔ QcqsLimitSquare B S hS hZ f := by
  refine ⟨fun hA => ?_, affineLimitSquare_of_qcqsLimitSquare B S hS hZ f⟩
  intro I _ _ D c hSize hHomSize hD hqc hqs hAffine hc _
  exact isPullback_of_chartBridges B S hS hZ hX.isSheaf hY.isSheaf D
    (fun i₀ _ _ C => ⟨C.limitBridge hSize hHomSize, chart_square B S hS hA _ hSize hHomSize⟩)
    hD hqc hqs hAffine c hc

/-- A relatively limit preserving morphism of algebraic spaces over `S` satisfies the
comparison condition for cofiltered limits of quasi-compact and quasi-separated algebraic
spaces with affine transition morphisms. -/
theorem qcqsLimitSquare_of_relativelyLimitPreserving (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (h : RelativelyLimitPreserving.{u, u, u, u} B S hS f) :
    QcqsLimitSquare B S hS hZ f :=
  (affineLimitSquare_iff_qcqsLimitSquare B S hS hZ f hX hY).mp
    fun I _ _ D c _ _ hlim haff hafflim =>
      (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mp h
        I D c hlim haff hafflim

/-- A morphism of algebraic spaces over `S` which is locally of finite presentation satisfies
the comparison condition for sufficiently small cofiltered limits of quasi-compact and
quasi-separated algebraic spaces with affine transition morphisms.

This is the implication (1) ⇒ (3) of Stacks 0CP4 for the size-bounded form
`AlgebraicGeometry.Space.QcqsLimitSquare` of (3); the full equivalence is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae_qcqsLimitSquare`. -/
theorem qcqsLimitSquare_of_isLocallyOfFinitePresentation (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    QcqsLimitSquare B S hS hZ f :=
  qcqsLimitSquare_of_relativelyLimitPreserving B S hS hZ f hX hY
    (relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX hY hf)

/-! ### The affine criterion on the charts of a stage, with no smallness -/

/-- The affine criterion of a relatively limit preserving morphism, applied to a chart system of
a stage and a limit of it: the comparison map of morphism sets along the charts is injective and
surjective stagewise. Unlike `chart_square`, no smallness is asked: the affine criterion of a
relatively limit preserving morphism holds for every cofiltered system of affine objects with a
limit in the site, and the limit bridge supplies that limit. -/
private theorem chart_square_of_relativelyLimitPreserving {f : X ⟶ Y}
    (hrlp : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge) :
    (∀ (j : Over i₀) (ξ₁ ξ₂ : yoneda.obj (C.siteDiagram.obj j) ⟶ X),
        yoneda.map (L.cone.π.app j) ≫ ξ₁ = yoneda.map (L.cone.π.app j) ≫ ξ₂ →
        ∀ (k : Over i₀) (g : k ⟶ j),
          yoneda.map (C.siteDiagram.map g) ≫ ξ₁ ≫ f =
            yoneda.map (C.siteDiagram.map g) ≫ ξ₂ ≫ f →
          ∃ (m : Over i₀) (h : m ⟶ j),
            yoneda.map (C.siteDiagram.map h) ≫ ξ₁ =
              yoneda.map (C.siteDiagram.map h) ≫ ξ₂) ∧
      ∀ (j : Over i₀) (ξ : yoneda.obj L.cone.pt ⟶ X)
          (η : yoneda.obj (C.siteDiagram.obj j) ⟶ Y),
        ξ ≫ f = yoneda.map (L.cone.π.app j) ≫ η →
        ∃ (k : Over i₀) (g : k ⟶ j) (ζ : yoneda.obj (C.siteDiagram.obj k) ⟶ X),
          yoneda.map (L.cone.π.app k) ≫ ζ = ξ ∧
            ζ ≫ f = yoneda.map (C.siteDiagram.map g) ≫ η := by
  have hsq := (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mp
    hrlp (Over i₀) C.siteDiagram L.cone L.schemeIsLimit C.isAffine_obj L.isAffine_pt
  have h := (isPullback_colim_iff C.siteDiagram L.cone
    (Functor.whiskerRight f uliftFunctor.{u, u})).mp hsq
  exact ⟨(colimInj_yoneda_iff B S hS C.siteDiagram L.cone f).mpr
      ((colimInj_uliftFunctor_iff f).mp h.1),
    (colimSurj_yoneda_iff B S hS C.siteDiagram L.cone f).mpr
      ((colimSurj_uliftFunctor_iff f).mp h.2)⟩


/-! ### The affine criterion on the charts of a stage, with no smallness -/

/-- The affine criterion of a relatively limit preserving morphism, applied to a chart system of
a stage and a limit of it. Unlike `chart_square`, no smallness is asked: the affine criterion of a
relatively limit preserving morphism holds for every cofiltered system of affine objects with a
limit in the site, and the limit bridge supplies that limit. -/
private theorem chartCriterion_of_relativelyLimitPreserving {f : X ⟶ Y}
    (hrlp : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge) :
    ChartCriterion B S hS L f :=
  chartCriterion_of_isPullback B S hS L
    ((relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mp
      hrlp (Over i₀) C.siteDiagram L.cone L.schemeIsLimit C.isAffine_obj L.isAffine_pt)

/-! ### The criterion under the chapter's standing convention -/

/-- **Stacks 0CP4, under the chapter's standing convention.** For a relatively limit preserving
morphism `f : X ⟶ Y` of algebraic spaces over `S` and a cofiltered inverse system `D` of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms, the
comparison square of morphism sets out of the stages and out of a limit `c` of `D` is
cartesian.

This is the conclusion of `AlgebraicGeometry.Space.QcqsLimitSquare` for the one system `D`, with
the smallness of `D` for the site replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the limits of the affine charts of `D`
lie in the site. Nothing is asked of the index. Smallness entered the proof of
`AlgebraicGeometry.Space.affineLimitSquare_iff_qcqsLimitSquare` only to place the limits of two
chart systems of a stage in the site, which is what the convention grants; and the affine
criterion of a relatively limit preserving morphism needs no smallness at all. -/
theorem isPullback_qcqsLimitSquare_of_siteContainsBaseChangeLimits (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrlp : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D)
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) (hc : IsLimit c) :
    IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op
        (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})))
      (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map f).app (op c.pt)))
      (colimit.desc (D.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op)) := by
  exact isPullback_of_chartBridges B S hS hZ hX.isSheaf hY.isSheaf D
    (fun i₀ _ _ C => ⟨C.limitBridgeOfLimitInSite
      (C.limitInSite_of_siteContainsBaseChangeLimits hconv),
        chartCriterion_of_relativelyLimitPreserving B S hS hrlp _⟩)
    hD hqc hqs hAffine c hc

/-- **Stacks 0CP4 for a morphism locally of finite presentation, under the chapter's standing
convention.** The comparison square of morphism sets is cartesian for every cofiltered inverse
system of quasi-compact and quasi-separated algebraic spaces with affine transition morphisms
whose limits of affine charts lie in the site,
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`; nothing is asked of the index. -/
theorem isPullback_qcqsLimitSquare_of_isLocallyOfFinitePresentation (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D)
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) (hc : IsLimit c) :
    IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op
        (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})))
      (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map f).app (op c.pt)))
      (colimit.desc (D.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op)) :=
  isPullback_qcqsLimitSquare_of_siteContainsBaseChangeLimits B S hS hZ f hX hY
    (relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX hY hf) D c hconv hD
    hqc hqs hAffine hc

end AlgebraicGeometry.Space

end
