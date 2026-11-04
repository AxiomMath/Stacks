module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteArrowSpace

/-!
# Two sections of an algebraic space whose transports agree agree locally

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `X` be
an algebraic space over `S` for `B`, and write `i` for the localized inclusion. Let `γ₁`, `γ₂` be
two sections of `X` over a test object `W` of the smaller site, and let `χ : V ⟶ i W` be a
morphism of the enlarged site along which the two transported sections of `f⁻¹X` restrict to the
same section.

This file proves that `γ₁` and `γ₂` then agree *locally on `V`* after a base change over the
smaller site: along a covering sieve of `V`, the morphism `χ` factors through the image of a
morphism `d : W₂ ⟶ W` with `d^* γ₁ = d^* γ₂`.

The locus where two sections agree is the fibre product of their graphs in the product of the
representable algebraic space of `W` with `X`; that product is formed over the *final*
representable algebraic space, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteArrowSpace`, so that it is again an
algebraic space and so that it stays cartesian after enlarging the big fppf site. The statement is
then the local description of sections of an inverse image of Stacks 04W1 applied to that
algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.pointSpaceSquare`: the product of the representable algebraic space of
  a test object with an algebraic space.
* `AlgebraicGeometry.Space.sectionGraph`: the graph of a section of an algebraic space.
* `AlgebraicGeometry.Space.equalLocus`: the locus where two sections agree.
* `AlgebraicGeometry.Space.equalLocusSection`: the section of the inverse image of the equal locus
  determined by a morphism of the enlarged site along which the two transports agree.

## Main results

* `AlgebraicGeometry.Space.equalLocus_section_eq`: the two sections agree after base change along
  the projection of any section of the equal locus.
* `AlgebraicGeometry.Space.exists_covering_equalLocus_restrict`: **two sections whose transports
  agree along `χ` agree, locally on `V`, after a base change through which `χ` factors.**

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

section Small

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (X : AlgebraicSpaces B S hS) (W : BigFppfOver B S hS)

/-- **The product of the representable algebraic space of a test object with an algebraic
space**, formed as the fibre product over the final representable algebraic space so that it is
again an algebraic space without appeal to products. -/
abbrev pointSpaceSquare : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS
    (toFinalSpace B S hS ((schemeSpaceFunctor B S hS).obj W)) (toFinalSpace B S hS X)

/-- The projection of the product to the representable algebraic space of the test object. -/
abbrev pointSpaceSquareFst : pointSpaceSquare B S hS X W ⟶ (schemeSpaceFunctor B S hS).obj W :=
  ObjectProperty.homMk (pullback.fst (toFinalSpace B S hS ((schemeSpaceFunctor B S hS).obj W)).hom
    (toFinalSpace B S hS X).hom)

/-- The projection of the product to the algebraic space. -/
abbrev pointSpaceSquareSnd : pointSpaceSquare B S hS X W ⟶ X :=
  ObjectProperty.homMk (pullback.snd (toFinalSpace B S hS ((schemeSpaceFunctor B S hS).obj W)).hom
    (toFinalSpace B S hS X).hom)

/-- The product is cartesian over the final representable algebraic space. -/
theorem isPullback_pointSpaceSquare :
    IsPullback (pointSpaceSquareFst B S hS X W) (pointSpaceSquareSnd B S hS X W)
      (toFinalSpace B S hS ((schemeSpaceFunctor B S hS).obj W)) (toFinalSpace B S hS X) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- **The graph of a section** of an algebraic space over a test object: the morphism with
components the identity and the section. -/
def sectionGraph (γ : X.obj.obj (op W)) :
    (schemeSpaceFunctor B S hS).obj W ⟶ pointSpaceSquare B S hS X W :=
  (isPullback_pointSpaceSquare B S hS X W).lift (𝟙 _)
    (ObjectProperty.homMk (yonedaEquiv.symm γ))
    ((toFinalSpace_unique B S hS _).trans (toFinalSpace_unique B S hS _).symm)

/-- The graph of a section has the identity as its first component. -/
theorem sectionGraph_fst (γ : X.obj.obj (op W)) :
    sectionGraph B S hS X W γ ≫ pointSpaceSquareFst B S hS X W = 𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

/-- The graph of a section has that section as its second component. -/
theorem sectionGraph_snd (γ : X.obj.obj (op W)) :
    sectionGraph B S hS X W γ ≫ pointSpaceSquareSnd B S hS X W =
      ObjectProperty.homMk (yonedaEquiv.symm γ) :=
  IsPullback.lift_snd _ _ _ _

/-- **The locus where two sections of an algebraic space agree**, as the fibre product of their
graphs. -/
abbrev equalLocus (γ₁ γ₂ : X.obj.obj (op W)) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (sectionGraph B S hS X W γ₁) (sectionGraph B S hS X W γ₂)

/-- The first projection of the equal locus to the representable algebraic space of the test
object. -/
abbrev equalLocusFst (γ₁ γ₂ : X.obj.obj (op W)) :
    equalLocus B S hS X W γ₁ γ₂ ⟶ (schemeSpaceFunctor B S hS).obj W :=
  ObjectProperty.homMk (pullback.fst (sectionGraph B S hS X W γ₁).hom
    (sectionGraph B S hS X W γ₂).hom)

/-- The second projection of the equal locus to the representable algebraic space of the test
object. -/
abbrev equalLocusSnd (γ₁ γ₂ : X.obj.obj (op W)) :
    equalLocus B S hS X W γ₁ γ₂ ⟶ (schemeSpaceFunctor B S hS).obj W :=
  ObjectProperty.homMk (pullback.snd (sectionGraph B S hS X W γ₁).hom
    (sectionGraph B S hS X W γ₂).hom)

/-- The equal locus is cartesian over the product. -/
theorem isPullback_equalLocus (γ₁ γ₂ : X.obj.obj (op W)) :
    IsPullback (equalLocusFst B S hS X W γ₁ γ₂) (equalLocusSnd B S hS X W γ₁ γ₂)
      (sectionGraph B S hS X W γ₁) (sectionGraph B S hS X W γ₂) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The two projections of the equal locus agree after composing with any map out of the
product. -/
private theorem equalLocus_w_comp_eq {T : AlgebraicSpaces B S hS} (γ₁ γ₂ : X.obj.obj (op W))
    (p : pointSpaceSquare B S hS X W ⟶ T) :
    equalLocusFst B S hS X W γ₁ γ₂ ≫ sectionGraph B S hS X W γ₁ ≫ p =
      equalLocusSnd B S hS X W γ₁ γ₂ ≫ sectionGraph B S hS X W γ₂ ≫ p := by
  rw [← Category.assoc, (isPullback_equalLocus B S hS X W γ₁ γ₂).w, Category.assoc]

/-- The two projections of the equal locus agree, the first component of a graph being the
identity. -/
theorem equalLocusFst_eq_snd (γ₁ γ₂ : X.obj.obj (op W)) :
    equalLocusFst B S hS X W γ₁ γ₂ = equalLocusSnd B S hS X W γ₁ γ₂ := by
  simpa [sectionGraph_fst] using equalLocus_w_comp_eq B S hS X W γ₁ γ₂
    (pointSpaceSquareFst B S hS X W)

/-- The two sections agree after base change along the projection of the equal locus. -/
theorem equalLocus_comp_eq (γ₁ γ₂ : X.obj.obj (op W)) :
    equalLocusFst B S hS X W γ₁ γ₂ ≫ ObjectProperty.homMk (yonedaEquiv.symm γ₁) =
      equalLocusFst B S hS X W γ₁ γ₂ ≫ ObjectProperty.homMk (yonedaEquiv.symm γ₂) := by
  rw [equalLocusFst_eq_snd B S hS X W γ₁ γ₂]
  simpa [sectionGraph_snd, ← equalLocusFst_eq_snd B S hS X W γ₁ γ₂] using
    equalLocus_w_comp_eq B S hS X W γ₁ γ₂ (pointSpaceSquareSnd B S hS X W)

/-- **The two sections agree after base change along the projection of a section of the equal
locus.** -/
theorem equalLocus_section_eq (γ₁ γ₂ : X.obj.obj (op W)) (W₂ : BigFppfOver B S hS)
    (w : (equalLocus B S hS X W γ₁ γ₂).obj.obj (op W₂)) :
    X.obj.map ((equalLocusFst B S hS X W γ₁ γ₂).hom.app (op W₂) w).op γ₁ =
      X.obj.map ((equalLocusFst B S hS X W γ₁ γ₂).hom.app (op W₂) w).op γ₂ := by
  have h0 := congrArg (fun (t : equalLocus B S hS X W γ₁ γ₂ ⟶ X) => t.hom.app (op W₂) w)
    (equalLocus_comp_eq B S hS X W γ₁ γ₂)
  simp only [comp_hom B S hS, NatTrans.comp_app, ConcreteCategory.comp_apply] at h0
  exact ((yonedaEquiv_symm_app_apply γ₁ (op W₂) _).symm.trans h0).trans
    (yonedaEquiv_symm_app_apply γ₂ (op W₂) _)

end Small

section Change

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (W : BigFppfOver B S hS)

/-- The product stays cartesian after enlarging the big fppf site. -/
theorem isPullback_changeBigSite_pointSpaceSquare :
    IsPullback
      ((changeBigSite B B' h S hS).map (pointSpaceSquareFst B S hS X W)).hom
      ((changeBigSite B B' h S hS).map (pointSpaceSquareSnd B S hS X W)).hom
      ((changeBigSite B B' h S hS).map
        (toFinalSpace B S hS ((schemeSpaceFunctor B S hS).obj W))).hom
      ((changeBigSite B B' h S hS).map (toFinalSpace B S hS X)).hom :=
  isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS _ _

/-- The equal locus stays cartesian after enlarging the big fppf site. -/
theorem isPullback_changeBigSite_equalLocus (γ₁ γ₂ : X.obj.obj (op W)) :
    IsPullback
      ((changeBigSite B B' h S hS).map (equalLocusFst B S hS X W γ₁ γ₂)).hom
      ((changeBigSite B B' h S hS).map (equalLocusSnd B S hS X W γ₁ γ₂)).hom
      ((changeBigSite B B' h S hS).map (sectionGraph B S hS X W γ₁)).hom
      ((changeBigSite B B' h S hS).map (sectionGraph B S hS X W γ₂)).hom :=
  isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS _ _

variable (γ₁ γ₂ : X.obj.obj (op W)) (V : BigFppfOver B' S (largerContains h hS))
  (χ : V ⟶ (inclusionOver h S hS).obj W)
  (hγ : ((changeBigSite B B' h S hS).obj X).obj.map χ.op
      (changeBigSiteSectionEquiv B B' h S hS X W γ₁) =
    ((changeBigSite B B' h S hS).obj X).obj.map χ.op
      (changeBigSiteSectionEquiv B B' h S hS X W γ₂))

include hγ in
/-- **The two graphs agree on the restriction of the comparison of Stacks 03FP, part (1).** This
is the compatibility that makes `χ` a section of the inverse image of the equal locus: the two
projections of the product are checked separately, and on the second the comparison turns the
transported section into the restriction of the transported section. -/
theorem changeBigSite_sectionGraph_comm :
    (yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W) ≫
        ((changeBigSite B B' h S hS).map (sectionGraph B S hS X W γ₁)).hom =
      (yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W) ≫
        ((changeBigSite B B' h S hS).map (sectionGraph B S hS X W γ₂)).hom := by
  refine (isPullback_changeBigSite_pointSpaceSquare B B' h S hS X W).hom_ext ?_ ?_
  · refine Eq.trans (yoneda_map_comp_assoc _ _ _ _) (Eq.trans ?_
      (yoneda_map_comp_assoc _ _ _ _).symm)
    refine congrArg (fun g => (yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W) ≫ g) ?_
    refine Eq.trans (changeBigSite_map_comp_hom B B' h S hS _ _) (Eq.trans ?_
      (changeBigSite_map_comp_hom B B' h S hS _ _).symm)
    exact congrArg (fun k : (schemeSpaceFunctor B S hS).obj W ⟶ (schemeSpaceFunctor B S hS).obj W =>
      ((changeBigSite B B' h S hS).map k).hom)
      ((sectionGraph_fst B S hS X W γ₁).trans (sectionGraph_fst B S hS X W γ₂).symm)
  · have key : ∀ γ : X.obj.obj (op W),
        ((yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W) ≫
            ((changeBigSite B B' h S hS).map (sectionGraph B S hS X W γ)).hom) ≫
          ((changeBigSite B B' h S hS).map (pointSpaceSquareSnd B S hS X W)).hom =
        yonedaEquiv.symm (((changeBigSite B B' h S hS).obj X).obj.map χ.op
          (changeBigSiteSectionEquiv B B' h S hS X W γ)) := by
      intro γ
      refine Eq.trans (yoneda_map_comp_assoc _ _ _ _) ?_
      refine Eq.trans (congrArg
        (fun g => (yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W) ≫ g)
        ((changeBigSite_map_comp_hom B B' h S hS _ _).trans
          (congrArg (fun k : (schemeSpaceFunctor B S hS).obj W ⟶ X =>
            ((changeBigSite B B' h S hS).map k).hom) (sectionGraph_snd B S hS X W γ)))) ?_
      refine yonedaEquiv.injective ?_
      refine Eq.trans (yonedaEquiv_restrict_comp χ _ _) ?_
      exact (changeBigSite_map_point_changeBigSiteYonedaHom B B' h S hS X W γ V χ).trans
        (Equiv.apply_symm_apply yonedaEquiv _).symm
    exact (key γ₁).trans ((congrArg yonedaEquiv.symm hγ).trans (key γ₂).symm)

include hγ in
/-- **The section of the inverse image of the equal locus determined by a morphism of the enlarged
site along which the two transports agree.** -/
def equalLocusSection :
    yoneda.obj V ⟶ ((changeBigSite B B' h S hS).obj (equalLocus B S hS X W γ₁ γ₂)).obj :=
  (isPullback_changeBigSite_equalLocus B B' h S hS X W γ₁ γ₂).lift
    (yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W)
    (yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W)
    (changeBigSite_sectionGraph_comm B B' h S hS X W γ₁ γ₂ V χ hγ)

include hγ in
/-- The section projects to the given morphism of the enlarged site. -/
theorem equalLocusSection_fst :
    equalLocusSection B B' h S hS X W γ₁ γ₂ V χ hγ ≫
        ((changeBigSite B B' h S hS).map (equalLocusFst B S hS X W γ₁ γ₂)).hom =
      yoneda.map χ ≫ changeBigSiteYonedaHom B B' h S hS W :=
  IsPullback.lift_fst _ _ _ _

include hγ in
/-- **Two sections of an algebraic space whose transports agree along `χ` agree, locally on the
test object of the enlarged site, after a base change through which `χ` factors.** Along a
covering sieve of `V`, the morphism `χ` factors through the image of a morphism `d : W₂ ⟶ W` of
the smaller site with `d^* γ₁ = d^* γ₂`.

This is the local description of sections of an inverse image of Stacks 04W1, applied to the
algebraic space on which the two sections agree. -/
theorem exists_covering_equalLocus_restrict :
    ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V' ⟶ V⦄, R.arrows β →
        ∃ (W₂ : BigFppfOver B S hS) (d : W₂ ⟶ W) (χ₂ : V' ⟶ (inclusionOver h S hS).obj W₂),
          χ₂ ≫ (inclusionOver h S hS).map d = β ≫ χ ∧
            X.obj.map d.op γ₁ = X.obj.map d.op γ₂ := by
  obtain ⟨W₂, w, R, hR, hspec⟩ := exists_sectionEquiv_restrict B B' h S hS
    (equalLocus B S hS X W γ₁ γ₂) V
    (yonedaEquiv (equalLocusSection B B' h S hS X W γ₁ γ₂ V χ hγ))
  refine ⟨R, hR, ?_⟩
  intro V' β hβ
  obtain ⟨φ, hφ⟩ := hspec β hβ
  refine ⟨W₂, (equalLocusFst B S hS X W γ₁ γ₂).hom.app (op W₂) w, φ, ?_,
    equalLocus_section_eq B S hS X W γ₁ γ₂ W₂ w⟩
  have h1 := congrArg (fun z => ((changeBigSite B B' h S hS).map
    (equalLocusFst B S hS X W γ₁ γ₂)).hom.app (op V') z) hφ
  simp only at h1
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply] at h1
  have e1 : ((changeBigSite B B' h S hS).map (equalLocusFst B S hS X W γ₁ γ₂)).hom.app (op V)
      (yonedaEquiv (equalLocusSection B B' h S hS X W γ₁ γ₂ V χ hγ)) =
      (changeBigSiteYonedaHom B B' h S hS W).app (op V) χ :=
    ((yonedaEquiv_comp _ _).symm.trans (congrArg yonedaEquiv
      (equalLocusSection_fst B B' h S hS X W γ₁ γ₂ V χ hγ))).trans
      (yonedaEquiv_restrict χ (changeBigSiteYonedaHom B B' h S hS W))
  have e2 : ((changeBigSite B B' h S hS).map (equalLocusFst B S hS X W γ₁ γ₂)).hom.app
        (op ((inclusionOver h S hS).obj W₂))
        (changeBigSiteSectionEquiv B B' h S hS (equalLocus B S hS X W γ₁ γ₂) W₂ w) =
      changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj W) W₂
        ((equalLocusFst B S hS X W γ₁ γ₂).hom.app (op W₂) w) :=
    (changeBigSiteSectionEquiv_map B B' h S hS (equalLocusFst B S hS X W γ₁ γ₂) W₂ w).symm
  rw [e1, e2] at h1
  have hinj : Function.Injective ((changeBigSiteYonedaHom B B' h S hS W).app (op V')) := by
    have hio := isIso_changeBigSiteYonedaHom B B' h S hS W
    have : IsIso ((changeBigSiteYonedaHom B B' h S hS W).app (op V')) :=
      NatIso.isIso_app_of_isIso (changeBigSiteYonedaHom B B' h S hS W) (op V')
    exact (ConcreteCategory.bijective_of_isIso _).injective
  refine hinj ?_
  refine Eq.trans (yoneda_naturality_restrict _ ((inclusionOver h S hS).map
    ((equalLocusFst B S hS X W γ₁ γ₂).hom.app (op W₂) w)) φ) ?_
  refine Eq.trans (congrArg (fun z => (((changeBigSite B B' h S hS).obj
    ((schemeSpaceFunctor B S hS).obj W)).obj.map φ.op) z)
    (changeBigSiteYonedaHom_app_map B B' h S hS W W₂
      ((equalLocusFst B S hS X W γ₁ γ₂).hom.app (op W₂) w))) ?_
  exact h1.symm.trans (yoneda_naturality_restrict _ χ β).symm

end Change

end AlgebraicGeometry.Space

end
