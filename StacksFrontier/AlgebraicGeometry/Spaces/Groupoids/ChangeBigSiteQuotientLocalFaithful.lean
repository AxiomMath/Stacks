module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteEqualLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSitePointwiseArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientLocalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseArrowCartesian
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackComparisonLocal

/-!
# The comparison of quotient stacks identifies only locally equal morphisms

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G` be
a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and write `i` for the
localized inclusion. This file proves the injectivity half of clause (1) of Stacks 02ZN for the
canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.

The generic reduction of
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackComparisonLocal` turns that
statement into one about two morphisms of a single fibre of `[U/R]`, together with a strongly
cartesian morphism of `[f⁻¹U/f⁻¹R]` over `φ : V ⟶ i U` identifying their images. What remains is
geometry: both objects of the fibre are, locally on `V`, presented by points of the object space
over one test object `W` of the smaller site, and the two morphisms then correspond to two arrows
of the groupoid of points at `W`, by part (2) of Stacks 044X. The hypothesis says that the two
transported arrows of `f⁻¹G` agree after restriction along the factoring morphism `V₁ ⟶ i W`, so
the two arrows agree locally on `V₁` after a base change over the smaller site, by the local
description of sections of an inverse image applied to the locus where they agree.

## Main results

* `AlgebraicGeometry.Stack.isStronglyCartesian_presentedComparison` and
  `AlgebraicGeometry.Stack.presentedComparison_comp_fiberInclusion`: the presenting isomorphism
  followed by the chosen cartesian lift of `d` is strongly cartesian over `d`, and computes a
  morphism of the fibre in terms of the arrow of the groupoid of points presenting it.
* `AlgebraicGeometry.Stack.exists_presentedArrow`: part (2) of Stacks 044X, in the form that names
  the arrow presenting a morphism of a fibre.
* `AlgebraicGeometry.Stack.pullbackFiberHom_eq_of_presented_arrow_restrict`: two morphisms of a
  fibre of `[U/R]` agree after base change along `d₂ ≫ d` as soon as the arrows of the groupoid of
  points presenting their base changes along `d` agree after restriction along `d₂`.
* `AlgebraicGeometry.Stack.exists_covering_presented_fiberPair`: two objects of one fibre of
  `[U/R]` are, locally on a test object of the enlarged site, presented by points of the object
  space over one test object of the smaller site.
* `AlgebraicGeometry.Stack.changeBigSiteGroupoidHom_evaluation_arrow`: the transport of an arrow
  of the groupoid of points is the transport of the section of the arrow space representing it.
* `AlgebraicGeometry.Stack.changeBigSite_arrow_restrict_eq`: the hypothesis of local faithfulness,
  transported to the groupoid of points of `f⁻¹G`.
* `AlgebraicGeometry.Stack.hfib_changeBigSiteQuotientMap`: the geometric input of the reduction.
* `AlgebraicGeometry.Stack.locallyEqual_changeBigSiteQuotientComparison`: the injectivity half of
  clause (1) of Stacks 02ZN for the canonical comparison.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Deformation

namespace AlgebraicGeometry.Stack

universe u

section SmallSite

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bs : AlgebraicSpaces C S hS}

/-- **The presenting isomorphism followed by the chosen cartesian lift of `d` is strongly
cartesian over `d`.** An isomorphism of the fibre over `W` lies over an identity, which does not
change the morphism of the base a strongly cartesian morphism lies over. -/
theorem isStronglyCartesian_presentedComparison
    (G : GroupoidInAlgebraicSpaces C S hS Bs) {U W : BigFppfOver C S hS}
    {A : (quotientStack G).p.Fiber U} (d : W ⟶ U)
    {a : G.toGroupoidInFunctors.Evaluation (op W)}
    (e : Functor.FiberIso (presentedFiber G W a)
      (Functor.pullbackFiber (quotientStack G).p A d)) :
    (quotientStack G).p.IsStronglyCartesian d
      (Functor.Fiber.fiberInclusion.map e.iso.hom ≫
        Functor.IsPreFibered.pullbackMap A.2 d) := by
  have hA : (quotientStack G).p.IsStronglyCartesian d
      (Functor.IsPreFibered.pullbackMap A.2 d) := by
    have := Functor.IsPreFibered.pullbackMap.IsCartesian A.2 d
    infer_instance
  have hlift : (quotientStack G).p.IsHomLift (𝟙 W)
      (Functor.Fiber.fiberInclusion.map e.iso.hom) := e.iso.hom.2
  have hiso : IsIso (Functor.Fiber.fiberInclusion.map e.iso.hom) := inferInstance
  exact PullbackAdjunction.isStronglyCartesian_id_comp
    (Functor.IsStronglyCartesian.of_isIso _ (𝟙 W) _) hA

/-- **The arrow of the groupoid of points presenting a morphism of a fibre computes that morphism
after the presenting comparisons.** The chosen cartesian lift of `d` turns the morphism of the
fibre into the base change of that morphism, which the two presenting isomorphisms conjugate into
the image of the arrow. -/
theorem presentedComparison_comp_fiberInclusion
    (G : GroupoidInAlgebraicSpaces C S hS Bs) {U W : BigFppfOver C S hS}
    {A Bo : (quotientStack G).p.Fiber U} (n : A ⟶ Bo) (d : W ⟶ U)
    {a a' : G.toGroupoidInFunctors.Evaluation (op W)}
    (e : Functor.FiberIso (presentedFiber G W a)
      (Functor.pullbackFiber (quotientStack G).p A d))
    (e' : Functor.FiberIso (presentedFiber G W a')
      (Functor.pullbackFiber (quotientStack G).p Bo d))
    (δ : a ⟶ a')
    (hδ : (pointwiseToQuotientStackFiber G W).map δ =
      e.iso.hom ≫ Functor.pullbackFiberHom n d ≫ e'.iso.inv) :
    (Functor.Fiber.fiberInclusion.map e.iso.hom ≫
          Functor.IsPreFibered.pullbackMap A.2 d) ≫ Functor.Fiber.fiberInclusion.map n =
      (pointwiseToQuotientStack G).map
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' W).map δ) ≫
        (Functor.Fiber.fiberInclusion.map e'.iso.hom ≫
          Functor.IsPreFibered.pullbackMap Bo.2 d) := by
  have hfib : e.iso.hom ≫ Functor.pullbackFiberHom n d =
      (pointwiseToQuotientStackFiber G W).map δ ≫ e'.iso.hom := by
    refine Eq.trans ?_ (congrArg (fun t => t ≫ e'.iso.hom) hδ.symm)
    refine Eq.trans ?_ (Category.assoc e.iso.hom _ e'.iso.hom).symm
    refine congrArg (fun t => e.iso.hom ≫ t) ?_
    refine Eq.trans ?_ (Category.assoc (Functor.pullbackFiberHom n d) _ _).symm
    exact ((congrArg (fun t => Functor.pullbackFiberHom n d ≫ t)
      e'.iso.inv_hom_id).trans (Category.comp_id _)).symm
  have hincl : Functor.Fiber.fiberInclusion.map
        ((pointwiseToQuotientStackFiber G W).map δ) =
      (pointwiseToQuotientStack G).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' W).map δ) := rfl
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => Functor.Fiber.fiberInclusion.map e.iso.hom ≫ t)
    (Functor.pullbackFiberHom_fac n d).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap Bo.2 d)
    (Functor.map_comp Functor.Fiber.fiberInclusion e.iso.hom
      (Functor.pullbackFiberHom n d)).symm) ?_
  refine Eq.trans (congrArg (fun t => Functor.Fiber.fiberInclusion.map t ≫
    Functor.IsPreFibered.pullbackMap Bo.2 d) hfib) ?_
  refine Eq.trans (congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap Bo.2 d)
    (Functor.map_comp Functor.Fiber.fiberInclusion
      ((pointwiseToQuotientStackFiber G W).map δ) e'.iso.hom)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun t => t ≫ Functor.Fiber.fiberInclusion.map e'.iso.hom ≫
    Functor.IsPreFibered.pullbackMap Bo.2 d) hincl

/-- **Two morphisms of a fibre of `[U/R]` agree after base change along `d₂ ≫ d` as soon as the
two arrows of the groupoid of points presenting their base changes along `d` agree after
restriction along `d₂`.**

The chosen cartesian lift of `d₂` at the presenting point maps to a strongly cartesian morphism of
`[U/R]`, which composed with the presenting isomorphism and the chosen cartesian lift of `d` is
strongly cartesian over `d₂ ≫ d`; the two morphisms of the fibre agree after it because the two
arrows do, and a strongly cartesian morphism over `d₂ ≫ d` pins down the base change. -/
theorem pullbackFiberHom_eq_of_presented_arrow_restrict
    (G : GroupoidInAlgebraicSpaces C S hS Bs) {U W W₂ : BigFppfOver C S hS}
    {A Bo : (quotientStack G).p.Fiber U} (n₁ n₂ : A ⟶ Bo) (d : W ⟶ U)
    {a a' : G.toGroupoidInFunctors.Evaluation (op W)}
    (e : Functor.FiberIso (presentedFiber G W a)
      (Functor.pullbackFiber (quotientStack G).p A d))
    (e' : Functor.FiberIso (presentedFiber G W a')
      (Functor.pullbackFiber (quotientStack G).p Bo d))
    (δ₁ δ₂ : a ⟶ a')
    (hδ₁ : (pointwiseToQuotientStackFiber G W).map δ₁ =
      e.iso.hom ≫ Functor.pullbackFiberHom n₁ d ≫ e'.iso.inv)
    (hδ₂ : (pointwiseToQuotientStackFiber G W).map δ₂ =
      e.iso.hom ≫ Functor.pullbackFiberHom n₂ d ≫ e'.iso.inv)
    (d₂ : W₂ ⟶ W)
    (harr : G.arrows.obj.map d₂.op
          (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ₁).1 =
        G.arrows.obj.map d₂.op
          (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ₂).1) :
    Functor.pullbackFiberHom n₁ (d₂ ≫ d) = Functor.pullbackFiberHom n₂ (d₂ ≫ d) := by
  have hcL : (quotientStack G).p.IsStronglyCartesian d₂
      ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
        (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor') a d₂)) :=
    (isFibredOneMorphism_pointwiseToQuotientStack G).map_isStronglyCartesian d₂ _
      (CoGrothendieck.isStronglyCartesian_homCartesianLift
        (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor') a d₂)
  have hkey := (pointwiseToQuotientStack_comp_ι_map_eq_iff G δ₁ δ₂ d₂
    ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
      (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor') a d₂)) hcL).2 harr
  have htail : (quotientStack G).p.IsStronglyCartesian d
      (Functor.Fiber.fiberInclusion.map e.iso.hom ≫ Functor.IsPreFibered.pullbackMap A.2 d) :=
    isStronglyCartesian_presentedComparison G d e
  have hΛ : (quotientStack G).p.IsStronglyCartesian (d₂ ≫ d)
      ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
          (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂) ≫
        (Functor.Fiber.fiberInclusion.map e.iso.hom ≫
          Functor.IsPreFibered.pullbackMap A.2 d)) :=
    @Functor.IsStronglyCartesian.comp _ _ _ _ (quotientStack G).p _ _ _ _ _ _ d₂ d _ _ hcL htail
  refine Functor.pullbackFiberHom_eq_of_comp_eq n₁ n₂ (d₂ ≫ d) _ hΛ ?_
  erw [Category.assoc, presentedComparison_comp_fiberInclusion G n₁ d e e' δ₁ hδ₁,
    Category.assoc, presentedComparison_comp_fiberInclusion G n₂ d e e' δ₂ hδ₂,
    ← Category.assoc, ← Category.assoc, hkey]
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

/-- **A morphism of a fibre of `[U/R]` whose source and target are presented by points comes from
an arrow of the groupoid of points**, after base change along `d` and conjugation by the two
presenting isomorphisms. This is part (2) of Stacks 044X. -/
theorem exists_presentedArrow (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U W : BigFppfOver C S hS} {A Bo : (quotientStack G).p.Fiber U} (n : A ⟶ Bo) (d : W ⟶ U)
    {a a' : G.toGroupoidInFunctors.Evaluation (op W)}
    (e : Functor.FiberIso (presentedFiber G W a)
      (Functor.pullbackFiber (quotientStack G).p A d))
    (e' : Functor.FiberIso (presentedFiber G W a')
      (Functor.pullbackFiber (quotientStack G).p Bo d)) :
    ∃ δ : a ⟶ a', (pointwiseToQuotientStackFiber G W).map δ =
      e.iso.hom ≫ Functor.pullbackFiberHom n d ≫ e'.iso.inv :=
  ⟨(fullyFaithful_pointwiseToQuotientStackFiber G W).some.preimage
      (e.iso.hom ≫ Functor.pullbackFiberHom n d ≫ e'.iso.inv),
    (fullyFaithful_pointwiseToQuotientStackFiber G W).some.map_preimage _⟩

end SmallSite

section Change

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **Two objects of one fibre of `[U/R]` are presented by points of the object space over one
test object of the smaller site, locally on a test object of the enlarged site.** Along a covering
sieve of `V`, the morphism `φ` factors through the image of a test object `W` of the smaller site
over which both base changes are presented by points.

The covering sieve is the one transferred from the smaller site, the localized inclusion being
continuous, from the intersection of the two sieves of part (1) of Stacks 044X. -/
theorem exists_covering_presented_fiberPair (U : BigFppfOver B S hS)
    (A Bo : (quotientStack G).p.Fiber U) (V : BigFppfOver B' S (largerContains h hS))
    (φ : V ⟶ (inclusionOver h S hS).obj U) :
    ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (W : BigFppfOver B S hS) (d : W ⟶ U) (χ : V₁ ⟶ (inclusionOver h S hS).obj W)
          (a a' : G.toGroupoidInFunctors.Evaluation (op W)),
          β ≫ φ = χ ≫ (inclusionOver h S hS).map d ∧
          Nonempty (Functor.FiberIso (presentedFiber G W a)
            (Functor.pullbackFiber (quotientStack G).p A d)) ∧
          Nonempty (Functor.FiberIso (presentedFiber G W a')
            (Functor.pullbackFiber (quotientStack G).p Bo d)) := by
  have hcont : (inclusionOver h S hS).IsContinuous (BigFppfOver.topology B S hS)
      (BigFppfOver.topology B' S (largerContains h hS)) :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  obtain ⟨R₁, hR₁, hspec₁⟩ := exists_covering_presented G U A
  obtain ⟨R₂, hR₂, hspec₂⟩ := exists_covering_presented G U Bo
  refine ⟨_, mem_pullback_functorPushforward (inclusionOver h S hS)
    (BigFppfOver.topology B S hS) (BigFppfOver.topology B' S (largerContains h hS))
    ((BigFppfOver.topology B S hS).intersection_covering hR₁ hR₂) φ, ?_⟩
  intro V₁ β hβ
  obtain ⟨W, d, χ, hd, hfac⟩ :=
    exists_factorisation_of_mem_pullback_functorPushforward (inclusionOver h S hS) φ hβ
  obtain ⟨a, ha⟩ := hspec₁ hd.1
  obtain ⟨a', ha'⟩ := hspec₂ hd.2
  exact ⟨W, d, χ, a, a', hfac, ha, ha'⟩

/-- **The transport of an arrow of the groupoid of points is the transport of the section of the
arrow space that represents it.** -/
theorem changeBigSiteGroupoidHom_evaluation_arrow (W : BigFppfOver B S hS)
    {a a' : G.toGroupoidInFunctors.Evaluation (op W)} (δ : a ⟶ a') :
    ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
          (op ((inclusionOver h S hS).obj W)) _ _
          (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map δ)).1 =
      changeBigSiteSectionEquiv B B' h S hS G.arrows W
        (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ).1 :=
  GroupoidInFunctors.Hom.evaluation_map_arrow (changeBigSiteGroupoidHom B B' h S hS G) (op W) δ
/-- **The hypothesis of local faithfulness, transported to the groupoid of points of `f⁻¹G`.**
If a strongly cartesian morphism over `χ ≫ i d` identifies the images under
`[U/R] ⟶ [f⁻¹U/f⁻¹R]` of two morphisms of a fibre of `[U/R]` whose base changes along `d` are
presented by two arrows of the groupoid of points, then the two transported arrows of `f⁻¹G` agree
after restriction along `χ`.

The strongly cartesian morphism factors through the image of the presenting comparison at the
source, and the image of the presenting comparison at the target cancels, leaving two morphisms
out of the image of a presented object. The 2-isomorphism exhibiting `[U/R] ⟶ [f⁻¹U/f⁻¹R]` on
presented objects turns these into the two morphisms of `[f⁻¹U/f⁻¹R]` given by the transported
arrows, which a strongly cartesian morphism over `χ` distinguishes exactly as the restricted
sections of the arrow space do. -/
theorem changeBigSite_arrow_restrict_eq
    {U W : BigFppfOver B S hS} {A Bo : (quotientStack G).p.Fiber U} (n₁ n₂ : A ⟶ Bo)
    (d : W ⟶ U) {a a' : G.toGroupoidInFunctors.Evaluation (op W)}
    (e : Functor.FiberIso (presentedFiber G W a)
      (Functor.pullbackFiber (quotientStack G).p A d))
    (e' : Functor.FiberIso (presentedFiber G W a')
      (Functor.pullbackFiber (quotientStack G).p Bo d))
    (δ₁ δ₂ : a ⟶ a')
    (hδ₁ : (pointwiseToQuotientStackFiber G W).map δ₁ =
      e.iso.hom ≫ Functor.pullbackFiberHom n₁ d ≫ e'.iso.inv)
    (hδ₂ : (pointwiseToQuotientStackFiber G W).map δ₂ =
      e.iso.hom ≫ Functor.pullbackFiberHom n₂ d ≫ e'.iso.inv)
    {V₁ : BigFppfOver B' S (largerContains h hS)} (χ : V₁ ⟶ (inclusionOver h S hS).obj W)
    {z : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj}
    (M : z ⟶ (changeBigSiteQuotientMap B B' h S hS G).obj A.1)
    (hM : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
      (χ ≫ (inclusionOver h S hS).map d) M)
    (hyp : M ≫ (changeBigSiteQuotientMap B B' h S hS G).map
          (Functor.Fiber.fiberInclusion.map n₁) =
        M ≫ (changeBigSiteQuotientMap B B' h S hS G).map
          (Functor.Fiber.fiberInclusion.map n₂)) :
    ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ.op
        (changeBigSiteSectionEquiv B B' h S hS G.arrows W
          (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ₁).1) =
      ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ.op
        (changeBigSiteSectionEquiv B B' h S hS G.arrows W
          (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ₂).1) := by
  have hvert : ∀ δ : a ⟶ a', (quotientStack G).p.IsHomLift (𝟙 W)
      ((pointwiseToQuotientStack G).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' W).map δ)) :=
    fun δ => ((pointwiseToQuotientStackFiber G W).map δ).2
  obtain ⟨κ, hκcart, hκeq⟩ := Functor.exists_isStronglyCartesian_factor_of_comp_eq
    (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)
    (isStronglyCartesian_presentedComparison G d e)
    (isStronglyCartesian_presentedComparison G d e') M hM (hvert δ₁) (hvert δ₂)
    (presentedComparison_comp_fiberInclusion G n₁ d e e' δ₁ hδ₁)
    (presentedComparison_comp_fiberInclusion G n₂ d e e' δ₂ hδ₂) hyp
  -- read the two morphisms through the 2-isomorphism at the presented objects
  have hμcart : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian χ
      (κ ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
        ((quotientPrestackEquivalence G).functor.obj
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' W).obj a))) :=
    Functor.isStronglyCartesian_comp_isoOverId hκcart _
      (isHomLift_changeBigSiteQuotientMapUnit_hom_app B B' h S hS G
        ((quotientPrestackEquivalence G).functor.obj
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' W).obj a)))
      (NatIso.isIso_app_of_isIso (changeBigSiteQuotientMapUnit B B' h S hS G).hom _)
  have hconv : ∀ δ : a ⟶ a',
      (κ ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
            ((quotientPrestackEquivalence G).functor.obj
              ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor' W).obj a))) ≫
          (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).map
            ((CoGrothendieck.ι (evaluationGroupoidFunctor
                  (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor' ((inclusionOver h S hS).obj W)).map
              (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map δ)) =
        (κ ≫ (changeBigSiteQuotientMap B B' h S hS G).map
            ((pointwiseToQuotientStack G).map
              ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor' W).map δ))) ≫
          (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
            ((quotientPrestackEquivalence G).functor.obj
              ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor' W).obj a')) := by
    intro δ
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun t => κ ≫ t)
      (changeBigSiteQuotientMap_map_pointwiseToQuotientStack B B' h S hS G W δ).symm) ?_
    exact (Category.assoc _ _ _).symm
  have hμeq := (hconv δ₁).trans
    ((congrArg (fun t => t ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
      ((quotientPrestackEquivalence G).functor.obj
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' W).obj a'))) hκeq).trans (hconv δ₂).symm)
  have hfinal := (pointwiseToQuotientStack_comp_ι_map_eq_iff
    (changeBigSiteGroupoid B B' h S hS G)
    (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map δ₁)
    (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map δ₂) χ _ hμcart).1 hμeq
  rw [changeBigSiteGroupoidHom_evaluation_arrow B B' h S hS G W δ₁,
    changeBigSiteGroupoidHom_evaluation_arrow B B' h S hS G W δ₂] at hfinal
  exact hfinal

/-- **The geometric input of the reduction of local faithfulness.** For two morphisms of one fibre
of `[U/R]` and a strongly cartesian morphism of `[f⁻¹U/f⁻¹R]` over `φ : V ⟶ i U` identifying their
images, the base changes of the two morphisms agree along a covering sieve of `V`, after a base
change over the smaller site through which `φ` factors.

The covering sieve is the composite of the one along which both objects of the fibre are presented
by points of the object space over one test object of the smaller site with, over each of its
members, the one along which the two arrows presenting the two morphisms agree after a base change
over the smaller site. -/
theorem hfib_changeBigSiteQuotientMap (U : BigFppfOver B S hS)
    (A Bo : (quotientStack G).p.Fiber U) (n₁ n₂ : A ⟶ Bo)
    (V : BigFppfOver B' S (largerContains h hS)) (φ : V ⟶ (inclusionOver h S hS).obj U)
    (z : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj)
    (μ : z ⟶ (changeBigSiteQuotientMap B B' h S hS G).obj A.1)
    (hμ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian φ μ)
    (hyp : μ ≫ (changeBigSiteQuotientMap B B' h S hS G).map
          (Functor.Fiber.fiberInclusion.map n₁) =
        μ ≫ (changeBigSiteQuotientMap B B' h S hS G).map
          (Functor.Fiber.fiberInclusion.map n₂)) :
    ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (W : BigFppfOver B S hS) (d : W ⟶ U) (φ₁ : V₁ ⟶ (inclusionOver h S hS).obj W),
          φ₁ ≫ (inclusionOver h S hS).map d = β ≫ φ ∧
          Functor.pullbackFiberHom n₁ d = Functor.pullbackFiberHom n₂ d := by
  obtain ⟨T₁, hT₁, hspec₁⟩ := exists_covering_presented_fiberPair B B' h S hS G U A Bo V φ
  have key : ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T₁.arrows β →
      ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V₁,
        ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ ⦃β' : V' ⟶ V₁⦄, R.arrows β' →
          ∃ (W : BigFppfOver B S hS) (d : W ⟶ U) (φ₁ : V' ⟶ (inclusionOver h S hS).obj W),
            φ₁ ≫ (inclusionOver h S hS).map d = (β' ≫ β) ≫ φ ∧
            Functor.pullbackFiberHom n₁ d = Functor.pullbackFiberHom n₂ d := by
    intro V₁ β hβ
    obtain ⟨W, d, χ, a, a', hfac, ⟨e⟩, ⟨e'⟩⟩ := hspec₁ hβ
    obtain ⟨δ₁, hδ₁⟩ := exists_presentedArrow G n₁ d e e'
    obtain ⟨δ₂, hδ₂⟩ := exists_presentedArrow G n₂ d e e'
    -- restrict the strongly cartesian morphism along `β`
    obtain ⟨z₁, ν, hν, hM⟩ := Functor.exists_isStronglyCartesian_restrict
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p β φ μ hμ
    have hM' : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
        (χ ≫ (inclusionOver h S hS).map d) (ν ≫ μ) := by
      rw [← hfac]; exact hM
    have hyp' : (ν ≫ μ) ≫ (changeBigSiteQuotientMap B B' h S hS G).map
          (Functor.Fiber.fiberInclusion.map n₁) =
        (ν ≫ μ) ≫ (changeBigSiteQuotientMap B B' h S hS G).map
          (Functor.Fiber.fiberInclusion.map n₂) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t => ν ≫ t) hyp).trans (Category.assoc _ _ _).symm)
    have hγ := changeBigSite_arrow_restrict_eq B B' h S hS G n₁ n₂ d e e' δ₁ δ₂ hδ₁ hδ₂
      χ (ν ≫ μ) hM' hyp'
    obtain ⟨R, hR, hspec⟩ := Space.exists_covering_equalLocus_restrict B B' h S hS G.arrows W
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ₁).1
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op W) a a' δ₂).1 V₁ χ hγ
    refine ⟨R, hR, ?_⟩
    intro V' β' hβ'
    obtain ⟨W₂, d₂, χ₂, hfac₂, harr⟩ := hspec hβ'
    refine ⟨W₂, d₂ ≫ d, χ₂, ?_, ?_⟩
    · refine Eq.trans (congrArg (fun t => χ₂ ≫ t)
        (Functor.map_comp (inclusionOver h S hS) d₂ d)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun t => t ≫ (inclusionOver h S hS).map d) hfac₂) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact (congrArg (fun t => β' ≫ t) hfac.symm).trans (Category.assoc _ _ _).symm
    · exact pullbackFiberHom_eq_of_presented_arrow_restrict G n₁ n₂ d e e' δ₁ δ₂ hδ₁ hδ₂ d₂ harr
  refine ⟨Sieve.bind T₁.arrows (fun {V₁} {β} hβ => (key hβ).choose), ?_, ?_⟩
  · refine (BigFppfOver.topology B' S (largerContains h hS)).bind_covering hT₁ ?_
    intro V₁ β hβ
    exact (key hβ).choose_spec.1
  · intro V' k hk
    obtain ⟨V₁, β', β, hβ, hβ', rfl⟩ := hk
    exact (key hβ).choose_spec.2 hβ'

/-- **The injectivity half of clause (1) of Stacks 02ZN for the canonical comparison**
`u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`: two morphisms of `u_p [U/R]` with the same image are locally equal.

This is the generic reduction of
`CategoryTheory.PullbackAdjunction.locallyEqual_of_leftToRight_map_eq`, whose hypothesis is
supplied by `AlgebraicGeometry.Stack.hfib_changeBigSiteQuotientMap` through
`CategoryTheory.PullbackAdjunction.hcore_of_fibrePair` and
`CategoryTheory.PullbackAdjunction.hfaith_of_equalBase`. -/
theorem locallyEqual_changeBigSiteQuotientComparison
    {A Bo : Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS)}
    (v v' : A ⟶ Bo)
    (hv : (changeBigSiteQuotientComparison B B' h S hS G).map v =
      (changeBigSiteQuotientComparison B B' h S hS G).map v') :
    (pullbackQuotientStackProj h S hS G).LocallyEqual
      (BigFppfOver.topology B' S (largerContains h hS)) v v' := by
  have hcore := PullbackAdjunction.hcore_of_fibrePair
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (changeBigSiteQuotientMap B B' h S hS G)
    (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)
    (BigFppfOver.topology B' S (largerContains h hS))
    (hfib_changeBigSiteQuotientMap B B' h S hS G)
  have hfaith := @PullbackAdjunction.hfaith_of_equalBase _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G)
    (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)
    (isFibered_quotientStack G)
    (BigFppfOver.topology B' S (largerContains h hS))
    ((hasNonemptyFiniteLimits_bigFppfOver S hS).out Limits.WalkingParallelPair)
    (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS Limits.WalkingParallelPair) hcore
  exact @PullbackAdjunction.locallyEqual_of_leftToRight_map_eq _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G)
    (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)
    (isFibered_quotientStack G) (hasNonemptyFiniteLimits_bigFppfOver S hS)
    (BigFppfOver.topology B' S (largerContains h hS))
    (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS) hfaith A Bo v v' hv

end Change

end AlgebraicGeometry.Stack

end
