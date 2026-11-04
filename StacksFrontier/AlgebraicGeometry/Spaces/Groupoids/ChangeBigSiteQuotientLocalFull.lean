module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteArrowPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientLocalFaithful
public import StacksFrontier.CategoryTheory.FiberedCategory.GrothendieckArrowAttachment
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackComparisonFull

/-!
# Morphisms of the quotient of a pulled-back groupoid come locally from the quotient stack

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G` be
a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and write `i` for the
localized inclusion. This file proves the surjectivity half of clause (1) of Stacks 02ZN for the
canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`: every morphism between its values is, along a
covering sieve of the base, the image of a morphism of `u_p [U/R]`.

The generic reduction of
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackComparisonFull` turns that statement
into one about a strongly cartesian morphism `μ : z ⟶ F(x₀)` of `[f⁻¹U/f⁻¹R]` over
`φ : V ⟶ i(p x₀)` and an arbitrary `Θ : z ⟶ F(y)`. What remains is geometry. The morphism `Θ` lies
over some `ψ : V ⟶ i(p y)`, and `φ` and `ψ` factor through the image of a single test object of the
smaller site, over which — locally on `V`, by part (1) of Stacks 044X — both `x₀` and `y` are
presented by points `a`, `a'` of the object space. Restricting `μ` and `Θ` there and cancelling the
two presenting cartesian morphisms turns `Θ` into an arrow of the groupoid of points of `f⁻¹G`
between the restrictions of the transports of `a` and `a'`, by part (2) of Stacks 044X. That arrow
is, locally on `V`, the transport of an arrow `δ₀` of the groupoid of points of `G`, by the local
description of sections of an inverse image applied to the arrow space of Stacks 044V; and the
morphism of `[U/R]` built from `δ₀` induces `Θ` there.

## Main results

* `AlgebraicGeometry.Stack.changeBigSitePointwiseMap_map_cartesianLift`: the map of pointwise
  groupoid fibrations sends the chosen cartesian lift of `d` to the morphism over `i d` whose
  fibre component is the transport comparing the two restricted transported points.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientMap_map_pointwiseToQuotientStack'`: the
  2-isomorphism exhibiting `[U/R] ⟶ [f⁻¹U/f⁻¹R]` on presented objects, read at an arbitrary
  morphism of the pointwise groupoid fibration.
* `AlgebraicGeometry.Stack.changeBigSiteSectionEquiv_restrict_eq`: two factorizations of one
  morphism of the enlarged site restrict a transported section in the same way.
* `AlgebraicGeometry.Stack.exists_covering_presented_cartesianPair`: two objects of `[U/R]` are
  presented by points over one test object of the smaller site, locally on a test object of the
  enlarged one, by strongly cartesian morphisms over the two prescribed morphisms of the base.
* `AlgebraicGeometry.Stack.exists_frameChange_changeBigSitePointwiseMap`: the comparison of the
  two chosen cartesian frames of a test object of the enlarged site, carrying the arrow of the
  groupoid of points of `f⁻¹G` to the transport of the descended arrow of `G`.
* `AlgebraicGeometry.Stack.hfullCore_changeBigSiteQuotientMap`: the geometric input of the
  reduction.
* `AlgebraicGeometry.Stack.exists_covering_changeBigSiteQuotientComparison_map_comp`: the
  surjectivity half of clause (1) of Stacks 02ZN for the canonical comparison.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Deformation

namespace AlgebraicGeometry.Stack

universe u

section Transport

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc BasedCategory.ofFunctor
  Grpd.forgetToCat Grpd.of

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The map of pointwise groupoid fibrations on chosen cartesian lifts.** The chosen cartesian
lift of `d` at a point goes to the morphism over `i d` whose fibre component is the transport
comparing the transport of the restricted point with the restriction of the transported point. -/
theorem changeBigSitePointwiseMap_map_cartesianLift {W W₂ : BigFppfOver B S hS} (d : W₂ ⟶ W)
    (a : G.toGroupoidInFunctors.Evaluation (op W)) :
    ∃ pf, (changeBigSitePointwiseMap B B' h S hS G).map
        (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor') a d) =
      CoGrothendieck.homOf ((inclusionOver h S hS).map d) (eqToHom pf) := by
  obtain ⟨hgeq, hnat⟩ := (pointwiseMapData (changeBigSiteGroupoidHom B B' h S hS G)).2.2
    (Quiver.Hom.toLoc (op d))
  refine ⟨changeBigSiteSectionEquiv_restrict B B' h S hS G.objects d a, ?_⟩
  refine CoGrothendieck.Hom.ext _ _ rfl ?_
  have key : ((changeBigSitePointwiseMap B B' h S hS G).map
        (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor') a d)).fiber =
      ((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map
          (𝟙 (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor'.map d.op.toLoc).toFunctor.obj a)) ≫
        ((pointwiseMapData (changeBigSiteGroupoidHom B B' h S hS G)).val.naturality
          (Quiver.Hom.toLoc (op d))).hom.toNatTrans.app a := rfl
  have hB : ∃ pn, ((pointwiseMapData (changeBigSiteGroupoidHom B B' h S hS G)).val.naturality
      (Quiver.Hom.toLoc (op d))).hom.toNatTrans.app a = eqToHom pn :=
    ⟨_, by rw [hnat, eqToIso.hom, Cat.eqToHom_app]⟩
  refine Eq.trans key ?_
  refine CoGrothendieck.eq_of_exists_eqToHom (CoGrothendieck.exists_eqToHom_comp
    (CoGrothendieck.exists_eqToHom_map _ (CoGrothendieck.exists_eqToHom_id _)) hB) ?_
  exact CoGrothendieck.exists_eqToHom_comp
    ⟨changeBigSiteSectionEquiv_restrict B B' h S hS G.objects d a, rfl⟩ ⟨_, rfl⟩

end Transport

section Presentation

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The restriction along the stackification of `[U/R] ⟶ [f⁻¹U/f⁻¹R]`, read at an arbitrary
morphism of the pointwise groupoid fibration.** -/
theorem changeBigSiteQuotientMap_map_pointwiseToQuotientStack'
    {X Y : CoGrothendieck (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor'} (w : X ⟶ Y) :
    (changeBigSiteQuotientMap B B' h S hS G).map ((pointwiseToQuotientStack G).map w) ≫
        (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj Y) =
      (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj X) ≫
        (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).map
          ((changeBigSitePointwiseMap B B' h S hS G).map w) :=
  (changeBigSiteQuotientMapUnit B B' h S hS G).hom.naturality
    ((quotientPrestackEquivalence G).functor.map w)


/-- **Two factorizations of one morphism of the enlarged site restrict a transported section in
the same way.** -/
theorem changeBigSiteSectionEquiv_restrict_eq (X : AlgebraicSpaces B S hS)
    {W W₂ : BigFppfOver B S hS} (d₂ : W₂ ⟶ W) (a : X.obj.obj (op W))
    {V₁ V' : BigFppfOver B' S (largerContains h hS)} (β' : V' ⟶ V₁)
    (χ : V₁ ⟶ (inclusionOver h S hS).obj W) (χ₂ : V' ⟶ (inclusionOver h S hS).obj W₂)
    (hfac₂ : χ₂ ≫ (inclusionOver h S hS).map d₂ = β' ≫ χ) :
    ((changeBigSite B B' h S hS).obj X).obj.map β'.op
        (((changeBigSite B B' h S hS).obj X).obj.map χ.op
          (changeBigSiteSectionEquiv B B' h S hS X W a)) =
      ((changeBigSite B B' h S hS).obj X).obj.map χ₂.op
        (changeBigSiteSectionEquiv B B' h S hS X W₂ (X.obj.map d₂.op a)) := by
  refine Eq.trans (Functor.map_comp_apply _ χ.op β'.op _).symm ?_
  refine Eq.trans ?_ ((Functor.map_comp_apply _ ((inclusionOver h S hS).map d₂).op χ₂.op
    (changeBigSiteSectionEquiv B B' h S hS X W a)).trans
      (congrArg (fun t => ((changeBigSite B B' h S hS).obj X).obj.map χ₂.op t)
        (changeBigSiteSectionEquiv_restrict B B' h S hS X d₂ a).symm))
  exact congrArg (fun (t : V' ⟶ (inclusionOver h S hS).obj W) =>
    ((changeBigSite B B' h S hS).obj X).obj.map t.op
      (changeBigSiteSectionEquiv B B' h S hS X W a)) hfac₂.symm

/-- **Two objects of `[U/R]` with prescribed morphisms of the base out of one test object are
presented, locally on a test object of the enlarged site, by points of the object space over one
test object mapping to both.** -/
theorem exists_covering_presented_cartesianPair
    (x₀ y : (quotientStack G).obj) {W₀ : BigFppfOver B S hS}
    (c₁ : W₀ ⟶ (quotientStack G).p.obj x₀) (c₂ : W₀ ⟶ (quotientStack G).p.obj y)
    (V : BigFppfOver B' S (largerContains h hS)) (ξ : V ⟶ (inclusionOver h S hS).obj W₀) :
    ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (W : BigFppfOver B S hS) (d₀ : W ⟶ W₀) (χ : V₁ ⟶ (inclusionOver h S hS).obj W)
          (a a' : G.objects.obj.obj (op W))
          (ex : (pointwiseToQuotientStack G).obj ⟨W, a⟩ ⟶ x₀)
          (gy : (pointwiseToQuotientStack G).obj ⟨W, a'⟩ ⟶ y),
          χ ≫ (inclusionOver h S hS).map d₀ = β ≫ ξ ∧
          (quotientStack G).p.IsStronglyCartesian (d₀ ≫ c₁) ex ∧
          (quotientStack G).p.IsStronglyCartesian (d₀ ≫ c₂) gy := by
  have hcont : (inclusionOver h S hS).IsContinuous (BigFppfOver.topology B S hS)
      (BigFppfOver.topology B' S (largerContains h hS)) :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  have hFib := isFibered_quotientStack G
  obtain ⟨R₁, hR₁, hs₁⟩ := exists_covering_presented G W₀
    (Functor.pullbackFiber (quotientStack G).p
      (Functor.Fiber.mk (rfl : (quotientStack G).p.obj x₀ = _)) c₁)
  obtain ⟨R₂, hR₂, hs₂⟩ := exists_covering_presented G W₀
    (Functor.pullbackFiber (quotientStack G).p
      (Functor.Fiber.mk (rfl : (quotientStack G).p.obj y = _)) c₂)
  refine ⟨_, mem_pullback_functorPushforward (inclusionOver h S hS)
    (BigFppfOver.topology B S hS) (BigFppfOver.topology B' S (largerContains h hS))
    ((BigFppfOver.topology B S hS).intersection_covering hR₁ hR₂) ξ, ?_⟩
  intro V₁ β hβ
  obtain ⟨W, d₀, χ, hd, hfac⟩ :=
    exists_factorisation_of_mem_pullback_functorPushforward (inclusionOver h S hS) ξ hβ
  obtain ⟨a, ⟨e⟩⟩ := hs₁ hd.1
  obtain ⟨a', ⟨e'⟩⟩ := hs₂ hd.2
  have eA : Functor.FiberIso (presentedFiber G W a)
      (Functor.pullbackFiber (quotientStack G).p
        (Functor.Fiber.mk (rfl : (quotientStack G).p.obj x₀ = _)) (d₀ ≫ c₁)) :=
    e.trans (Functor.FiberIso.pullbackComp hFib _ c₁ d₀)
  have eB : Functor.FiberIso (presentedFiber G W a')
      (Functor.pullbackFiber (quotientStack G).p
        (Functor.Fiber.mk (rfl : (quotientStack G).p.obj y = _)) (d₀ ≫ c₂)) :=
    e'.trans (Functor.FiberIso.pullbackComp hFib _ c₂ d₀)
  exact ⟨W, d₀, χ, a, a', _, _, hfac.symm,
    isStronglyCartesian_presentedComparison G (d₀ ≫ c₁) eA,
    isStronglyCartesian_presentedComparison G (d₀ ≫ c₂) eB⟩


/-- **The frame change comparing the two presentations of a test object of the enlarged site.**
Let `d₂ : W₂ ⟶ W` be a morphism of the smaller site and let `β' : V' ⟶ V₁`, `χ : V₁ ⟶ i W` and
`χ₂ : V' ⟶ i W₂` satisfy `χ₂ ∘ i d₂ = β' ∘ χ`. Let `γ` be an arrow of the groupoid of points of
`f⁻¹G` at `V₁` between the restrictions along `χ` of the transports of two points `a`, `a'` of the
object space over `W`, and let `δ₀` be an arrow of the groupoid of points of `G` at `W₂` between
the two points restricted along `d₂` whose transport, restricted along `χ₂`, is the restriction of
`γ` along `β'`.

Then the two chosen cartesian frames of `V'` — the one through `β'` and the one through `χ₂` — are
compared by a vertical morphism of the pointwise groupoid fibration of `f⁻¹G` which carries the
chosen cartesian lift of `χ` to the transported chosen cartesian lift of `d₂`, and the morphism
determined by `γ` to the transport of `δ₀`.

The comparison is the transport of the equality of the two restricted points, whose fibre
components are transports; the two identities then come from the arrow `δ₀` presenting the same
section of the arrow space as `γ`. -/
theorem exists_frameChange_changeBigSitePointwiseMap
    {W W₂ : BigFppfOver B S hS} (d₂ : W₂ ⟶ W) (a a' : G.objects.obj.obj (op W))
    {V₁ V' : BigFppfOver B' S (largerContains h hS)} (β' : V' ⟶ V₁)
    (χ : V₁ ⟶ (inclusionOver h S hS).obj W) (χ₂ : V' ⟶ (inclusionOver h S hS).obj W₂)
    (hfac₂ : χ₂ ≫ (inclusionOver h S hS).map d₂ = β' ≫ χ)
    (γ : (((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj (changeBigSiteSectionEquiv B
      B' h S hS G.objects W a) ⟶
      (((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj (changeBigSiteSectionEquiv
        B B' h S hS G.objects W a'))
    (δ₀ : (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor').map d₂.op.toLoc).toFunctor.obj a ⟶
      (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map
        d₂.op.toLoc).toFunctor.obj a')
    (r₀ : G.arrows.obj.obj (op W₂))
    (hδ₀ : (G.toGroupoidInFunctors.evaluationArrowEquiv (op W₂) _ _ δ₀).1 = r₀)
    (hres : ((changeBigSite B B' h S hS).obj G.arrows).obj.map β'.op
          ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
            (op V₁) _ _ γ).1 =
        ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ₂.op
          (changeBigSiteSectionEquiv B B' h S hS G.arrows W₂ r₀)) :
    ∃ v₀ : CoGrothendieck.domainCartesianLift
          ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj
            (changeBigSiteSectionEquiv B B' h S hS G.objects W a)) β' ⟶
        CoGrothendieck.domainCartesianLift (changeBigSiteSectionEquiv B B' h S hS G.objects W₂
          (G.objects.obj.map d₂.op a)) χ₂,
      ((presheafOfGroupoids (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors)).p).IsHomLift (𝟙 V') v₀ ∧
      ((presheafOfGroupoids (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors)).p).IsStronglyCartesian (χ₂ ≫ (inclusionOver h S hS).map d₂)
        ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B'
        h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫
        (changeBigSitePointwiseMap B B' h S hS G).map (CoGrothendieck.cartesianLift (F :=
        (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a
        d₂)) ∧
      (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S
        hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj (changeBigSiteSectionEquiv
        B B' h S hS G.objects W a)) β') ≫ CoGrothendieck.cartesianLift (F :=
        (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv B B' h S hS G.objects W a) χ
        =
        v₀ ≫ (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B
          B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
          (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫
          (changeBigSitePointwiseMap B B' h S hS G).map (CoGrothendieck.cartesianLift (F :=
          (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a
          d₂) ∧
      (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S
        hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj (changeBigSiteSectionEquiv
        B B' h S hS G.objects W a)) β') ≫ CoGrothendieck.homOf χ γ =
        v₀ ≫ (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B
          B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
          (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫
          (changeBigSitePointwiseMap B B' h S hS G).map ((CoGrothendieck.ι
          ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
          W₂).map δ₀ ≫ (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor
          G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a' d₂)) := by
  have hpv : ∀ b : G.objects.obj.obj (op W),
      ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map β'.op.toLoc).toFunctor.obj
        ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj
          (changeBigSiteSectionEquiv B B' h S hS G.objects W b)) : ((evaluationGroupoidFunctor
          (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor').obj ⟨op V'⟩) =
      (((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ₂.op.toLoc).toFunctor.obj
        (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op b)) :=
    fun b => changeBigSiteSectionEquiv_restrict_eq B B' h S hS G.objects d₂ b β' χ χ₂ hfac₂
  have hgen : ∀ b : G.objects.obj.obj (op W),
      ∃ pf, (changeBigSitePointwiseMap B B' h S hS G).map (CoGrothendieck.cartesianLift
        (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor') b d₂) =
        CoGrothendieck.homOf ((inclusionOver h S hS).map d₂) (eqToHom pf) ∧
      (CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') V').map (eqToHom (hpv b)) ≫
        ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B'
          h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
          (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op b)) χ₂) ≫
          CoGrothendieck.homOf ((inclusionOver h S hS).map d₂) (eqToHom pf)) =
      (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S
        hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj (changeBigSiteSectionEquiv
        B B' h S hS G.objects W b)) β') ≫ CoGrothendieck.cartesianLift (F :=
        (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor')
        (changeBigSiteSectionEquiv B B' h S hS G.objects W b) χ := by
    intro b
    obtain ⟨pf, hpf⟩ := changeBigSitePointwiseMap_map_cartesianLift B B' h S hS G d₂ b
    refine ⟨pf, hpf, CoGrothendieck.ι_map_eqToHom_comp_eq
      ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat)) (hpv b) _ _ hfac₂.symm
      (CoGrothendieck.exists_eqToHom_fiber_comp ((evaluationGroupoidFunctor (changeBigSiteGroupoid B
        B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat)) _ _
        (CoGrothendieck.exists_eqToHom_fiber_cartesianLift _ _)
        (CoGrothendieck.exists_eqToHom_fiber_cartesianLift _ _))
      (CoGrothendieck.exists_eqToHom_fiber_comp ((evaluationGroupoidFunctor (changeBigSiteGroupoid B
        B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat)) _ _
        (CoGrothendieck.exists_eqToHom_fiber_cartesianLift _ _)
        (CoGrothendieck.exists_eqToHom_fiber_homOf _ ⟨pf, rfl⟩))⟩
  obtain ⟨pf, hpf, hv₀⟩ := hgen a
  obtain ⟨pf', hpf', hv₀'⟩ := hgen a'
  have p_v := hpv a
  have p_v' := hpv a'
  have hceq : ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
        (op V') _ _ (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
          G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map
          β'.op.toLoc).toFunctor).map γ)).1 =
      ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
        (op V') _ _ (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
          G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map
          χ₂.op.toLoc).toFunctor).map (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op
          W₂)).map δ₀))).1 := by
    refine Eq.trans (Deformation.evaluationMap_map_arrow
      (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors β'.op γ) ?_
    refine Eq.trans hres ?_
    refine Eq.trans (congrArg (fun t =>
      ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ₂.op
        (changeBigSiteSectionEquiv B B' h S hS G.arrows W₂ t)) hδ₀.symm) ?_
    refine Eq.trans (congrArg
      (fun t => ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ₂.op t)
      (changeBigSiteGroupoidHom_evaluation_arrow B B' h S hS G W₂ δ₀).symm) ?_
    exact (Deformation.evaluationMap_map_arrow
      (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors χ₂.op (((changeBigSiteGroupoidHom B
        B' h S hS G).evaluation (op W₂)).map δ₀)).symm
  have harr : ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
    G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map β'.op.toLoc).toFunctor).map γ
    ≫ eqToHom p_v' = eqToHom p_v ≫ ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
    G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map χ₂.op.toLoc).toFunctor).map
    (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map δ₀) := by
    refine Eq.trans (congrArg (fun t => t ≫ eqToHom p_v')
      (Deformation.hom_eq_transport
        (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors (op V') p_v p_v'
        (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor').map β'.op.toLoc).toFunctor).map γ)
          (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors
          ⋙ Grpd.forgetToCat).toPseudofunctor').map χ₂.op.toLoc).toFunctor).map
          (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map δ₀)) hceq)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun t => eqToHom p_v ≫ t) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun t => ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h
      S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map
      χ₂.op.toLoc).toFunctor).map (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map
      δ₀) ≫ t) ?_)
      (Category.comp_id _)
    exact (eqToHom_trans p_v'.symm p_v').trans (eqToHom_refl _ _)
  have hrhs : (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid
    B B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
    (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫
    (changeBigSitePointwiseMap B B' h S hS G).map ((CoGrothendieck.ι ((evaluationGroupoidFunctor
    G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') W₂).map δ₀ ≫
    (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
    Grpd.forgetToCat).toPseudofunctor') a' d₂)) =
      (CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') V').map
        (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ₂.op.toLoc).toFunctor).map
        (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map δ₀)) ≫
        ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B'
          h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
          (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a')) χ₂) ≫
          CoGrothendieck.homOf ((inclusionOver h S hS).map d₂) (eqToHom pf')) := by
    refine Eq.trans (congrArg (fun t => (CoGrothendieck.cartesianLift (F :=
      (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv B B' h S hS G.objects W₂
      (G.objects.obj.map d₂.op a)) χ₂) ≫ t)
      (Functor.map_comp (changeBigSitePointwiseMap B B' h S hS G) ((CoGrothendieck.ι
        ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        W₂).map δ₀) (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor
        G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a' d₂))) ?_
    refine Eq.trans (congrArg (fun t => (CoGrothendieck.cartesianLift (F :=
      (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv B B' h S hS G.objects W₂
      (G.objects.obj.map d₂.op a)) χ₂) ≫ t ≫ (changeBigSitePointwiseMap B B' h S hS G).map
      (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') a' d₂))
      (changeBigSitePointwiseMap_map_ι B B' h S hS G W₂ δ₀)) ?_
    refine Eq.trans (congrArg (fun t => (CoGrothendieck.cartesianLift (F :=
      (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv B B' h S hS G.objects W₂
      (G.objects.obj.map d₂.op a)) χ₂) ≫
      (CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') ((inclusionOver h S hS).obj
        W₂)).map (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map δ₀) ≫ t) hpf')
        ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ CoGrothendieck.homOf ((inclusionOver h S hS).map d₂)
      (eqToHom pf'))
      (CoGrothendieck.cartesianLift_comp_ι_map ((evaluationGroupoidFunctor (changeBigSiteGroupoid B
        B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat)) χ₂ (((changeBigSiteGroupoidHom B B' h
        S hS G).evaluation (op W₂)).map δ₀))) ?_
    exact Category.assoc ((CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B'
      h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') V').map
      (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor').map χ₂.op.toLoc).toFunctor).map
      (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map δ₀)))
      ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h
      S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv
      B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a')) χ₂)) (CoGrothendieck.homOf
      ((inclusionOver h S hS).map d₂) (eqToHom pf'))
  have hv₀lift : (presheafOfGroupoids (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
    G).toGroupoidInFunctors)).p.IsHomLift (𝟙 V')
      ((CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
        G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') V').map (eqToHom p_v)) :=
    CoGrothendieck.isHomLift_ι_map (eqToHom p_v)
  refine ⟨(CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS
    G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') V').map (eqToHom p_v), hv₀lift,
    ?_, ?_, ?_⟩
  · refine Eq.mp (congrArg (fun t => ((presheafOfGroupoids (evaluationGroupoidFunctor
    (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors)).p).IsStronglyCartesian (χ₂ ≫
    (inclusionOver h S hS).map d₂)
      ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h
        S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫ t))
        hpf.symm) ?_
    exact Functor.isStronglyCartesian_comp'
      (CoGrothendieck.isStronglyCartesian_homCartesianLift (F := (evaluationGroupoidFunctor
        (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv B B' h S hS G.objects W₂
        (G.objects.obj.map d₂.op a)) χ₂)
      (CoGrothendieck.isStronglyCartesian_homOf_of_isIso ((evaluationGroupoidFunctor
        (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat))
        ((inclusionOver h S hS).map d₂) (eqToHom pf)
        ⟨eqToHom pf.symm, (eqToHom_trans pf pf.symm).trans (eqToHom_refl _ _),
          (eqToHom_trans pf.symm pf).trans (eqToHom_refl _ _)⟩)
  · refine Eq.trans hv₀.symm ?_
    exact congrArg (fun t => (CoGrothendieck.ι ((evaluationGroupoidFunctor (changeBigSiteGroupoid B
      B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') V').map (eqToHom p_v)
      ≫
      (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S
        hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv
        B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫ t) hpf.symm
  · exact CoGrothendieck.cartesianLift_comp_homOf_eq ((evaluationGroupoidFunctor
    (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat)) β' χ γ p_v p_v'
      (((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map χ₂.op.toLoc).toFunctor).map
        (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W₂)).map δ₀))
      ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h
        S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a')) χ₂) ≫
        CoGrothendieck.homOf ((inclusionOver h S hS).map d₂) (eqToHom pf'))
      ((CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h
        S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
        (changeBigSiteSectionEquiv B B' h S hS G.objects W₂ (G.objects.obj.map d₂.op a)) χ₂) ≫
        (changeBigSitePointwiseMap B B' h S hS G).map ((CoGrothendieck.ι ((evaluationGroupoidFunctor
        G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') W₂).map δ₀ ≫
        (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor') a' d₂)))
      hv₀' harr hrhs

end Presentation

section Core

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The geometric input of the reduction of local fullness.** For a strongly cartesian morphism
`μ : z ⟶ F(x₀)` of `[f⁻¹U/f⁻¹R]` over `φ : V ⟶ i(p x₀)` and an arbitrary morphism `Θ : z ⟶ F(y)`,
there is, along a covering sieve of `V`, a morphism `e : x₁ ⟶ x₀` of `[U/R]` strongly cartesian
over its image together with a morphism `α : x₁ ⟶ y` and a restriction of `μ` along which `Θ`
becomes the morphism induced by `α`.

The covering sieve is the composite of the one along which `x₀` and `y` are both presented by
points of the object space over one test object of the smaller site, through which `φ` and the
base of `Θ` both factor, with, over each of its members, the one along which the arrow of the
groupoid of points of `f⁻¹G` that `Θ` becomes is the transport of an arrow of the groupoid of
points of `G`. -/
theorem hfullCore_changeBigSiteQuotientMap
    (x₀ y : (quotientStack G).obj) (V : BigFppfOver B' S (largerContains h hS))
    (φ : V ⟶ (inclusionOver h S hS).obj ((quotientStack G).p.obj x₀))
    (z : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj)
    (μ : z ⟶ (changeBigSiteQuotientMap B B' h S hS G).obj x₀)
    (hμ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian φ μ)
    (Θ : z ⟶ (changeBigSiteQuotientMap B B' h S hS G).obj y) :
    ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (x₁ : (quotientStack G).obj) (e : x₁ ⟶ x₀)
          (φ₁ : V₁ ⟶ (inclusionOver h S hS).obj ((quotientStack G).p.obj x₁))
          (α : x₁ ⟶ y) (z₁ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj)
          (μ₁ : z₁ ⟶ (changeBigSiteQuotientMap B B' h S hS G).obj x₁) (ν : z₁ ⟶ z),
          stronglyCartesianOver (quotientStack G).p e ∧
          φ₁ ≫ ((quotientStack G).p ⋙ inclusionOver h S hS).map e = β ≫ φ ∧
          (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian φ₁ μ₁ ∧
          (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift β ν ∧
          ν ≫ μ = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map e ∧
          ν ≫ Θ = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map α := by
  have hμl := hμ.toIsHomLift
  have hz : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.obj z = V :=
    IsHomLift.domain_eq _ φ μ
  obtain ⟨ψ, hψ⟩ := PullbackAdjunction.exists_isHomLift_of_obj_eq (quotientStack G).p
    (inclusionOver h S hS) (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (changeBigSiteQuotientMap B B' h S hS G) (changeBigSiteQuotientMap_comp B B' h S hS G) hz Θ
  obtain ⟨W₀, c₁, c₂, ξ, hξ₁, hξ₂⟩ := Space.exists_commonBase B B' h S hS
    ((quotientStack G).p.obj x₀) ((quotientStack G).p.obj y) V φ ψ
  obtain ⟨T₁, hT₁, hs₁⟩ := exists_covering_presented_cartesianPair B B' h S hS G x₀ y c₁ c₂ V ξ
  have hFcomp := changeBigSiteQuotientMap_comp B B' h S hS G
  have hN' := isFibredOneMorphism_pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)
  have hfib' : ∀ T : BigFppfOver B' S (largerContains h hS),
      Nonempty (Functor.Fiber.inducedFunctor (CoGrothendieck.ι_comp_comp_eq hN' T)).Full :=
    fun T => ⟨(fullyFaithful_pointwiseToQuotientStackFiber
      (changeBigSiteGroupoid B B' h S hS G) T).some.full⟩
  have key : ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T₁.arrows β →
      ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V₁,
        ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ ⦃β' : V' ⟶ V₁⦄, R.arrows β' →
          ∃ (x₁ : (quotientStack G).obj) (e : x₁ ⟶ x₀)
            (φ₁ : V' ⟶ (inclusionOver h S hS).obj ((quotientStack G).p.obj x₁))
            (α : x₁ ⟶ y) (z₁ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj)
            (μ₁ : z₁ ⟶ (changeBigSiteQuotientMap B B' h S hS G).obj x₁) (ν : z₁ ⟶ z),
            stronglyCartesianOver (quotientStack G).p e ∧
            φ₁ ≫ ((quotientStack G).p ⋙ inclusionOver h S hS).map e = (β' ≫ β) ≫ φ ∧
            (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian φ₁ μ₁ ∧
            (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift (β' ≫ β) ν ∧
            ν ≫ μ = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map e ∧
            ν ≫ Θ = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map α := by
    intro V₁ β hβ
    obtain ⟨W, d₀, χ, a, a', ex, gy, hfacχ, hex, hgy⟩ := hs₁ hβ
    -- the two factorizations of `β ≫ φ` and `β ≫ ψ` through the image of `W`
    have hχ : ∀ {Y : BigFppfOver B S hS} (c : W₀ ⟶ Y) (ρ : V ⟶ (inclusionOver h S hS).obj Y),
        ξ ≫ (inclusionOver h S hS).map c = ρ →
          χ ≫ (inclusionOver h S hS).map (d₀ ≫ c) = β ≫ ρ := by
      rintro Y c ρ rfl
      exact (congrArg (χ ≫ ·) (Functor.map_comp (inclusionOver h S hS) d₀ c)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hfacχ).trans (Category.assoc _ _ _)))
    have hχd := hχ c₁ φ hξ₁
    have hχd' := hχ c₂ ψ hξ₂
    -- restrict the strongly cartesian morphism along `β`
    obtain ⟨z₁, ν, hν, hνμ⟩ := Functor.exists_isStronglyCartesian_restrict
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p β φ μ hμ
    -- the images of the two presenting cartesian morphisms are strongly cartesian
    have hFmap : ∀ {R R' : BigFppfOver B S hS} {f : R ⟶ R'} {x x' : (quotientStack G).obj}
        {m : x ⟶ x'}, (quotientStack G).p.IsStronglyCartesian f m →
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
          ((inclusionOver h S hS).map f) ((changeBigSiteQuotientMap B B' h S hS G).map m) :=
      fun hm => Functor.isStronglyCartesian_map_of_comp_eq hFcomp
        (isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G) hm
    have hFex := hFmap hex
    have hFgy := hFmap hgy
    -- factor the restricted cartesian morphism and the restricted `Θ`
    have hνμ' : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
        (χ ≫ (inclusionOver h S hS).map (d₀ ≫ c₁)) (ν ≫ μ) :=
      Eq.mp (congrArg (fun t => (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
        t (ν ≫ μ)) hχd.symm) hνμ.toIsHomLift
    obtain ⟨κ, hκlift, hκfac⟩ := Functor.exists_factor_of_isStronglyCartesian χ
      ((inclusionOver h S hS).map (d₀ ≫ c₁)) _ hFex (ν ≫ μ) hνμ'
    have hΘ₁ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
        (χ ≫ (inclusionOver h S hS).map (d₀ ≫ c₂)) (ν ≫ Θ) :=
      Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift t (ν ≫ Θ)) hχd'.symm)
        (Functor.isHomLift_comp' hν.toIsHomLift hψ)
    obtain ⟨lam, hlamlift, hlamfac⟩ := Functor.exists_factor_of_isStronglyCartesian χ
      ((inclusionOver h S hS).map (d₀ ≫ c₂)) _ hFgy (ν ≫ Θ) hΘ₁
    -- the presenting comparison of the source is strongly cartesian over `χ`
    have hκcomp : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
        (χ ≫ (inclusionOver h S hS).map (d₀ ≫ c₁))
        (κ ≫ (changeBigSiteQuotientMap B B' h S hS G).map ex) := by
      refine Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
          (χ ≫ (inclusionOver h S hS).map (d₀ ≫ c₁)) t) hκfac.symm) ?_
      exact Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian t (ν ≫ μ))
        hχd.symm) hνμ
    have hκcart : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian χ κ :=
      Functor.isStronglyCartesian_of_comp' hκcomp hFex hκlift
    -- the two components of the 2-isomorphism at the presented objects
    have hUnlift : ∀ (W' : BigFppfOver B S hS) (a'' : G.objects.obj.obj (op W')),
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
          (𝟙 ((inclusionOver h S hS).obj W'))
          ((changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
            ((quotientPrestackEquivalence G).functor.obj ⟨W', a''⟩)) :=
      fun W' a'' => isHomLift_changeBigSiteQuotientMapUnit_hom_app B B' h S hS G
        ((quotientPrestackEquivalence G).functor.obj ⟨W', a''⟩)
    have hUniso := NatIso.isIso_app_of_isIso (changeBigSiteQuotientMapUnit B B' h S hS G).hom
    have hκ' : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian χ
        (κ ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj ⟨W, a⟩)) :=
      Functor.isStronglyCartesian_comp_isoOverId hκcart _ (hUnlift _ _) (hUniso _)
    obtain ⟨ι₀, hι₀iso, hι₀lift, hι₀fac⟩ :=
      CoGrothendieck.exists_isoOverId_of_isStronglyCartesian hN'
        (T := (inclusionOver h S hS).obj W)
        (b := changeBigSiteSectionEquiv B B' h S hS G.objects W a) χ
        (κ ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj ⟨W, a⟩)) hκ'
    have hθlift : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift χ
        (lam ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj ⟨W, a'⟩)) :=
      Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift t
          (lam ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
            ((quotientPrestackEquivalence G).functor.obj ⟨W, a'⟩))) (Category.comp_id χ))
        (Functor.isHomLift_comp' hlamlift (hUnlift _ _))
    obtain ⟨γ, hγ⟩ := CoGrothendieck.exists_homOf_eq_of_isHomLift hN' hfib' χ ι₀ hι₀iso hι₀lift
      (lam ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
        ((quotientPrestackEquivalence G).functor.obj ⟨W, a'⟩)) hθlift
    -- the section of the arrow space that the resulting arrow of the groupoid of points gives
    have hsrcr : ((changeBigSite B B' h S hS).map G.source).hom.app (op V₁)
        ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
          (op V₁) _ _ γ).1 =
        ((changeBigSite B B' h S hS).obj G.objects).obj.map χ.op
          (changeBigSiteSectionEquiv B B' h S hS G.objects W a) :=
      ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
        (op V₁) _ _ γ).2.1
    have htgtr : ((changeBigSite B B' h S hS).map G.target).hom.app (op V₁)
        ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
          (op V₁) _ _ γ).1 =
        ((changeBigSite B B' h S hS).obj G.objects).obj.map χ.op
          (changeBigSiteSectionEquiv B B' h S hS G.objects W a') :=
      ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.evaluationArrowEquiv
        (op V₁) _ _ γ).2.2
    obtain ⟨R, hR, hspec⟩ := Space.exists_covering_arrow_restrict B B' h S hS G W a a' V₁ χ
      _ htgtr hsrcr
    refine ⟨R, hR, ?_⟩
    intro V' β' hβ'
    obtain ⟨W₂, d₂, χ₂, r₀, hfac₂, htgt₀, hsrc₀, hres⟩ := hspec hβ'
    -- the arrow of the groupoid of points of `G` at `W₂` represented by `r₀`
    obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor'.map d₂.op.toLoc).toFunctor.obj a) ⟶
        (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor'.map d₂.op.toLoc).toFunctor.obj a'),
        (G.toGroupoidInFunctors.evaluationArrowEquiv (op W₂) _ _ δ₀).1 = r₀ :=
      ⟨(G.toGroupoidInFunctors.evaluationArrowEquiv (op W₂) _ _).symm ⟨r₀, hsrc₀, htgt₀⟩,
        congrArg Subtype.val (Equiv.apply_symm_apply _ _)⟩
    -- the chosen cartesian lift of `d₂` at the presenting point, and the presentation it gives
    have hcld₂ : (quotientStack G).p.IsStronglyCartesian d₂
        ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
          (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂)) :=
      (isFibredOneMorphism_pointwiseToQuotientStack G).map_isStronglyCartesian d₂ _
        (CoGrothendieck.isStronglyCartesian_homCartesianLift
          (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂)
    have he₁ : (quotientStack G).p.IsStronglyCartesian (d₂ ≫ d₀ ≫ c₁)
        ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
          (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂) ≫ ex) :=
      Functor.isStronglyCartesian_comp' hcld₂ hex
    have hsc₁ : stronglyCartesianOver (quotientStack G).p
        ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
          (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂) ≫ ex) :=
      Comma.stronglyCartesianOver_of_isStronglyCartesian (quotientStack G).p he₁
    have hwcompat : (χ₂ ≫ (inclusionOver h S hS).map (eqToHom
          (IsHomLift.domain_eq (quotientStack G).p (d₂ ≫ d₀ ≫ c₁)
            ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
              (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor') a d₂) ≫ ex)).symm)) ≫
          ((quotientStack G).p ⋙ inclusionOver h S hS).map
            ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
              (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor') a d₂) ≫ ex) =
        (β' ≫ β) ≫ φ := by
      refine Eq.trans (PullbackAdjunction.comp_map_eqToHom_of_isHomLift (quotientStack G).p
        (inclusionOver h S hS) he₁.toIsHomLift χ₂) ?_
      refine Eq.trans (congrArg (fun t => χ₂ ≫ t)
        (Functor.map_comp (inclusionOver h S hS) d₂ (d₀ ≫ c₁))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun t => t ≫ (inclusionOver h S hS).map (d₀ ≫ c₁)) hfac₂) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact (congrArg (fun t => β' ≫ t) hχd).trans (Category.assoc _ _ _).symm
    -- restrict the cartesian morphism once more and factor it through the chosen lift of `d₂`
    obtain ⟨z₂, ν₂, hν₂, hν₂ν⟩ := Functor.exists_isStronglyCartesian_restrict
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p β' β ν hν
    have hFcl := hFmap hcld₂
    have hν₂κ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
        (χ₂ ≫ (inclusionOver h S hS).map d₂) (ν₂ ≫ κ) :=
      Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift t (ν₂ ≫ κ)) hfac₂.symm)
        (Functor.isHomLift_comp' hν₂.toIsHomLift hκlift)
    obtain ⟨μ₁, hμ₁lift, hμ₁fac⟩ := Functor.exists_factor_of_isStronglyCartesian χ₂
      ((inclusionOver h S hS).map d₂) _ hFcl (ν₂ ≫ κ) hν₂κ
    have hμ₁cart : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
        χ₂ μ₁ := by
      refine Functor.isStronglyCartesian_of_comp' ?_ hFcl hμ₁lift
      refine Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
          (χ₂ ≫ (inclusionOver h S hS).map d₂) t) hμ₁fac.symm) ?_
      exact Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian t (ν₂ ≫ κ))
        hfac₂.symm) (Functor.isStronglyCartesian_comp' hν₂ hκcart)
    have hμ₁φ₁ : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
        (χ₂ ≫ (inclusionOver h S hS).map (eqToHom
          (IsHomLift.domain_eq (quotientStack G).p (d₂ ≫ d₀ ≫ c₁)
            ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
              (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor') a d₂) ≫ ex)).symm)) μ₁ := by
      refine Eq.mp (congrArg (fun t =>
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian (χ₂ ≫ t) μ₁)
        (eqToHom_map (inclusionOver h S hS) _).symm) ?_
      exact PullbackAdjunction.isStronglyCartesian_comp_eqToHom _ χ₂ μ₁ hμ₁cart
    -- the two identities of the presentation
    have hμeq : (ν₂ ≫ ν) ≫ μ = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map
        ((pointwiseToQuotientStack G).map (CoGrothendieck.cartesianLift
          (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂) ≫ ex) := by
      refine Eq.trans (Category.assoc ν₂ ν μ) ?_
      refine Eq.trans (congrArg (fun t => ν₂ ≫ t) hκfac.symm) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun t => t ≫ (changeBigSiteQuotientMap B B' h S hS G).map ex)
        hμ₁fac.symm) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (fun t => μ₁ ≫ t) (Functor.map_comp _ _ _).symm
    have hstar : ν₂ ≫ lam = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map
        ((pointwiseToQuotientStack G).map
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' W₂).map δ₀ ≫
              CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor
                G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a' d₂)) := by
      obtain ⟨v₀, hv₀lift, hv₀cart, hid1, hid2⟩ :=
        exists_frameChange_changeBigSitePointwiseMap B B' h S hS G d₂ a a' β' χ χ₂ hfac₂ γ δ₀
          r₀ hδ₀ hres
      have hAcart : ((quotientStack (changeBigSiteGroupoid B B' h S hS G)).p).IsStronglyCartesian β'
        (ν₂ ≫ ι₀) :=
        Functor.isStronglyCartesian_comp_isoOverId hν₂ ι₀ hι₀lift hι₀iso
      have hBbcart : ((quotientStack (changeBigSiteGroupoid B B' h S hS G)).p).IsStronglyCartesian
        χ₂ (μ₁ ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app ((quotientPrestackEquivalence
        G).functor.obj ⟨W₂, (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor').map d₂.op.toLoc).toFunctor.obj a⟩)) :=
        Functor.isStronglyCartesian_comp_isoOverId hμ₁cart _ (hUnlift _ _) (hUniso _)
      have hdag : (ν₂ ≫ ι₀) ≫ (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).map
            (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor (changeBigSiteGroupoid B
              B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
              (changeBigSiteSectionEquiv B B' h S hS G.objects W a) χ) =
          (μ₁ ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app ((quotientPrestackEquivalence
            G).functor.obj ⟨W₂, (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor').map d₂.op.toLoc).toFunctor.obj a⟩)) ≫
            (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).map
            ((changeBigSitePointwiseMap B B' h S hS G).map (CoGrothendieck.cartesianLift (F :=
            (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
            a d₂)) := by
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (congrArg (fun t => ν₂ ≫ t) hι₀fac) ?_
        refine Eq.trans (Category.assoc _ _ _).symm ?_
        refine Eq.trans (congrArg (fun t => t ≫ (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj ⟨W, a⟩)) hμ₁fac.symm) ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (congrArg (fun t => μ₁ ≫ t)
          (changeBigSiteQuotientMap_map_pointwiseToQuotientStack' B B' h S hS G
            (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') a d₂))) ?_
        exact (Category.assoc _ _ _).symm
      have hfinal := Functor.comp_map_eq_of_frameChange hN'
        (CoGrothendieck.isStronglyCartesian_homCartesianLift (F := (evaluationGroupoidFunctor
          (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor')
          ((((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor').map χ.op.toLoc).toFunctor.obj
            (changeBigSiteSectionEquiv B B' h S hS G.objects W a)) β')
        (CoGrothendieck.isStronglyCartesian_homCartesianLift (F := (evaluationGroupoidFunctor
          (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor') (changeBigSiteSectionEquiv B B' h S hS G.objects W₂
          (G.objects.obj.map d₂.op a)) χ₂)
        hv₀lift hv₀cart hid1 hid2 hAcart hBbcart hdag
      have hmono := hUniso ((quotientPrestackEquivalence G).functor.obj ⟨W, a'⟩)
      refine (cancel_mono ((changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
        ((quotientPrestackEquivalence G).functor.obj ⟨W, a'⟩))).1 ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (fun t => ν₂ ≫ t) hγ) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans hfinal ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (fun t => μ₁ ≫ t)
        (changeBigSiteQuotientMap_map_pointwiseToQuotientStack' B B' h S hS G
          ((CoGrothendieck.ι ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor') W₂).map δ₀ ≫ (CoGrothendieck.cartesianLift (F :=
            (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor')
            a' d₂))).symm) ?_
      exact (Category.assoc _ _ _).symm
    have hΘeq : (ν₂ ≫ ν) ≫ Θ = μ₁ ≫ (changeBigSiteQuotientMap B B' h S hS G).map
        ((pointwiseToQuotientStack G).map
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' W₂).map δ₀ ≫
              CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor
                G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a' d₂) ≫ gy) := by
      refine Eq.trans (Category.assoc ν₂ ν Θ) ?_
      refine Eq.trans (congrArg (fun t => ν₂ ≫ t) hlamfac.symm) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun t => t ≫ (changeBigSiteQuotientMap B B' h S hS G).map gy)
        hstar) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (fun t => μ₁ ≫ t) (Functor.map_comp _ _ _).symm
    exact ⟨_, _, _, _, z₂, μ₁, ν₂ ≫ ν, hsc₁, hwcompat, hμ₁φ₁, hν₂ν.toIsHomLift, hμeq, hΘeq⟩
  refine ⟨Sieve.bind T₁.arrows (fun {V₁} {β} hβ => (key hβ).choose), ?_, ?_⟩
  · refine (BigFppfOver.topology B' S (largerContains h hS)).bind_covering hT₁ ?_
    intro V₁ β hβ
    exact (key hβ).choose_spec.1
  · intro V' k hk
    obtain ⟨V₁, β', β, hβ, hβ', rfl⟩ := hk
    exact (key hβ).choose_spec.2 hβ'


/-- **Local fullness of the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.** Every morphism
between values of the comparison is, along a covering sieve of the base, the image of a morphism
of `u_p [U/R]`.

This is the generic reduction of
`CategoryTheory.PullbackAdjunction.exists_covering_leftToRight_map_comp`, whose hypothesis is
supplied by `AlgebraicGeometry.Stack.hfullCore_changeBigSiteQuotientMap` through
`CategoryTheory.PullbackAdjunction.hfull_of_core`. -/
theorem exists_covering_changeBigSiteQuotientComparison_map_comp
    {A Bo : Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS)}
    (θ : (changeBigSiteQuotientComparison B B' h S hS G).obj A ⟶
      (changeBigSiteQuotientComparison B B' h S hS G).obj Bo) :
    ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS)
      ((pullbackQuotientStackProj h S hS G).obj A),
      ∀ ⦃w : Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS)⦄ (ρ : w ⟶ A),
        T.arrows ((pullbackQuotientStackProj h S hS G).map ρ) →
        ∃ k : w ⟶ Bo, (changeBigSiteQuotientComparison B B' h S hS G).map ρ ≫ θ =
          (changeBigSiteQuotientComparison B B' h S hS G).map k := by
  have hfull := fun Z Θ => @PullbackAdjunction.hfull_of_core _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G) (changeBigSiteQuotientMap_comp B B' h S hS G)
    (BigFppfOver.topology B' S (largerContains h hS))
    (hfullCore_changeBigSiteQuotientMap B B' h S hS G) Z Θ
  exact @PullbackAdjunction.exists_covering_leftToRight_map_comp _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G) (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)
    (isFibered_quotientStack G) (hasNonemptyFiniteLimits_bigFppfOver S hS)
    (BigFppfOver.topology B' S (largerContains h hS))
    (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS) hfull A Bo θ

end Core

end AlgebraicGeometry.Stack

end
