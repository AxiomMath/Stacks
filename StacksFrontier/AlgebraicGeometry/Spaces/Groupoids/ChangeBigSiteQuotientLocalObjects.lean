module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSectionCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientPrestackPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.FibreClause
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification

/-!
# Objects of the quotient of a pulled-back groupoid come locally from presentations over the
smaller site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G`
be a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and let `f` be the
morphism of sites determined by the localized inclusion `i`. This file proves that every object
of a fibre of `[f⁻¹U/f⁻¹R]` is, along a covering sieve of its test object, in the essential image
on fibres of the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.

This is clause (2) of Stacks 02ZN for that comparison, the condition that exhibits
`[f⁻¹U/f⁻¹R]` as a stackification of `u_p [U/R]` on the side of objects.

The proof composes three steps. An object of a fibre of `[f⁻¹U/f⁻¹R]` is, along a covering sieve,
presented by a point of `f⁻¹U` (Stacks 044X); such a point is, along a further covering sieve, the
restriction along a morphism `V' ⟶ i W` of the transport of a `W`-point of `U`; and the object
presented by a transport is the image under the comparison of the presentation `(V', φ, x)`,
because the comparison sends a presentation to the chosen pullback along `φ` of the image of `x`.

## Main definitions

* `AlgebraicGeometry.Stack.changeBigSiteQuotientMapFiber`: the image of an object of `[U/R]` under
  the 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]`, as an object of a fibre of `[f⁻¹U/f⁻¹R]`.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientMapPresentationIso`: the image of a presented
  object of `[U/R]` is isomorphic, over an identity of the enlarged site, to the object presented
  by the transported point.

## Main results

* `AlgebraicGeometry.Stack.changeBigSiteQuotientComparison_fiberObj`: the comparison sends the
  object of the fibre of `u_p [U/R]` determined by a presentation `(V, φ, x)` to the chosen
  pullback along `φ` of the image of `x`.
* `AlgebraicGeometry.Stack.exists_covering_sectionEquiv_restrict`: every section of the inverse
  image of an algebraic space is, along a covering sieve of its test object, the restriction of a
  transported section.
* `AlgebraicGeometry.Stack.essImage_changeBigSiteQuotientComparison`: **clause (2) of
  Stacks 02ZN** for the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.

## Implementation notes

The fibre of a functor carries its category structure through the instance argument of the
functor, which is no longer found by synthesis once the functor is a stackification of a
localization of a comma category over a big site. Clause (2), an isomorphism of fibre objects and
the image of a fibre object are therefore taken from
`StacksFrontier.CategoryTheory.FiberedCategory.FibreClause`, where they are stated for a generic
1-morphism of fibred categories: each statement here is an application of one of those names, so
the instance is instantiated rather than synthesised. For the same reason the quotient stack of
the pulled-back groupoid has its chosen pullbacks passed explicitly rather than by synthesis, and
the presented objects of a fibre go through
`AlgebraicGeometry.Stack.presentedFiber`, which is stated for a generic groupoid.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section


open CategoryTheory Opposite


namespace AlgebraicGeometry.Stack

universe u

section Presentations

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bs : AlgebraicSpaces C S hS}

/-- **The object of a fibre of the quotient stack presented by a point of the object space.** -/
def presentedFiber (G : GroupoidInAlgebraicSpaces C S hS Bs) (T : BigFppfOver C S hS)
    (w : G.objects.obj.obj (op T)) : (quotientStack G).p.Fiber T :=
  (pointwiseToQuotientStackFiber G T).obj w

/-- The stackification, read on fibres, sends the object determined by a point to the object
presented by that point. -/
lemma fiberMapObj_prestackPoint
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    (T : BigFppfOver C S hS) (w : G.objects.obj.obj (op T)) :
    Functor.fiberMapObj (isFibredOneMorphism_toQuotientStack G).comp_eq T
        (prestackPoint G T w) = presentedFiber G T w := by
  apply Subtype.ext
  rfl

/-- **The chosen pullback of a presented object is the object presented by the restricted
point.** -/
def presentedFiberPullbackIso (G : GroupoidInAlgebraicSpaces C S hS Bs)
    (T : BigFppfOver C S hS) (w : G.objects.obj.obj (op T)) (V : Over T) :
    Functor.FiberIso
      (Functor.pullbackFiber (quotientStack G).p (presentedFiber G T w) V.hom)
      (presentedFiber G V.left (G.objects.obj.map V.hom.op w)) :=
  presentedPullbackIso G T w _ rfl V

end Presentations

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- The quotient stack of the pulled-back groupoid has chosen pullbacks. -/
theorem isPreFibered_changeBigSiteQuotientStack :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsPreFibered :=
  have := isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G)
  inferInstance

/-- **The image of an object of `[U/R]` in a fibre of `[f⁻¹U/f⁻¹R]`.** The 1-morphism
`[U/R] ⟶ [f⁻¹U/f⁻¹R]` covers the localized inclusion, so the image of an object over `T` lies
over `i T`. -/
abbrev changeBigSiteQuotientMapFiber (x : (quotientStack G).obj) :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.Fiber
      ((inclusionOver h S hS).obj ((quotientStack G).p.obj x)) :=
  Functor.Fiber.mk (Functor.congr_obj (changeBigSiteQuotientMap_comp B B' h S hS G) x)

/-- **The comparison on the fibre object of a presentation.** The object of the fibre of
`u_p [U/R]` over `V` determined by a presentation `(V, φ : V ⟶ i T, x)` goes to the chosen
pullback along `φ` of the image of `x` in `[f⁻¹U/f⁻¹R]`. -/
theorem changeBigSiteQuotientComparison_fiberObj
    (V : BigFppfOver B' S (largerContains h hS)) (x : (quotientStack G).obj)
    (φ : V ⟶ (inclusionOver h S hS).obj ((quotientStack G).p.obj x)) :
    Functor.fiberMapObj
        (isFibredOneMorphism_changeBigSiteQuotientComparison B B' h S hS G).comp_eq V
        (Comma.fiberObj (quotientStack G).p (inclusionOver h S hS) V x φ) =
      Functor.pullbackFiber (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
        (changeBigSiteQuotientMapFiber B B' h S hS G x) φ := by
  refine Subtype.ext (Eq.trans (Functor.fiberMapObj_val _ _ _) ?_)
  refine Eq.trans (congrArg (changeBigSiteQuotientComparison B B' h S hS G).obj
    (Comma.fiberObj_val (quotientStack G).p (inclusionOver h S hS) V x φ)) ?_
  exact changeBigSiteQuotientComparison_obj_localization B B' h S hS G _

/-- **The image of a presented object is the object presented by the transported point**, by an
isomorphism of the fibre of `[f⁻¹U/f⁻¹R]` over the image of the test object. This is the
restriction of the 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]` along the stackification, read at a point of
the object space. -/
def changeBigSiteQuotientMapPresentationIso (W : BigFppfOver B S hS)
    (w : G.objects.obj.obj (op W)) :
    Functor.FiberIso
      (changeBigSiteQuotientMapFiber B B' h S hS G
        ((pointwiseToQuotientStack G).obj ⟨W, w⟩))
      (presentedFiber (changeBigSiteGroupoid B B' h S hS G)
        ((inclusionOver h S hS).obj W)
          (changeBigSiteSectionEquiv B B' h S hS G.objects W w)) :=
  Functor.FiberIso.mk'
    ((changeBigSiteQuotientMapUnit B B' h S hS G).app
      ((quotientPrestackEquivalence G).functor.obj ⟨W, w⟩))
    (isHomLift_changeBigSiteQuotientMapUnit_hom_app B B' h S hS G
      ((quotientPrestackEquivalence G).functor.obj ⟨W, w⟩))

/-- **Every section of the inverse image of an algebraic space is locally a transported
section**, in the form that names the covering sieve first: along a covering sieve of the test
object, the section is the restriction, along a morphism to the image of a test object of the
smaller site, of the transport of a section there. -/
theorem exists_covering_sectionEquiv_restrict (X : AlgebraicSpaces B S hS)
    (V : BigFppfOver B' S (largerContains h hS))
    (x : ((changeBigSite B B' h S hS).obj X).obj.obj (op V)) :
    ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ ⦃g : V' ⟶ V⦄, R.arrows g →
        ∃ (W : BigFppfOver B S hS) (w : X.obj.obj (op W))
          (φ : V' ⟶ (inclusionOver h S hS).obj W),
          ((changeBigSite B B' h S hS).obj X).obj.map g.op x =
            ((changeBigSite B B' h S hS).obj X).obj.map φ.op
              (changeBigSiteSectionEquiv B B' h S hS X W w) := by
  obtain ⟨W, w, R, hR, hRs⟩ := exists_sectionEquiv_restrict B B' h S hS X V x
  refine ⟨R, hR, ?_⟩
  intro V' g hg
  obtain ⟨φ, hφ⟩ := hRs g hg
  exact ⟨W, w, φ, hφ⟩

/-- **Clause (2) of Stacks 02ZN for the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.** Every
object of a fibre of `[f⁻¹U/f⁻¹R]` is, along a covering sieve of its test object, in the
essential image of the functor the comparison induces on fibres.

The covering sieve is the composite of the one along which the object is presented by a point of
`f⁻¹U` with, over each of its members, the one along which that point is the restriction of a
transported point of `U`. -/
theorem essImage_changeBigSiteQuotientComparison :
    Functor.IsLocallyEssImageOnFibers
        (isPreFibered_changeBigSiteQuotientStack B B' h S hS G)
        (isFibredOneMorphism_changeBigSiteQuotientComparison B B' h S hS G).comp_eq
        (BigFppfOver.topology B' S (largerContains h hS)) := by
  refine Functor.IsLocallyEssImageOnFibers.mk' ?_
  intro V x
  obtain ⟨R₁, hR₁, hess₁⟩ :=
    essImage_toQuotientStack (changeBigSiteGroupoid B B' h S hS G) V x
  have key : ∀ ⦃W : BigFppfOver B' S (largerContains h hS)⦄ ⦃g : W ⟶ V⦄, R₁.arrows g →
      ∃ w : (changeBigSiteGroupoid B B' h S hS G).objects.obj.obj (op W),
        Nonempty (Functor.FiberIso
          (presentedFiber (changeBigSiteGroupoid B B' h S hS G) W w)
          (Functor.pullbackFiber
            (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p x g)) := by
    intro W g hg
    obtain ⟨z, ⟨e⟩⟩ := hess₁ hg
    obtain ⟨w, rfl⟩ := exists_prestackPoint (changeBigSiteGroupoid B B' h S hS G) W z
    exact ⟨w, ⟨(Functor.FiberIso.ofEq (fiberMapObj_prestackPoint
      (changeBigSiteGroupoid B B' h S hS G) W w)).symm.trans e⟩⟩
  refine ⟨Sieve.bind R₁.arrows (fun {W} {g} hg =>
      (exists_covering_sectionEquiv_restrict B B' h S hS G.objects W (key hg).choose).choose),
    ?_, ?_⟩
  · refine (BigFppfOver.topology B' S (largerContains h hS)).bind_covering hR₁ ?_
    intro W g hg
    exact (exists_covering_sectionEquiv_restrict B B' h S hS G.objects W
      (key hg).choose).choose_spec.1
  · intro W k hk
    obtain ⟨W₁, g', g, hg, hg', rfl⟩ := hk
    obtain ⟨e⟩ := (key hg).choose_spec
    obtain ⟨W₀, w₀, φ, hφ⟩ := (exists_covering_sectionEquiv_restrict B B' h S hS G.objects W₁
      (key hg).choose).choose_spec.2 hg'
    refine ⟨Comma.fiberObj (quotientStack G).p (inclusionOver h S hS) W
        ((pointwiseToQuotientStack G).obj ⟨W₀, w₀⟩) φ, ⟨?_⟩⟩
    have hFib := isFibered_quotientStack_changeBigSite B B' h S hS G
    have A₀ := Functor.FiberIso.ofEq (changeBigSiteQuotientComparison_fiberObj B B' h S hS G W
      ((pointwiseToQuotientStack G).obj ⟨W₀, w₀⟩) φ)
    have A₁ := (changeBigSiteQuotientMapPresentationIso B B' h S hS G W₀ w₀).pullback hFib φ
    have A₂ := presentedFiberPullbackIso (changeBigSiteGroupoid B B' h S hS G)
      ((inclusionOver h S hS).obj W₀)
      (changeBigSiteSectionEquiv B B' h S hS G.objects W₀ w₀) (Over.mk φ)
    have A₃ := Functor.FiberIso.ofEq (congrArg
      (presentedFiber (changeBigSiteGroupoid B B' h S hS G) W) hφ.symm)
    have A₄ := (presentedFiberPullbackIso (changeBigSiteGroupoid B B' h S hS G) W₁
      (key hg).choose (Over.mk g')).symm
    have A₅ := Functor.FiberIso.pullback hFib e g'
    have A₆ := Functor.FiberIso.pullbackComp hFib x g g'
    exact (A₀.trans (A₁.trans (A₂.trans (A₃.trans (A₄.trans (A₅.trans A₆)))))).iso

end AlgebraicGeometry.Stack

end
