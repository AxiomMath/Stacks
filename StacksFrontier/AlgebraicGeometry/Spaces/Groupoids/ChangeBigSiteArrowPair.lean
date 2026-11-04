module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteArrowSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackChangeBigSite

/-!
# Arrows of the inverse-image groupoid between points over two different test objects

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let
`G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space over `S` for `B`,
and write `i` for the localized inclusion.

`AlgebraicGeometry.Space.exists_covering_arrow_restrict` describes an arrow of `f⁻¹G` whose two
endpoints are the restrictions, along *one* morphism `V ⟶ i T`, of the transports of two points
of the object space over the same test object `T`. In the quotient-stack arguments the two
endpoints arrive over *different* test objects `W` and `W'`, restricted along two different
morphisms `χ : V ⟶ i W` and `χ' : V ⟶ i W'`.

This file reduces that situation to the previous one: the product of the two test objects exists
in the smaller localized big fppf site and the localized inclusion preserves it, so `χ` and `χ'`
combine into a single morphism to the image of one test object mapping to both, and the two points
pull back along the two projections.

## Main results

* `AlgebraicGeometry.Space.exists_commonBase`: two morphisms out of a test object of the enlarged
  site into the images of two test objects of the smaller one factor through the image of a single
  test object mapping to both.
* `AlgebraicGeometry.Space.exists_covering_arrow_restrict_pair`: **an arrow of the inverse image
  of the groupoid between the transports of two points over two different test objects is locally
  a transported arrow**, over a test object of the smaller site mapping to both.

## Implementation notes

The finite completeness of a localized big fppf site is recorded as a `theorem` and applied
explicitly rather than left to instance search: the proof that the larger site contains `S` is a
compound term, and an instance keyed on `AlgebraicGeometry.BigFppfOver` is then not found for the
enlarged site, although the same statement applied by hand elaborates. For that reason the product
of the two test objects is introduced inside a tactic proof, by
`AlgebraicGeometry.Space.exists_commonBase`, and never appears in the statement of a declaration.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- A localized big fppf site has all finite limits. This is the finite completeness of
Stacks 022K, transported along `AlgebraicGeometry.BigFppfOver`. -/
theorem hasFiniteLimits_bigFppfOver : HasFiniteLimits (BigFppfOver B S hS) :=
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  inferInstance

/-- **Two morphisms into the images of two test objects of the smaller site factor through the
image of a single test object mapping to both**: the product of the two test objects, which the
localized inclusion preserves. -/
theorem exists_commonBase (W W' : BigFppfOver B S hS)
    (V : BigFppfOver B' S (largerContains h hS)) (χ : V ⟶ (inclusionOver h S hS).obj W)
    (χ' : V ⟶ (inclusionOver h S hS).obj W') :
    ∃ (T : BigFppfOver B S hS) (p₁ : T ⟶ W) (p₂ : T ⟶ W')
      (ξ : V ⟶ (inclusionOver h S hS).obj T),
      ξ ≫ (inclusionOver h S hS).map p₁ = χ ∧ ξ ≫ (inclusionOver h S hS).map p₂ = χ' := by
  obtain ⟨⟨cone, hcone⟩⟩ := (((hasFiniteLimits_bigFppfOver B S hS).out
    (Discrete WalkingPair)).has_limit (pair W W')).exists_limit
  obtain ⟨hmap⟩ := ((inclusionOver_preservesLimitsOfShape_of_nonempty h S hS
    (Discrete WalkingPair)).preservesLimit (K := pair W W')).preserves hcone
  refine ⟨cone.pt, cone.π.app ⟨WalkingPair.left⟩, cone.π.app ⟨WalkingPair.right⟩,
    hmap.lift { pt := V, π := Discrete.natTrans (fun j => match j with
      | ⟨WalkingPair.left⟩ => χ
      | ⟨WalkingPair.right⟩ => χ') }, ?_, ?_⟩
  · exact hmap.fac _ ⟨WalkingPair.left⟩
  · exact hmap.fac _ ⟨WalkingPair.right⟩

variable {Bs : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- The restriction along a factoring morphism of the transport of a point pulled back along the
factor is the restriction of the transport along the original morphism. -/
theorem changeBigSite_factor_restrict (X : AlgebraicSpaces B S hS)
    {T W : BigFppfOver B S hS} (d : T ⟶ W) (z : X.obj.obj (op W))
    {V : BigFppfOver B' S (largerContains h hS)} {ξ : V ⟶ (inclusionOver h S hS).obj T}
    {χ : V ⟶ (inclusionOver h S hS).obj W}
    (hξ : ξ ≫ (inclusionOver h S hS).map d = χ) :
    ((changeBigSite B B' h S hS).obj X).obj.map ξ.op
        (changeBigSiteSectionEquiv B B' h S hS X T (X.obj.map d.op z)) =
      ((changeBigSite B B' h S hS).obj X).obj.map χ.op
        (changeBigSiteSectionEquiv B B' h S hS X W z) := by
  rw [changeBigSiteSectionEquiv_restrict B B' h S hS X d z, ← hξ]
  exact (Functor.map_comp_apply _ _ _ _).symm

/-- **An arrow of the inverse image of the groupoid between the transports of two points over two
different test objects is locally a transported arrow.** Along a covering sieve of the test object
of the enlarged site, the arrow is the restriction, along a morphism to the image of a test object
`W₂` of the smaller site mapping to both `W` and `W'`, of the transport of an arrow over `W₂`
whose endpoints are the two points pulled back along those two morphisms.

This is `AlgebraicGeometry.Space.exists_covering_arrow_restrict` for the two points pulled back to
the common base of `AlgebraicGeometry.Space.exists_commonBase`, whose image under the localized
inclusion receives both given morphisms at once. -/
theorem exists_covering_arrow_restrict_pair (W W' : BigFppfOver B S hS)
    (x : G.objects.obj.obj (op W)) (y : G.objects.obj.obj (op W'))
    (V : BigFppfOver B' S (largerContains h hS)) (χ : V ⟶ (inclusionOver h S hS).obj W)
    (χ' : V ⟶ (inclusionOver h S hS).obj W')
    (r : ((changeBigSite B B' h S hS).obj G.arrows).obj.obj (op V))
    (hy : ((changeBigSite B B' h S hS).map G.target).hom.app (op V) r =
      ((changeBigSite B B' h S hS).obj G.objects).obj.map χ'.op
        (changeBigSiteSectionEquiv B B' h S hS G.objects W' y))
    (hx : ((changeBigSite B B' h S hS).map G.source).hom.app (op V) r =
      ((changeBigSite B B' h S hS).obj G.objects).obj.map χ.op
        (changeBigSiteSectionEquiv B B' h S hS G.objects W x)) :
    ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V' ⟶ V⦄, R.arrows β →
        ∃ (W₂ : BigFppfOver B S hS) (d : W₂ ⟶ W) (d' : W₂ ⟶ W')
          (χ₂ : V' ⟶ (inclusionOver h S hS).obj W₂) (r₀ : G.arrows.obj.obj (op W₂)),
          χ₂ ≫ (inclusionOver h S hS).map d = β ≫ χ ∧
          χ₂ ≫ (inclusionOver h S hS).map d' = β ≫ χ' ∧
          G.target.hom.app (op W₂) r₀ = G.objects.obj.map d'.op y ∧
          G.source.hom.app (op W₂) r₀ = G.objects.obj.map d.op x ∧
          ((changeBigSite B B' h S hS).obj G.arrows).obj.map β.op r =
            ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ₂.op
              (changeBigSiteSectionEquiv B B' h S hS G.arrows W₂ r₀) := by
  obtain ⟨T, p₁, p₂, ξ, hξ₁, hξ₂⟩ := exists_commonBase B B' h S hS W W' V χ χ'
  obtain ⟨R₀, hR₀, hspec⟩ := exists_covering_arrow_restrict B B' h S hS G T
    (G.objects.obj.map p₁.op x) (G.objects.obj.map p₂.op y) V ξ r
    (hy.trans (changeBigSite_factor_restrict B B' h S hS G.objects p₂ y hξ₂).symm)
    (hx.trans (changeBigSite_factor_restrict B B' h S hS G.objects p₁ x hξ₁).symm)
  refine ⟨R₀, hR₀, fun V' β hβ => ?_⟩
  obtain ⟨W₂, e, χ₂, r₀, hfac, htgt, hsrc, hres⟩ := hspec hβ
  have comp : ∀ {W₀ : BigFppfOver B S hS} (p : T ⟶ W₀) (χ₀ : V ⟶ (inclusionOver h S hS).obj W₀),
      ξ ≫ (inclusionOver h S hS).map p = χ₀ → χ₂ ≫ (inclusionOver h S hS).map (e ≫ p) = β ≫ χ₀ :=
    fun p _ hp => by
      refine (congrArg (χ₂ ≫ ·) (Functor.map_comp (inclusionOver h S hS) e p)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact ((congrArg (· ≫ _) hfac).trans (Category.assoc _ _ _)).trans (congrArg (β ≫ ·) hp)
  exact ⟨W₂, e ≫ p₁, e ≫ p₂, χ₂, r₀, comp p₁ χ hξ₁, comp p₂ χ' hξ₂,
    htgt.trans (Functor.map_comp_apply _ _ _ _).symm,
    hsrc.trans (Functor.map_comp_apply _ _ _ _).symm, hres⟩

end AlgebraicGeometry.Space

end
