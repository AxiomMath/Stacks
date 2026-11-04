module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreObjectTwoYoneda
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionCanonicalMap
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SliceGluing

/-!
# Descending an object of a fibre along the arrows of its self-intersection groupoid

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `U₀` be an object of
that site and `ξ` an object of the fibre of `𝒳` over `U₀`. The 2-Yoneda lemma (**Stacks 004B**)
names `ξ` by a 1-morphism `(Sch/U₀)_{fppf} ⟶ 𝒳`
(`AlgebraicGeometry.Stack.fibreObjectFibredMap`), and **Stacks 04T4** attaches to that 1-morphism
its self-intersection `ℛ = (Sch/U₀) ×_𝒳 (Sch/U₀)`, whose sections over a test object `Z` of the
site are — once `ℛ` is represented by an algebraic space `R` — in bijection with the morphisms of
the fibre of `𝒳` over `Z` between the pullbacks of `ξ` along two arrows `Z ⟶ U₀`
(`AlgebraicGeometry.Stack.SelfIntersection.arrowEquivOfSection`).

This file turns that bijection into the gluing data of a descent. Fix `q : U₀ ⟶ Ū` and a family
`Φ ε ε'` of sections of `R`, one for each pair of arrows `ε, ε' : Z ⟶ U₀` agreeing after `q`, with
`ε'` as source and `ε` as target. If the family is closed under the composition law of the
self-intersection groupoid and is natural in `Z`, then `ξ` descends along `q`: there is an object
of the fibre of `𝒳` over `Ū` whose pullback along `q` is `ξ`, as soon as `𝒳` is a stack and `q`
generates a covering sieve
(`AlgebraicGeometry.Stack.SelfIntersection.exists_iso_pullbackFiber_of_arrowFamily`).

The identification the whole file passes through is
`AlgebraicGeometry.Stack.SelfIntersection.pullbackFiberFObjIso`: the chosen pullback of `ξ` along
`ε` *is* the object `f (j⁻¹ ε)` of the fibre of `𝒳` that the self-intersection calculus uses, both
being cartesian lifts of `ε` at `ξ`. On the self-intersection side the chosen representative
`j⁻¹ ε` of the section `ε` is the object `(Z, ε)` of the slice `Sch/U₀` on the nose, because the
chart of the represented category fibred in groupoids is
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, whose backward functor reads
an element of the represented presheaf as that object of the slice; so `f (j⁻¹ ε)` is the value at
`(Z, ε)` of the 2-Yoneda functor of `ξ`, which is what
`StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SliceGluing` compares with the chosen pullback.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.pullbackFiberFObjIso`: **the chosen pullback of `ξ`
  along `ε`, identified with the fibre object of the self-intersection calculus.**
* `AlgebraicGeometry.Stack.SelfIntersection.fiberHomOfArrow`: the morphism of the fibre named by a
  section of the arrow space with prescribed source and target.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.arrowOfFiberHom_fiberHomOfArrow`: the section named by
  that morphism is the section it came from.
* `AlgebraicGeometry.Stack.SelfIntersection.fiberHomOfArrow_comp`: the composition law of the
  self-intersection groupoid on two such sections is matched by composition of the two morphisms of
  the fibre.
* `AlgebraicGeometry.Stack.SelfIntersection.fiberHomOfArrow_restrict`: restriction of such a
  section along an arrow of the site is the transport of the morphism of the fibre.
* `AlgebraicGeometry.Stack.SelfIntersection.exists_iso_pullbackFiber_of_arrowFamily`: **a
  composable, natural family of sections of the arrow space descends `ξ` along `q`.**

## Implementation notes

The two conditions of a gluing system are reduced to the two conditions on the family by the
injectivity of `AlgebraicGeometry.Stack.SelfIntersection.arrowOfFiberHom` on fibre morphisms with
fixed endpoints — `AlgebraicGeometry.Stack.SelfIntersection.arrowOfFiberHom_injective`, which is
where the source being fibred in setoids is used. It is so here with no hypothesis, the source
being the represented category fibred in groupoids: that is
`AlgebraicGeometry.Stack.SelfIntersection.isFiberedInSetoids_source` at its own chart.

Naturality is matched by the transport of a fibre morphism along an arrow of the site,
`AlgebraicGeometry.Stack.SelfIntersection.transportFiberHom` of
`StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionCanonicalMap`, and by the two statements
there which say that it does what is wanted: its defining square
`…fRestrict_comp_transportFiberHom` with the canonical morphisms `…fRestrict` between the images
of the chosen representatives, and `…arrowOfFiberHom_restrict`, that the section named by a fibre
morphism restricts to the section named by the transported one. At the represented chart those
canonical morphisms are the images under the 2-Yoneda functor of the arrows of the slice `Sch/U₀`
that `γ` gives, which is what the gluing system's compatibility condition asks for.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- An object `U₀` of the site, read as an algebraic space over `S`: its representable presheaf.

This is `AlgebraicGeometry.schemeSpace`, written with the constructor so that the presheaf is
recovered from it by a projection rather than by unfolding a definition — the rewriting tactics
re-elaborate their motives at a transparency at which they would not unfold it, and the statements
below mention both the algebraic space and its presheaf. -/
abbrev objectSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U₀ : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩

/-- **The chosen pullback of `ξ` along `ε`, identified with the object `f (j⁻¹ ε)` of the fibre
that the self-intersection calculus of Stacks 04T4 names.** Here `f` is the 1-morphism the
2-Yoneda lemma attaches to `ξ` and `j⁻¹` the chosen representative of a section of the object
space at the chart of the represented category fibred in groupoids; `f (j⁻¹ ε)` is then the value
of the 2-Yoneda functor of `ξ` at the object `(Z, ε)` of the slice, and the two objects are
compared as two cartesian lifts of `ε` at `ξ`. -/
noncomputable def pullbackFiberFObjIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U₀ : BigFppfOver B S hS) (ξ : 𝒳.val.p.Fiber U₀) {Z : BigFppfOver B S hS} (ε : Z ⟶ U₀) :
    haveI := 𝒳.isFiberedInGroupoids.isFibered
    Functor.pullbackFiber 𝒳.val.p ξ ε ≅
      Functor.Fiber.mk (fObj_over (B := B) (S := S) (hS := hS)
        (𝒰 := schemeFibredCategory B S hS U₀) (𝒳 := 𝒳)
        (f := (fibreObjectFibredMap B S hS 𝒳 U₀ ξ).hom) (U := objectSpace B S hS U₀)
        (representedChart B S hS U₀) (W := Z) ε) :=
  haveI := 𝒳.isFiberedInGroupoids.isFibered
  Functor.TwoYoneda.pullbackFiberSliceIso
    (Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.p 𝒳.isFiberedInGroupoids U₀ ξ)
    𝒳.isFiberedInGroupoids ε

section Family

variable (U₀ : BigFppfOver B S hS) (ξ : 𝒳.val.p.Fiber U₀) (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS (schemeFibredCategory B S hS U₀) 𝒳
      (fibreObjectFibredMap B S hS 𝒳 U₀ ξ).hom).val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

/-- The source category of the self-intersection of the 1-morphism named by `ξ` is fibred in
setoids: it is the represented category fibred in groupoids, and its own chart identifies it with
a category of elements. -/
theorem isFiberedInSetoids_represented :
    (schemeFibredCategory B S hS U₀).val.p.IsFiberedInSetoids :=
  isFiberedInSetoids_source (B := B) (S := S) (hS := hS)
    (𝒰 := schemeFibredCategory B S hS U₀) (U := objectSpace B S hS U₀)
    (representedChart B S hS U₀)

/-- **The morphism of the fibre named by a section of the arrow space with prescribed source and
target.** The chosen inverse of the bijection of Stacks 04T4 (4). -/
noncomputable def fiberHomOfArrow {Z : BigFppfOver B S hS} (ε ε' : Z ⟶ U₀)
    (r : Rsp.obj.obj (op Z))
    (hs : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r = ε')
    (ht : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r = ε) :
    (Functor.Fiber.mk (fObj_over (f := (fibreObjectFibredMap B S hS 𝒳 U₀ ξ).hom)
        (U := objectSpace B S hS U₀) (representedChart B S hS U₀) ε) : 𝒳.val.p.Fiber Z) ⟶
      Functor.Fiber.mk (fObj_over (f := (fibreObjectFibredMap B S hS 𝒳 U₀ ξ).hom)
        (U := objectSpace B S hS U₀) (representedChart B S hS U₀) ε') :=
  Classical.choose (exists_fiberHom_of_arrow (U := objectSpace B S hS U₀)
    (representedChart B S hS U₀) eR ε' ε r hs ht)

/-- The section named by `AlgebraicGeometry.Stack.SelfIntersection.fiberHomOfArrow` is the section
it was built from. -/
theorem arrowOfFiberHom_fiberHomOfArrow {Z : BigFppfOver B S hS} (ε ε' : Z ⟶ U₀)
    (r : Rsp.obj.obj (op Z))
    (hs : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r = ε')
    (ht : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r = ε) :
    arrowOfFiberHom (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR ε' ε
        (fiberHomOfArrow U₀ ξ Rsp eR ε ε' r hs ht) = r :=
  Classical.choose_spec (exists_fiberHom_of_arrow (U := objectSpace B S hS U₀)
    (representedChart B S hS U₀) eR ε' ε r hs ht)

/-- **The composition law of the self-intersection groupoid on two sections of the arrow space is
matched by composition of the two morphisms of the fibre they name.** -/
theorem fiberHomOfArrow_comp {Z : BigFppfOver B S hS} (ε₁ ε₂ ε₃ : Z ⟶ U₀)
    (r₁₂ r₂₃ r₁₃ : Rsp.obj.obj (op Z))
    (hs₁₂ : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r₁₂ = ε₂)
    (ht₁₂ : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r₁₂ = ε₁)
    (hs₂₃ : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r₂₃ = ε₃)
    (ht₂₃ : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r₂₃ = ε₂)
    (hs₁₃ : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r₁₃ = ε₃)
    (ht₁₃ : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r₁₃ = ε₁)
    (hmul : ∀ compat : (relationSourceMap (U := objectSpace B S hS U₀)
        (representedChart B S hS U₀) eR).app (op Z) r₁₂ =
      (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
        (op Z) r₂₃,
      (compositionLaw (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR
          (isFiberedInSetoids_represented U₀)).app (op Z) ⟨(r₁₂, r₂₃), compat⟩ = r₁₃) :
    fiberHomOfArrow U₀ ξ Rsp eR ε₁ ε₂ r₁₂ hs₁₂ ht₁₂ ≫
        fiberHomOfArrow U₀ ξ Rsp eR ε₂ ε₃ r₂₃ hs₂₃ ht₂₃ =
      fiberHomOfArrow U₀ ξ Rsp eR ε₁ ε₃ r₁₃ hs₁₃ ht₁₃ := by
  refine arrowOfFiberHom_injective (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR
    (isFiberedInSetoids_represented U₀) ε₃ ε₁ _ _ ?_
  have hcl := compositionLaw_app_sectionOfObj (U := objectSpace B S hS U₀)
    (representedChart B S hS U₀) eR (isFiberedInSetoids_represented U₀)
    (composableOfFiberHoms (𝒳 := 𝒳) (f := (fibreObjectFibredMap B S hS 𝒳 U₀ ξ).hom)
      (U := objectSpace B S hS U₀) (representedChart B S hS U₀) ε₃ ε₂ ε₁
        (fiberHomOfArrow U₀ ξ Rsp eR ε₂ ε₃ r₂₃ hs₂₃ ht₂₃)
        (fiberHomOfArrow U₀ ξ Rsp eR ε₁ ε₂ r₁₂ hs₁₂ ht₁₂))
  have hco := sectionOfObj_composition_composableOfFiberHoms (U := objectSpace B S hS U₀)
    (representedChart B S hS U₀) eR ε₃ ε₂ ε₁
    (fiberHomOfArrow U₀ ξ Rsp eR ε₂ ε₃ r₂₃ hs₂₃ ht₂₃)
    (fiberHomOfArrow U₀ ξ Rsp eR ε₁ ε₂ r₁₂ hs₁₂ ht₁₂)
  have hcongr : ∀ u v : (Deformation.composableArrows (objectSpace B S hS U₀).obj Rsp.obj
      (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR)
      (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR)).obj (op Z),
      u.1 = v.1 →
      (compositionLaw (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR
          (isFiberedInSetoids_represented U₀)).app (op Z) u =
        (compositionLaw (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR
          (isFiberedInSetoids_represented U₀)).app (op Z) v :=
    fun _ _ h => congrArg _ (Subtype.ext h)
  have compat : (relationSourceMap (U := objectSpace B S hS U₀)
        (representedChart B S hS U₀) eR).app (op Z) r₁₂ =
      (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
        (op Z) r₂₃ := by
    rw [hs₁₂, ht₂₃]
  rw [arrowOfFiberHom_fiberHomOfArrow, ← hco, ← hcl]
  refine (hcongr _ ⟨(r₁₂, r₂₃), compat⟩ (Prod.ext ?_ ?_)).trans (hmul compat)
  · exact arrowOfFiberHom_fiberHomOfArrow U₀ ξ Rsp eR ε₁ ε₂ r₁₂ hs₁₂ ht₁₂
  · exact arrowOfFiberHom_fiberHomOfArrow U₀ ξ Rsp eR ε₂ ε₃ r₂₃ hs₂₃ ht₂₃

/-- **Restriction along `γ` of a section of the arrow space is matched by the transport along `γ`
of the morphism of the fibre it names.** -/
theorem fiberHomOfArrow_restrict {Z Z' : BigFppfOver B S hS} (ε ε' : Z ⟶ U₀) (γ : Z' ⟶ Z)
    (r : Rsp.obj.obj (op Z))
    (hs : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r = ε')
    (ht : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z) r = ε)
    (r' : Rsp.obj.obj (op Z'))
    (hs' : (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z') r' = γ ≫ ε')
    (ht' : (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app
      (op Z') r' = γ ≫ ε)
    (hnat : r' = Rsp.obj.map γ.op r) :
    fiberHomOfArrow U₀ ξ Rsp eR (γ ≫ ε) (γ ≫ ε') r' hs' ht' =
      transportFiberHom (U := objectSpace B S hS U₀) (representedChart B S hS U₀) γ ε' ε
        (fiberHomOfArrow U₀ ξ Rsp eR ε ε' r hs ht) := by
  refine arrowOfFiberHom_injective (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR
    (isFiberedInSetoids_represented U₀) (γ ≫ ε') (γ ≫ ε) _ _ ?_
  have h1 := arrowOfFiberHom_restrict (U := objectSpace B S hS U₀)
    (representedChart B S hS U₀) eR γ ε' ε (fiberHomOfArrow U₀ ξ Rsp eR ε ε' r hs ht)
  have h2 := congrArg (fun z => Rsp.obj.map γ.op z)
    (arrowOfFiberHom_fiberHomOfArrow U₀ ξ Rsp eR ε ε' r hs ht)
  exact (arrowOfFiberHom_fiberHomOfArrow U₀ ξ Rsp eR (γ ≫ ε) (γ ≫ ε') r' hs' ht').trans
    (hnat.trans (h2.symm.trans h1))

/-- **A composable, natural family of sections of the arrow space descends `ξ` along `q`.** Let
`𝒳` be a stack over the big fppf site of `S`, let `ξ` be an object of its fibre over an object
`U₀` of the site, and let the self-intersection of the 1-morphism the 2-Yoneda lemma attaches to
`ξ` be represented by the algebraic space `R`. Let `q : U₀ ⟶ Ū` generate a covering sieve of `Ū`
and let `Φ ε ε'` be a section of `R` over `Z`, with source `ε'` and target `ε`, for every pair of
arrows `ε, ε' : Z ⟶ U₀` agreeing after `q`. If the family is closed under the composition law of
the self-intersection groupoid and is natural in `Z`, then `ξ` is the pullback along `q` of an
object of the fibre of `𝒳` over `Ū`. -/
theorem exists_iso_pullbackFiber_of_arrowFamily
    {J : GrothendieckTopology (BigFppfOver B S hS)} (hstack : 𝒳.val.p.IsStack J)
    {Ū : BigFppfOver B S hS} (q : U₀ ⟶ Ū)
    (hq : Sieve.generate (Presieve.singleton q) ∈ J Ū)
    (Φ : ∀ ⦃Z : BigFppfOver B S hS⦄ (ε ε' : Z ⟶ U₀), ε ≫ q = ε' ≫ q → Rsp.obj.obj (op Z))
    (hΦs : ∀ ⦃Z : BigFppfOver B S hS⦄ (ε ε' : Z ⟶ U₀) (h : ε ≫ q = ε' ≫ q),
      (relationSourceMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app (op Z)
        (Φ ε ε' h) = ε')
    (hΦt : ∀ ⦃Z : BigFppfOver B S hS⦄ (ε ε' : Z ⟶ U₀) (h : ε ≫ q = ε' ≫ q),
      (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app (op Z)
        (Φ ε ε' h) = ε)
    (hΦcomp : ∀ ⦃Z : BigFppfOver B S hS⦄ (ε₁ ε₂ ε₃ : Z ⟶ U₀) (h₁₂ : ε₁ ≫ q = ε₂ ≫ q)
      (h₂₃ : ε₂ ≫ q = ε₃ ≫ q) (h₁₃ : ε₁ ≫ q = ε₃ ≫ q)
      (compat : (relationSourceMap (U := objectSpace B S hS U₀)
          (representedChart B S hS U₀) eR).app (op Z) (Φ ε₁ ε₂ h₁₂) =
        (relationTargetMap (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR).app (op Z)
          (Φ ε₂ ε₃ h₂₃)),
      (compositionLaw (U := objectSpace B S hS U₀) (representedChart B S hS U₀) eR
          (isFiberedInSetoids_represented U₀)).app (op Z)
        ⟨(Φ ε₁ ε₂ h₁₂, Φ ε₂ ε₃ h₂₃), compat⟩ = Φ ε₁ ε₃ h₁₃)
    (hΦnat : ∀ ⦃Z Z' : BigFppfOver B S hS⦄ (ε ε' : Z ⟶ U₀) (h : ε ≫ q = ε' ≫ q) (γ : Z' ⟶ Z)
      (h' : (γ ≫ ε) ≫ q = (γ ≫ ε') ≫ q),
      Φ (γ ≫ ε) (γ ≫ ε') h' = Rsp.obj.map γ.op (Φ ε ε' h)) :
    haveI := hstack.isFibered
    ∃ x : 𝒳.val.p.Fiber Ū, Nonempty (ξ ≅ Functor.pullbackFiber 𝒳.val.p x q) := by
  have := hstack.isFibered
  refine Functor.TwoYoneda.exists_iso_pullbackFiber_of_sliceGluing 𝒳.isFiberedInGroupoids hstack
    (Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.p 𝒳.isFiberedInGroupoids U₀ ξ) hq
    (fun ⦃_⦄ ε ε' h => fiberHomOfArrow U₀ ξ Rsp eR ε ε' (Φ ε ε' h) (hΦs ε ε' h) (hΦt ε ε' h))
    (fun ⦃_⦄ ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ => ?_) (fun ⦃_ _⦄ ε ε' h γ h' => ?_)
  · exact fiberHomOfArrow_comp U₀ ξ Rsp eR ε₁ ε₂ ε₃ (Φ ε₁ ε₂ h₁₂) (Φ ε₂ ε₃ h₂₃) (Φ ε₁ ε₃ h₁₃)
      (hΦs ε₁ ε₂ h₁₂) (hΦt ε₁ ε₂ h₁₂) (hΦs ε₂ ε₃ h₂₃) (hΦt ε₂ ε₃ h₂₃) (hΦs ε₁ ε₃ h₁₃)
      (hΦt ε₁ ε₃ h₁₃) (fun compat => hΦcomp ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ compat)
  · rw [fiberHomOfArrow_restrict U₀ ξ Rsp eR ε ε' γ (Φ ε ε' h) (hΦs ε ε' h) (hΦt ε ε' h)
      (Φ (γ ≫ ε) (γ ≫ ε') h') (hΦs (γ ≫ ε) (γ ≫ ε') h') (hΦt (γ ≫ ε) (γ ≫ ε') h')
      (hΦnat ε ε' h γ h')]
    exact fRestrict_comp_transportFiberHom (U := objectSpace B S hS U₀)
      (representedChart B S hS U₀) γ ε' ε
      (fiberHomOfArrow U₀ ξ Rsp eR ε ε' (Φ ε ε' h) (hΦs ε ε' h) (hΦt ε ε' h))

end Family

end AlgebraicGeometry.Stack.SelfIntersection

end
