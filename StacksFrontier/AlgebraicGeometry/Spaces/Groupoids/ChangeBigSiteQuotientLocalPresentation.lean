module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientLocalObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientPrestackPoint

/-!
# Two objects of a quotient stack are presented by points over a common base, locally on the
enlarged site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G` be
a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and write `i` for the
localized inclusion.

Part (1) of Stacks 044X presents every object of a fibre of `[U/R]` by a point of the object
space, along a covering sieve of its test object. Two objects `x` and `y` of `[U/R]` together with
a morphism `b : p x ⟶ p y` of the smaller site are presented *simultaneously*, over one test
object: pull the covering sieve for `y` back along `b` and intersect it with the one for `x`.

Transferring the resulting covering sieve of `p x` to a covering sieve of a test object `V` of the
enlarged site along a morphism `φ : V ⟶ i (p x)` — which is possible because the localized
inclusion is continuous — gives the form in which the arguments of Stacks 04WX consume it.

## Main results

* `AlgebraicGeometry.Stack.exists_presented_pair`: along a covering sieve of `p x`, both `x` and
  `y` are presented by points of the object space over one test object.
* `AlgebraicGeometry.Stack.exists_covering_presented_pair`: the same, transferred along
  `φ : V ⟶ i (p x)` to a covering sieve of `V`.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

section Presentations

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bs : AlgebraicSpaces C S hS}

/-- **Every object of a fibre of the quotient stack is presented by a point of the object space,
along a covering sieve of its test object**, in the form that names the point. This is part (1) of
Stacks 044X with the essential image unwound. -/
theorem exists_covering_presented (G : GroupoidInAlgebraicSpaces C S hS Bs)
    (T : BigFppfOver C S hS) (z : (quotientStack G).p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃W : BigFppfOver C S hS⦄ ⦃d : W ⟶ T⦄, R.arrows d →
        ∃ w : G.objects.obj.obj (op W),
          Nonempty (Functor.FiberIso (presentedFiber G W w)
            (Functor.pullbackFiber (quotientStack G).p z d)) := by
  obtain ⟨R, hR, hess⟩ := essImage_toQuotientStack G T z
  refine ⟨R, hR, ?_⟩
  intro W d hd
  obtain ⟨c, ⟨e⟩⟩ := hess hd
  obtain ⟨w, rfl⟩ := exists_prestackPoint G W c
  exact ⟨w, ⟨(Functor.FiberIso.ofEq (fiberMapObj_prestackPoint G W w)).symm.trans e⟩⟩

end Presentations

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **Two objects of the quotient stack are presented by points of the object space over one test
object, along a covering sieve of the base of the first.** The covering sieve is the intersection
of the sieve presenting the first object with the pullback along `b` of the sieve presenting the
second. -/
theorem exists_presented_pair (x y : (quotientStack G).obj)
    (b : (quotientStack G).p.obj x ⟶ (quotientStack G).p.obj y) :
    ∃ R ∈ BigFppfOver.topology B S hS ((quotientStack G).p.obj x),
      ∀ ⦃W : BigFppfOver B S hS⦄ ⦃d : W ⟶ (quotientStack G).p.obj x⦄, R.arrows d →
        ∃ a a' : G.objects.obj.obj (op W),
          Nonempty (Functor.FiberIso (presentedFiber G W a)
            (Functor.pullbackFiber (quotientStack G).p
              (Functor.Fiber.mk (rfl : (quotientStack G).p.obj x = _)) d)) ∧
          Nonempty (Functor.FiberIso (presentedFiber G W a')
            (Functor.pullbackFiber (quotientStack G).p
              (Functor.Fiber.mk (rfl : (quotientStack G).p.obj y = _)) (d ≫ b))) := by
  obtain ⟨R₁, hR₁, hspec₁⟩ := exists_covering_presented G ((quotientStack G).p.obj x)
    (Functor.Fiber.mk (rfl : (quotientStack G).p.obj x = _))
  obtain ⟨R₂, hR₂, hspec₂⟩ := exists_covering_presented G ((quotientStack G).p.obj y)
    (Functor.Fiber.mk (rfl : (quotientStack G).p.obj y = _))
  refine ⟨R₁ ⊓ Sieve.pullback b R₂,
    (BigFppfOver.topology B S hS).intersection_covering hR₁
      ((BigFppfOver.topology B S hS).pullback_stable _ hR₂), ?_⟩
  intro W d hd
  obtain ⟨a, ha⟩ := hspec₁ hd.1
  obtain ⟨a', ha'⟩ := hspec₂ hd.2
  exact ⟨a, a', ha, ha'⟩

/-- **Two objects of the quotient stack are presented by points of the object space over one test
object, locally on a test object of the enlarged site.** Along a covering sieve of `V`, the
morphism `φ` factors through the image of a test object `W` of the smaller site over which both
objects are presented by points.

The covering sieve of `V` is the one transferred from the smaller site by
`CategoryTheory.Comma.mem_pullback_functorPushforward`, the localized inclusion being
continuous. -/
theorem exists_covering_presented_pair (x y : (quotientStack G).obj)
    (b : (quotientStack G).p.obj x ⟶ (quotientStack G).p.obj y)
    (V : BigFppfOver B' S (largerContains h hS))
    (φ : V ⟶ (inclusionOver h S hS).obj ((quotientStack G).p.obj x)) :
    ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V₁ : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (W : BigFppfOver B S hS) (d : W ⟶ (quotientStack G).p.obj x)
          (χ : V₁ ⟶ (inclusionOver h S hS).obj W) (a a' : G.objects.obj.obj (op W)),
          β ≫ φ = χ ≫ (inclusionOver h S hS).map d ∧
          Nonempty (Functor.FiberIso (presentedFiber G W a)
            (Functor.pullbackFiber (quotientStack G).p
              (Functor.Fiber.mk (rfl : (quotientStack G).p.obj x = _)) d)) ∧
          Nonempty (Functor.FiberIso (presentedFiber G W a')
            (Functor.pullbackFiber (quotientStack G).p
              (Functor.Fiber.mk (rfl : (quotientStack G).p.obj y = _)) (d ≫ b))) := by
  have hcont : (inclusionOver h S hS).IsContinuous (BigFppfOver.topology B S hS)
      (BigFppfOver.topology B' S (largerContains h hS)) :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  obtain ⟨R, hR, hspec⟩ := exists_presented_pair B S hS G x y b
  refine ⟨_, mem_pullback_functorPushforward (inclusionOver h S hS)
    (BigFppfOver.topology B S hS) (BigFppfOver.topology B' S (largerContains h hS)) hR φ, ?_⟩
  intro V₁ β hβ
  obtain ⟨W, d, χ, hd, hfac⟩ :=
    exists_factorisation_of_mem_pullback_functorPushforward (inclusionOver h S hS) φ hβ
  obtain ⟨a, a', ha, ha'⟩ := hspec hd
  exact ⟨W, d, χ, a, a', hfac, ha, ha'⟩

end AlgebraicGeometry.Stack

end
