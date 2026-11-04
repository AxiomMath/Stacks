module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSections

/-!
# Sections of the inverse image of an algebraic space come locally from the smaller site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `X`
be an algebraic space over `S` for `B`, and write `i` for the localized inclusion. An étale
atlas of `X` transports to a locally surjective morphism `h_{i W} ⟶ f⁻¹X` with `W` an object of
the *smaller* site. Composing with the identification of the `i W`-points of `f⁻¹X` with the
`W`-points of `X` gives the form in which the enlargement is used: every section of `f⁻¹X` over
a test object `V` of the larger site agrees, locally on `V`, with a transported section of `X`
restricted along a morphism `V ⟶ i W`.

This is what makes an object of the larger site accessible from the smaller one. A test object
of the larger site need not come from the smaller one, and a section of `f⁻¹X` over it need not
be transported; but it becomes one after passing to a covering and composing with a morphism to
the image of an atlas.

## Main results

* `AlgebraicGeometry.exists_isLocallySurjective_toChangeBigSite`: the inverse image of an
  algebraic space receives a locally surjective morphism from the sheaf represented by an object
  of the smaller site.
* `AlgebraicGeometry.exists_sectionEquiv_restrict`: every section of the inverse image is, along
  a covering sieve, the restriction of a transported section.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **The inverse image of an algebraic space is covered by an object of the smaller site.**
The étale atlas of the algebraic space transports to a locally surjective morphism from the
sheaf represented by the image of the same object. -/
theorem exists_isLocallySurjective_toChangeBigSite (X : AlgebraicSpaces B S hS) :
    ∃ (W : BigFppfOver B S hS) (ψ : yoneda.obj ((inclusionOver h S hS).obj W) ⟶
        ((changeBigSite B B' h S hS).obj X).obj),
      Presheaf.IsLocallySurjective
        (BigFppfOver.topology B' S (largerContains h hS)) ψ := by
  obtain ⟨W, -, -, -, ψ, hψ, -, -, -⟩ :=
    exists_sheafPullback_atlas B B' h S hS X.obj X.property
  exact ⟨W, ψ, hψ⟩

/-- **Every section of the inverse image of an algebraic space is locally a transported
section.** Along a covering sieve of the test object, the section is the restriction, along a
morphism to the image of an atlas, of the transport of a section over that atlas. -/
theorem exists_sectionEquiv_restrict (X : AlgebraicSpaces B S hS)
    (V : BigFppfOver B' S (largerContains h hS))
    (x : ((changeBigSite B B' h S hS).obj X).obj.obj (op V)) :
    ∃ (W : BigFppfOver B S hS) (w : X.obj.obj (op W)) (R : Sieve V),
      R ∈ BigFppfOver.topology B' S (largerContains h hS) V ∧
        ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ (g : V' ⟶ V), R.arrows g →
          ∃ φ : V' ⟶ (inclusionOver h S hS).obj W,
            ((changeBigSite B B' h S hS).obj X).obj.map g.op x =
              ((changeBigSite B B' h S hS).obj X).obj.map φ.op
                (changeBigSiteSectionEquiv B B' h S hS X W w) := by
  obtain ⟨W, ψ, hψ⟩ := exists_isLocallySurjective_toChangeBigSite B B' h S hS X
  obtain ⟨w, hw⟩ : ∃ w, changeBigSiteSectionEquiv B B' h S hS X W w =
      ψ.app (op ((inclusionOver h S hS).obj W)) (𝟙 _) :=
    ⟨_, (changeBigSiteSectionEquiv B B' h S hS X W).apply_symm_apply _⟩
  refine ⟨W, w, Presheaf.imageSieve ψ x, hψ.imageSieve_mem x, ?_⟩
  intro V' g hg
  obtain ⟨φ, hφ⟩ := hg
  refine ⟨φ, ?_⟩
  rw [hw]
  have e1 : (yoneda.obj ((inclusionOver h S hS).obj W)).map φ.op
      (𝟙 ((inclusionOver h S hS).obj W)) = φ := Category.comp_id φ
  have e2 := NatTrans.naturality_apply ψ φ.op (𝟙 ((inclusionOver h S hS).obj W))
  rw [e1] at e2
  exact hφ.symm.trans e2

end AlgebraicGeometry

end
