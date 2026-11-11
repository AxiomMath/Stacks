module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraicSizeBound

/-!
# Stacks 02WQ under the hypothesis of the source

Stacks 02WQ asks that `I` and the algebraic spaces `Fᵢ` be "not too large", and makes this
precise as follows: if surjective étale charts `Uᵢ → Fᵢ` can be chosen so that `∐ Uᵢ` is an
object of the site, then the coproduct `∐ Fᵢ` of fppf sheaves is an algebraic space. This file
states the theorem under exactly that hypothesis.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit_of_contains`: a coproduct of algebraic
  spaces over `S` whose chosen charts have their disjoint union in the site is an algebraic
  space over `S`.

## Implementation notes

The disjoint union of the charts, known to lie in the site, carries the universal property of a
coproduct *inside* the site by
`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt`, which is the form
`AlgebraicGeometry.isAlgebraicSpace_coproduct` consumes. The diagonal clause is
`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`, proved there for an index
type of any size: a fibre product `V ×_G W` of two representables splits, along the
decomposition of Stacks 02WO, into the pieces `Vᵢ ×_{Fᵢ} Wᵢ`, monomorphisms into `V ×_S W`, and
their union is an object of the site by a size bound which does not involve `#I`. No bound on
the index type and no hypothesis on the diagonal is therefore assumed, unlike
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` (cofinality bound) and
`AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains` (diagonal assumed, atlas only).

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 02WQ.** Let `G` be the coproduct, in fppf sheaves over `S`, of algebraic spaces
`Fᵢ`, and let `aᵢ : Uᵢ → Fᵢ` be surjective étale charts whose coproduct `∐ Uᵢ` of underlying
schemes is an object of the site. Then `G` is an algebraic space over `S`.

No bound on the index type and no hypothesis on the diagonal is assumed. The disjoint union
`∐ Uᵢ` becomes a coproduct inside the site by
`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt`, and
`AlgebraicGeometry.isAlgebraicSpace_coproduct` concludes; there the diagonal of `G` is
`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`, proved for an index type
of any size by splitting `V ×_G W` into the pieces `Vᵢ ×_{Fᵢ} Wᵢ`. -/
@[stacks 02WQ "the precise hypothesis of the source: the coproduct of a choice of surjective \
étale charts of the members is an object of the site; no bound on the index type"]
theorem isAlgebraicSpace_of_isColimit_of_contains
    {I : Type u} {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hFᵢ : ∀ i, IsAlgebraicSpace B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (Uᵢ : I → BigFppfOver B S hS) (aᵢ : ∀ i, yoneda.obj (Uᵢ i) ⟶ (Fᵢ i).obj)
    (hsurjᵢ : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (aᵢ i))
    (hetᵢ : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (aᵢ i))
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Uᵢ i))) :
    IsAlgebraicSpace B S hS G.obj := by
  obtain ⟨V, j, ⟨hV⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt B S hS Uᵢ hsum
  exact isAlgebraicSpace_coproduct B S hS (fun i => (Fᵢ i).obj) hFᵢ G jj hcoprod Uᵢ aᵢ
    hsurjᵢ hetᵢ V j hV

end AlgebraicGeometry.Space

end
