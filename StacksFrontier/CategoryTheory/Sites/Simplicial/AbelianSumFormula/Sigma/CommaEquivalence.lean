module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.CommaDecomposition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.Sigma.ColimitDecomposition

/-!
# The comma category of a component inclusion is a disjoint union, and colimits over it split

Let `Cs` be a simplicial site — case (A) of the simplicial-site situation of Stacks 09WE — let
`(m, W)` be an object of its total category and let `n` be a simplicial degree. The summand
inclusions `Stacks.Sites.AbelianSumFormula.summandInclusion`, with `base_eq_of_hom` and
`summandInclusion_obj_mk_hom_fiber`, say that the comma category of the degree-`n` component
inclusion over `(m, W)` is the disjoint union, over the simplex maps `ψ : n ⟶ m`, of the comma
categories of the transition functors `u_ψ` over `W`. Here that is assembled into the statement
that the functor induced on the disjoint union by the summand inclusions is an *equivalence*, and
the decomposition of a colimit over the comma category as the coproduct of the colimits over the
summands is read off from it.

Both are given for the comma category and for its opposite, which is the shape over which a left
Kan extension to the total site is computed.

## Main results

* `Stacks.Sites.AbelianSumFormula.sigmaDesc_summandInclusion_isEquivalence`: the comma category of
  the component inclusion over `(m, W)` is the disjoint union of the comma categories of the
  transition functors over `W`.
* `Stacks.Sites.AbelianSumFormula.sigmaDesc_summandInclusion_op_isEquivalence`: the same for the
  opposite categories.
* `Stacks.Sites.AbelianSumFormula.isIso_sigmaDesc_colimitPre_summandInclusion_op`: **a colimit
  over the opposite of the comma category of the component inclusion is the coproduct, over the
  simplex maps `ψ : n ⟶ m`, of the colimits over the opposites of the comma categories of the
  transition functors.** This is the shape of the sum formula of Stacks 09WG.

## Implementation notes

The disjointness hypothesis of the criterion is `base_eq_of_hom` — a morphism of the comma
category cannot change the simplex map — and the exhaustion hypothesis is
`summandInclusion_obj_mk_hom_fiber`, which holds by `rfl`, so the isomorphism it is turned into
is an `eqToIso`. Nothing in either direction transports along the equality of simplex maps.

For the opposite categories the same two hypotheses are used through `Quiver.Hom.unop`: a
morphism of the opposite comma category is a morphism of the comma category in the other
direction, so disjointness is the same statement read backwards.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

universe v u

namespace Stacks.Sites.AbelianSumFormula

variable {Cs : SimplicialSite.{u}} {m n : SimplexCategory} {W : Cs.underlying.obj m}

/-- A morphism between objects in the images of two summand inclusions forces the simplex maps to
agree. -/
private theorem eq_of_summandInclusion_hom {ψ ψ' : n ⟶ m}
    {x : StructuredArrow W (Cs.underlying.map ψ).toFunctor}
    {y : StructuredArrow W (Cs.underlying.map ψ').toFunctor}
    (g : (summandInclusion ψ).obj x ⟶ (summandInclusion ψ').obj y) : ψ = ψ' :=
  Quiver.Hom.op_inj (base_eq_of_hom g)

/-- **The comma category of a component inclusion is the disjoint union of the comma categories of
the transition functors.** In case (A) of Stacks 09WE, the functor induced on the disjoint union
over the simplex maps `ψ : n ⟶ m` by the summand inclusions is an equivalence onto the comma
category of the degree-`n` component inclusion over `(m, W)`. -/
theorem sigmaDesc_summandInclusion_isEquivalence :
    (CategoryTheory.Sigma.desc fun ψ : n ⟶ m => summandInclusion (W := W) ψ).IsEquivalence := by
  refine sigmaDesc_isEquivalence _ (fun ψ ψ' x y g => ?_) (fun z => ?_)
  · exact eq_of_summandInclusion_hom g
  · exact ⟨z.hom.base.unop, StructuredArrow.mk (Y := z.right) z.hom.fiber,
      ⟨eqToIso (summandInclusion_obj_mk_hom_fiber z)⟩⟩

/-- The opposite of the comma category of a component inclusion is the disjoint union of the
opposites of the comma categories of the transition functors. -/
theorem sigmaDesc_summandInclusion_op_isEquivalence :
    (CategoryTheory.Sigma.desc
      fun ψ : n ⟶ m => (summandInclusion (W := W) ψ).op).IsEquivalence := by
  refine sigmaDesc_isEquivalence _ (fun ψ ψ' x y g => ?_) (fun z => ?_)
  · exact (eq_of_summandInclusion_hom g.unop).symm
  · exact ⟨z.unop.hom.base.unop, op (StructuredArrow.mk (Y := z.unop.right) z.unop.hom.fiber),
      ⟨eqToIso (congrArg Opposite.op (summandInclusion_obj_mk_hom_fiber z.unop))⟩⟩

section Colimits

variable {A : Type v} [Category.{u} A]
  (G : (StructuredArrow (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
    (CoGrothendieck.ι Cs.totalPseudofunctor (op n)))ᵒᵖ ⥤ A)
  [HasColimit G] [∀ ψ : n ⟶ m, HasColimit ((summandInclusion (W := W) ψ).op ⋙ G)]
  [HasCoproduct fun ψ : n ⟶ m => colimit ((summandInclusion (W := W) ψ).op ⋙ G)]

/-- **The sum formula for colimits over the comma category of a component inclusion.** A colimit
over the opposite of the comma category of the degree-`n` component inclusion over `(m, W)` is
the coproduct, over the simplex maps `ψ : n ⟶ m`, of the colimits over the opposites of the comma
categories of the transition functors over `W`; the identification is the canonical comparison
map. -/
theorem isIso_sigmaDesc_colimitPre_summandInclusion_op :
    IsIso (Limits.Sigma.desc fun ψ : n ⟶ m =>
      colimit.pre G (summandInclusion (W := W) ψ).op) :=
  have := sigmaDesc_summandInclusion_op_isEquivalence (W := W) (n := n)
  isIso_sigmaDesc_colimitPre _ G

/-- The sum formula for colimits over the comma category of a component inclusion, as an
isomorphism. -/
noncomputable def commaColimitSumIso :
    (∐ fun ψ : n ⟶ m => colimit ((summandInclusion (W := W) ψ).op ⋙ G)) ≅ colimit G :=
  haveI := sigmaDesc_summandInclusion_op_isEquivalence (W := W) (n := n)
  colimitDecompositionIso _ G

/-- The forward map of `commaColimitSumIso` is the map out of the coproduct induced by the
canonical comparison maps `colimit.pre`. -/
@[simp]
theorem commaColimitSumIso_hom :
    (commaColimitSumIso G).hom =
      Limits.Sigma.desc fun ψ : n ⟶ m => colimit.pre G (summandInclusion (W := W) ψ).op := rfl

end Colimits

end Stacks.Sites.AbelianSumFormula

end
