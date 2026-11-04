module

public import StacksFrontier.CategoryTheory.Limits.MapFormalCoproductLimits
public import StacksFrontier.CategoryTheory.Limits.NonemptyFiniteProducts
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.RefinementTransfer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refining a hypercovering of the final presheaf by a covering in one degree

[Stacks, Tag 01GJ] refines a hypercovering of an *object* of a site by a covering of one of its
terms. A hypercovering of the final presheaf is not a hypercovering of an object, and the category
`SR(C)` of semi-representable objects of the site has no terminal object unless the site does, so
the proof of Tag 01GJ is not available there. This file carries Tag 01GJ across.

## Main results

* `exists_hypercoveringOfTerminal_map_factoring_through_covering`: a covering of the term in a
  fixed degree of a hypercovering of the final presheaf can be incorporated into a refinement.

## Implementation notes

The refinement is formed twice: once in `SR(C)`, where it is only a simplicial object, and once in
`SR(C, *)` -- the semi-representable objects over the final presheaf -- where
`isHypercovering_refinementByCovering` says it is a hypercovering for `localPretopology`. The two
are identified by `refinementByCoveringCompIso`, the Yoneda embedding preserving everything the
construction uses: the degreewise powers by `C[k]`, which are products over a finite nonempty
index set, and the degreewise fibre products. `hypercoveringOfTerminal_lift` then descends the
hypercovering property to the refinement formed in `SR(C)`.

The Yoneda embedding of semi-representable objects is `mapFormalCoproduct` of the Yoneda embedding
of the site, and a product or fibre product of formal coproducts is computed summandwise, so the
preservation statements come from `preservesLimitsOfShape_discrete_mapFormalCoproduct` and
`preservesLimitsOfShape_walkingCospan_mapFormalCoproduct` together with the preservation of all
limits by Yoneda.

Products over the index sets `C[k]_n = Mor_Δ(⦋k⦌, ⦋n⦌)` are available because those sets are
finite and nonempty, which `hasProductsOfShape_of_finite_of_elem` turns into products out of
binary ones with no terminal object; this is why `C` is asked for products of pairs, which is
exactly what [Stacks, Tag 09VZ] grants, and not for a terminal object.

## References

* [Stacks Project, Tag 01GJ](https://stacks.math.columbia.edu/tag/01GJ)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

/- `FormalCoproduct.instHasProductsOfShape` builds a product of a nonempty finite family out of
binary ones, and is used here through the theorem it comes from, never by instance search. As an
instance it is a second route to every `HasProduct` goal in this file, and the search it adds --
`Inhabited` of an index type that may well be empty -- exhausts the elaboration budget of the
refinement below. -/
attribute [-instance] CategoryTheory.Limits.FormalCoproduct.instHasProductsOfShape

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
  [HasBinaryProducts C]

/-- The products over the coordinates of `C[k]` exist in the site: those index sets are finite
and nonempty, and products of pairs are available. -/
instance hasProductsOfShape_simplexPowerIndex (k : ℕ) (m : SimplexCategoryᵒᵖ) :
    HasProductsOfShape ((simplexPowerIndex.{max w u v} k).obj m.unop) C :=
  hasProductsOfShape_of_finite_of_elem _ _ (nonempty_simplexPowerIndex_obj k m.unop).some

/-- The products over the coordinates of `C[k]` exist in `SR(C)`: products of pairs of
semi-representable objects exist, and the index sets are finite and nonempty, so no terminal
object -- which `SR(C)` has only when `C` does -- is needed. -/
instance hasProductsOfShape_simplexPowerIndex_formalCoproduct (k : ℕ) (m : SimplexCategoryᵒᵖ) :
    HasProductsOfShape ((simplexPowerIndex.{max w u v} k).obj m.unop)
      (FormalCoproduct.{max w u v} C) :=
  hasProductsOfShape_of_finite_of_elem _ _ (nonempty_simplexPowerIndex_obj k m.unop).some

/-- The products over the coordinates of `C[k]` exist in `SR(C, *)`. -/
instance hasProductsOfShape_simplexPowerIndex_formalCoproduct_over (k : ℕ)
    (m : SimplexCategoryᵒᵖ) :
    HasProductsOfShape ((simplexPowerIndex.{max w u v} k).obj m.unop)
      (FormalCoproduct.{max w u v} (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))) :=
  hasProductsOfShape_of_finite_of_elem _ _ (nonempty_simplexPowerIndex_obj k m.unop).some

/-- **The Yoneda embedding of semi-representable objects preserves the products that the
refinement of [Stacks, Tag 01GJ] is built from.** -/
instance preservesLimitsOfShape_discrete_yonedaFormal (k : ℕ) (m : SimplexCategoryᵒᵖ) :
    PreservesLimitsOfShape (Discrete ((simplexPowerIndex.{max w u v} k).obj m.unop))
      (yonedaFormal.{w} (C := C)) :=
  preservesLimitsOfShape_discrete_mapFormalCoproduct overYoneda.{w}

/-- **The Yoneda embedding into the slice over the final presheaf preserves fibre products**:
Yoneda preserves every limit, and the slice over a terminal object is an equivalence. -/
instance preservesLimitsOfShape_walkingCospan_overYoneda :
    PreservesLimitsOfShape WalkingCospan (overYoneda.{w} (C := C)) := by
  have : PreservesLimitsOfShape WalkingCospan (uliftYoneda.{max w u} (C := C)) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (Over.equivalenceOfIsTerminal
        (terminalIsTerminal (C := Cᵒᵖ ⥤ Type (max w u v)))).inverse := inferInstance
  exact comp_preservesLimitsOfShape _ _

/-- **The Yoneda embedding of semi-representable objects preserves the degreewise fibre products
that the refinement of [Stacks, Tag 01GJ] is built from.** -/
instance preservesLimitsOfShape_walkingCospan_yonedaFormal :
    PreservesLimitsOfShape WalkingCospan (yonedaFormal.{w} (C := C)) :=
  preservesLimitsOfShape_walkingCospan_mapFormalCoproduct overYoneda.{w}

section Refinement

variable (J : Pretopology C) (H : HypercoveringOfTerminal.{max w u v} J) (k : ℕ)
  {Z : FormalCoproduct.{max w u v} C}
  (u : Z ⟶ H.toSimplicialObject.obj (op (SimplexCategory.mk k)))

/-- **The refinement of a hypercovering of the final presheaf by a covering in one degree**: the
refinement of [Stacks, Tag 01GJ] formed in `SR(C)` rather than in a slice. -/
noncomputable abbrev terminalRefinement : SimplicialObject (FormalCoproduct.{max w u v} C) :=
  refinementByCovering.{max w u v} H.toSimplicialObject k u

/-- The refinement formed upstairs, in the semi-representable objects over the final presheaf,
where [Stacks, Tag 01GJ] is available. -/
noncomputable abbrev terminalRefinementOver :
    SimplicialObject (FormalCoproduct.{max w u v} (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))) :=
  refinementByCovering.{max w u v} (H.toSimplicialObject ⋙ yonedaFormal) k (yonedaFormal.map u)

/-- The refinement formed in `SR(C)` is carried to the refinement formed upstairs. -/
noncomputable def terminalRefinementCompIso :
    terminalRefinement.{w} J H k u ⋙ yonedaFormal ≅ terminalRefinementOver.{w} J H k u :=
  refinementByCoveringCompIso.{max w u v} yonedaFormal H.toSimplicialObject k u

omit [HasBinaryProducts C] in
/-- The refinement formed upstairs is a hypercovering for `localPretopology`, by
[Stacks, Tag 01GJ]. -/
theorem isHypercovering_terminalRefinementOver
    [Precoverage.IsStableUnderComposition J.toPrecoverage] (hu : IsCovering J u) :
    IsHypercovering (localPretopology.{v, u, max w u v} J)
      (terminalRefinementOver.{w} J H k u) := by
  apply isHypercovering_refinementByCovering (H.toSimplicialObject ⋙ yonedaFormal) k
    (yonedaFormal.map u) (localPretopology.{v, u, max w u v} J)
  · exact isHypercovering_yonedaFormal J H
  · exact isCoveringOver_yonedaFormal_map J u hu

/-- **[Stacks, Tag 01GJ] for a hypercovering of the final presheaf.** A covering of the term in
any fixed degree of a hypercovering of the final presheaf can be refined by a morphism from
another hypercovering of the final presheaf, whose component in that degree factors through the
covering. -/
@[sga "4 V 7.3.2" "2)"]
theorem exists_hypercoveringOfTerminal_map_factoring_through_covering
    [Precoverage.IsStableUnderComposition J.toPrecoverage] (hu : IsCovering J u) :
    ∃ H' : HypercoveringOfTerminal.{max w u v} J,
      H'.toSimplicialObject = terminalRefinement.{w} J H k u ∧
        ∃ (f : terminalRefinement.{w} J H k u ⟶ H.toSimplicialObject)
          (g : (terminalRefinement.{w} J H k u).obj (op (SimplexCategory.mk k)) ⟶ Z),
          g ≫ u = f.app (op (SimplexCategory.mk k)) := by
  obtain ⟨H', hH'⟩ := hypercoveringOfTerminal_lift J (terminalRefinement.{w} J H k u)
    (terminalRefinementOver.{w} J H k u) (terminalRefinementCompIso.{w} J H k u)
    (isHypercovering_terminalRefinementOver.{w} J H k u hu)
  exact ⟨H', hH', refinementByCoveringMap.{max w u v} H.toSimplicialObject k u,
    refinementByCoveringFactor.{max w u v} H.toSimplicialObject k u,
    refinementByCoveringFactor_comp.{max w u v} H.toSimplicialObject k u⟩

end Refinement

end Stacks.CategoryTheory.Hypercovering

end
