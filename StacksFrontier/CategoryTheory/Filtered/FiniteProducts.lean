module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits and finite products of sets (Stacks 09WQ)

Part (1) of Stacks 09WQ isolates what survives of "colimits commute with finite
products of sets" when filteredness is weakened to the bare pairwise-cocone
condition: the canonical comparison
`colim (M ⨯ N) ⟶ colim M ⨯ colim N` is still *surjective*, though no longer
injective.

The comparison is Mathlib's `Limits.prodComparison` at the colimit functor
`colim : (I ⥤ Type v) ⥤ Type v`, and the product `M ⨯ N` is the categorical binary
product in the functor category, which `CategoryTheory.FunctorToTypes` identifies
with the pointwise product. The hypothesis is the amalgamation condition
`∀ x y, ∃ z, (x ⟶ z) × (y ⟶ z)` alone — exactly the shape of Mathlib's
`IsFilteredOrEmpty.cocone_objs`, and strictly weaker than `IsFiltered I`, which is
why Mathlib's `isIso_colimitPointwiseProductToProductColimit` does not apply.

Part (2) of the tag, that injectivity genuinely fails, is
`exists_not_injective_prodComparison_colim` in
`StacksFrontier.CategoryTheory.Filtered.FiniteProductsNotInjective`, where both parts are
combined as `colim_prod_surjective_and_not_injective`.

The instance hypothesis `HasColimitsOfShape I (Type v)` is what makes `colim` a
functor and hence `prodComparison` expressible; it is automatic for a small index
category.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable {I : Type u} [Category.{v} I]

/-- **Stacks 09WQ (1).** If every pair of objects of `I` admits a common upper bound,
then for all set-valued diagrams `M, N : I ⥤ Type v` the canonical comparison
`colim (M ⨯ N) ⟶ colim M ⨯ colim N` is surjective.

Given a pair of elements, choose representatives at indices `i` and `j`, push both
along arrows into a common `k`, and pair them there; the resulting element of
`colim (M ⨯ N)` maps to the original pair. -/
@[stacks 09WQ "(1)"]
theorem surjective_prodComparison_colim [HasColimitsOfShape I (Type v)]
    (h : ∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True)
    (M N : I ⥤ Type v) :
    Function.Surjective (prodComparison (colim : (I ⥤ Type v) ⥤ Type v) M N) := by
  intro p
  obtain ⟨i, m, hm⟩ := Types.jointly_surjective' (F := M)
    ((Limits.prod.fst : colim.obj M ⨯ colim.obj N ⟶ colim.obj M) p)
  obtain ⟨j, n, hn⟩ := Types.jointly_surjective' (F := N)
    ((Limits.prod.snd : colim.obj M ⨯ colim.obj N ⟶ colim.obj N) p)
  obtain ⟨k, f, g, -⟩ := h i j
  set w : (M ⨯ N).obj k := FunctorToTypes.prodMk (M.map f m) (N.map g n) with hw
  have key : ∀ {P : I ⥤ Type v} (f : M ⨯ N ⟶ P)
      (g : colim.obj M ⨯ colim.obj N ⟶ colim.obj P),
      prodComparison (colim : (I ⥤ Type v) ⥤ Type v) M N ≫ g = colim.map f →
      g (prodComparison (colim : (I ⥤ Type v) ⥤ Type v) M N (colimit.ι (M ⨯ N) k w))
        = colimit.ι P k (f.app k w) := by
    intro P f g hfg
    have e1 := ConcreteCategory.congr_hom hfg (colimit.ι (M ⨯ N) k w)
    have e2 := ConcreteCategory.congr_hom (ι_colimMap f k) w
    simp only [ConcreteCategory.comp_apply, colim_map] at e1 e2
    exact e1.trans e2
  refine ⟨colimit.ι (M ⨯ N) k w, ?_⟩
  apply (Types.binaryProductIso (colim.obj M) (colim.obj N)).toEquiv.injective
  simp only [Iso.toEquiv_fun]
  refine Prod.ext ?_ ?_
  · simp only [Types.binaryProductIso_hom_comp_fst_apply]
    rw [key _ _ (prodComparison_fst _ _ _), hw, FunctorToTypes.prodMk_fst, colimit.w_apply, hm]
  · simp only [Types.binaryProductIso_hom_comp_snd_apply]
    rw [key _ _ (prodComparison_snd _ _ _), hw, FunctorToTypes.prodMk_snd, colimit.w_apply, hn]

end CategoryTheory.Limits
