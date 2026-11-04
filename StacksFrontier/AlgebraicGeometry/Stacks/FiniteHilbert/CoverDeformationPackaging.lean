module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertCoverDeformationRepresentable

/-!
# Packaging a deformation of schemes as a solution of the cover deformation problem

`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` asks, for a first-order thickening
`i : U ⟶ U'`, an algebraic space `X'` over `U'`, a degree-`d` finite locally free cover
`q : Z ⟶ U` and a morphism `f` from `Z` to the special fibre of `X'`, for a degree-`d` finite
locally free `q' : Z' ⟶ U'` with `Z = U ×_{U'} Z'` and a morphism `Z' ⟶ X'` restricting to `f`.

The proof of **Stacks 06D8** produces the cover as a closed subscheme `Z'` of the ambient of a
thickening `j : Z ⟶ W` of `Z` over `U'`, where `y : W ⟶ X'` is a morphism from an object of the
big fppf site of `U'` extending the point `x : Z ⟶ X'` named by `f`. This file reads that output
back as a solution of the deformation problem, for an arbitrary presheaf `X'`; the morphism
`Z' ⟶ X'` is the composite `Z' ⟶ W ⟶ X'`.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_schemeDeformation`: the
  packaging.

## Implementation notes

The cover is finite over `U'`, so
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact` puts it in the site.
`AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_siteDeformation` then
produces the cover and a morphism `Z' ⟶ W` in the site, with `T = Z` and `κ = j`. The
remaining identification, that the comparison of `j` followed by the restriction of `y` is `f`, is
`CategoryTheory.OverShriek.restrictYonedaHom_comp_relocalizeRestrict_map` read through the Yoneda
equivalence.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06D9](https://stacks.math.columbia.edu/tag/06D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack.FiniteHilbert

/-- **A deformation of the underlying schemes through an extension of the point solves the cover
deformation problem.** Take the data of
`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations`: a morphism `i : U ⟶ U'` of the big
fppf site of `S`, a presheaf `X'` on the big fppf site of `U'`, a cover `q : Z ⟶ U` and a morphism
`f` from `Z` to the restriction of `X'`. Suppose further:

* `j : Z ⟶ W` is a morphism of the big fppf site of `U'`, and `y : W ⟶ X'` extends the point of
  `X'` that `f` names (`hjy`);
* `Z'` is a scheme with `iZ : Z ⟶ Z'` and `k : Z' ⟶ W`, factoring `j` (`hk`);
* the composite `Z' ⟶ W ⟶ U'` is finite locally free of degree `d` (`hflf`);
* the square `Z = U ×_{U'} Z'` is cartesian (`hpb`).

Then `Z'` is a solution of the deformation problem: it is an object of the site, finite locally
free of degree `d` over `U'`, and it presents `Z` as `U ×_{U'} Z'`. The morphism `Z' ⟶ W ⟶ X'`
restricts to `f`.

This generalizes `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_siteDeformation`
from a representable presheaf to an arbitrary one. -/
theorem exists_coverDeformation_of_schemeDeformation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (X' : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)
    {Z : BigFppfOver B S hS} (q : Z ⟶ U)
    (f : yoneda.obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
      (OverShriek.relocalizeRestrict i.left).obj X')
    {W : BigFppfOver B U'.left.1 U'.left.2}
    (j : (Over.map i.left).obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶ W)
    (y : yoneda.obj W ⟶ X')
    (hjy : yoneda.map j ≫ y = (yonedaEquiv (F := X')).symm
      ((yonedaEquiv (F := (OverShriek.relocalizeRestrict i.left).obj X')) f))
    {Z' : Scheme.{u}}
    (iZ : (BigFppfOver.toScheme B S hS).obj Z ⟶ Z')
    (k : Z' ⟶ (BigFppfOver.toScheme B U'.left.1 U'.left.2).obj W)
    (hk : iZ ≫ k = (BigFppfOver.toScheme B U'.left.1 U'.left.2).map j)
    (hflf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (k ≫ B.inclusion.map W.hom) d)
    (hpb : IsPullback iZ ((BigFppfOver.toScheme B S hS).map q) (k ≫ B.inclusion.map W.hom)
      ((BigFppfOver.toScheme B S hS).map i)) :
    ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U') (g : Z ⟶ Z') (hg : IsPullback g q q' i),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q') d ∧
        ∃ f' : yoneda.obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) ⟶ X',
          OverShriek.restrictYonedaHom i.left (coverComparisonOfSquare hg.w) ≫
              (OverShriek.relocalizeRestrict i.left).map f' = f := by
  -- The cover is finite over `U'`, so it belongs to the site.
  have := hflf
  have : Stacks.Morphisms.IsFiniteLocallyFree (k ≫ B.inclusion.map W.hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  have : IsFinite (k ≫ B.inclusion.map W.hom) :=
    Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
  obtain ⟨Z'', q', g, hg, hrank, f'₀, hf'₀⟩ :=
    exists_coverDeformation_of_siteDeformation B S hS d i q j (𝟙 _)
      (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (k ≫ B.inclusion.map W.hom)
        U'.left.2) iZ (k ≫ B.inclusion.map W.hom) k hflf hpb
      (by rw [Over.id_left, B.inclusion.map_id, Category.id_comp]; exact hk) rfl
  refine ⟨Z'', q', g, hg, hrank, f'₀ ≫ y, ?_⟩
  -- The comparison of `j` followed by the restriction of `y` is `f`.
  have hs : yonedaEquiv f = X'.map j.op (yonedaEquiv y) := by
    rw [yonedaEquiv_naturality, hjy, Equiv.apply_symm_apply]
  have hf := OverShriek.restrictYonedaHom_comp_relocalizeRestrict_map i.left j X'
    (yonedaEquiv y) (yonedaEquiv f) hs
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hf
  rw [Functor.map_comp, ← Category.assoc, hf'₀, CategoryTheory.Functor.map_id, Category.id_comp,
    hf]

end AlgebraicGeometry.Stack.FiniteHilbert

end
