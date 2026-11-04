module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Extending a complex along an embedding of shapes preserves short exactness

Let `e : c.Embedding c'` be an embedding of complex shapes and let `C` be an abelian category.
The extension functor `HomologicalComplex.extend _ e` reindexes a complex along `e` and fills the
degrees outside the image of `e.f` with zero objects, so it changes nothing degreewise except by
inserting zeros. Short exactness of a short complex of homological complexes is a degreewise
condition, and a short complex with a zero middle term is short exact; hence a short exact
sequence of complexes over `c` extends to a short exact sequence of complexes over `c'`.

## Main results

* `HomologicalComplex.extendMap_comp_extendMap`: the two extended maps of a short complex still
  compose to zero, so they form a short complex.
* `HomologicalComplex.shortExact_extend`: **extending a short complex of homological complexes
  along `e` preserves short exactness.**

## Implementation notes

Mathlib already has the functoriality of `HomologicalComplex.extendMap`
(`HomologicalComplex.extendMap_comp`, `HomologicalComplex.extendMap_zero`, and the functor
`ComplexShape.Embedding.extendFunctor`), so nothing of that kind is redeveloped here.

The proof runs through `HomologicalComplex.shortExact_of_degreewise_shortExact`, which reduces the
claim to each degree `n` of `c'`, and then splits on whether `n` is in the image of `e.f`. In a
degree `e.f i` the three canonical isomorphisms `HomologicalComplex.extendXIso` assemble into an
isomorphism of short complexes with the degree-`i` short complex of `S`, because
`HomologicalComplex.extendMap_f` describes the extended maps in that degree as the original ones
conjugated by exactly those isomorphisms; short exactness is then transported along the
isomorphism. In a degree in no image all three terms are zero objects, which gives `Mono` of the
first map, `Epi` of the second and exactness at once.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex

universe v u

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type u} [Category.{v} C] [Abelian C] (e : c.Embedding c')

/-- The extensions along `e` of the two maps of a short complex of homological complexes still
compose to zero. -/
theorem extendMap_comp_extendMap (S : ShortComplex (HomologicalComplex C c)) :
    extendMap S.f e ≫ extendMap S.g e = 0 := by
  rw [← extendMap_comp, S.zero, extendMap_zero]

/-- **Extending along an embedding of complex shapes preserves short exactness.** If `S` is a
short exact sequence of homological complexes over `c`, then the sequence of extensions along
`e : c.Embedding c'` is a short exact sequence of homological complexes over `c'`. -/
theorem shortExact_extend (S : ShortComplex (HomologicalComplex C c)) (hS : S.ShortExact) :
    (ShortComplex.mk (extendMap S.f e) (extendMap S.g e)
      (extendMap_comp_extendMap e S)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : ∃ i, e.f i = n
  · obtain ⟨i, hi⟩ := hn
    refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (S.X₁.extendXIso e hi).symm (S.X₂.extendXIso e hi).symm (S.X₃.extendXIso e hi).symm
      ?_ ?_) ((shortExact_iff_degreewise_shortExact S).1 hS i)
    · simp [extendMap_f S.f e hi]
    · simp [extendMap_f S.g e hi]
  · have hn' : ∀ i, e.f i ≠ n := fun i hi => hn ⟨i, hi⟩
    exact
      { mono_f := (S.X₁.isZero_extend_X e n hn').mono _
        epi_g := (S.X₃.isZero_extend_X e n hn').epi _
        exact := ShortComplex.exact_of_isZero_X₂ _ (S.X₂.isZero_extend_X e n hn') }

end HomologicalComplex

end
