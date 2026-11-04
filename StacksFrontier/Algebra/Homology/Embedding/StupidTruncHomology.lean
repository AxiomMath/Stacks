module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of the inclusion of a stupid truncation

`HomologicalComplex.ιStupidTrunc` is the inclusion `σ^{≥a}K ⟶ K` of the stupid truncation of a
complex along a truncation embedding onto a final segment. For cochain complexes indexed by `ℤ`
and the embeddings `ComplexShape.embeddingUpIntGE a` it is an isomorphism in every degree at
least `a` and zero below, so on cohomology it is an isomorphism in the degrees above `a` and
surjective in degree `a`.

## Main results

* `HomologicalComplex.isIso_homologyMap_of_isIso_f` and
  `HomologicalComplex.epi_homologyMap_of_isIso_f`: cohomology in degree `i` of a morphism of
  homological complexes is an isomorphism when the morphism is an isomorphism in the three
  degrees `c.prev i`, `i`, `c.next i`, and surjective already when it is an isomorphism in the
  two degrees `i` and `c.next i`.
* `HomologicalComplex.isZero_X_stupidTrunc_embeddingUpIntGE`: the stupid truncation in degrees
  `≥ a` vanishes below `a`.
* `HomologicalComplex.isIso_homologyMap_ιStupidTrunc_embeddingUpIntGE` and
  `HomologicalComplex.epi_homologyMap_ιStupidTrunc_embeddingUpIntGE`: the inclusion of the
  stupid truncation in degrees `≥ a` is an isomorphism on cohomology above `a` and surjective
  on cohomology in degree `a`.

## References

* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Tag 08C8](https://stacks.math.columbia.edu/tag/08C8)
-/

@[expose] public noncomputable section

open CategoryTheory Category CategoryTheory.Limits

namespace HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C]

section General

variable [Abelian C] {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- The degree-`i` cohomology of a morphism of homological complexes is an isomorphism as soon as
the morphism is an isomorphism in the degrees `c.prev i`, `i` and `c.next i`. -/
theorem isIso_homologyMap_of_isIso_f (φ : K ⟶ L) (i : ι)
    (h₁ : IsIso (φ.f (c.prev i))) (h₂ : IsIso (φ.f i)) (h₃ : IsIso (φ.f (c.next i))) :
    IsIso (homologyMap φ i) :=
  have := h₁; have := h₃
  ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' ((shortComplexFunctor C c i).map φ)
    (inferInstanceAs (Epi (φ.f (c.prev i)))) h₂ (inferInstanceAs (Mono (φ.f (c.next i))))

/-- The degree-`i` cohomology of a morphism of homological complexes is an epimorphism as soon as
the morphism is an isomorphism in the degrees `i` and `c.next i`. -/
theorem epi_homologyMap_of_isIso_f (φ : K ⟶ L) (i : ι)
    (h₂ : IsIso (φ.f i)) (h₃ : IsIso (φ.f (c.next i))) :
    Epi (homologyMap φ i) := by
  have := h₃
  have : IsIso ((shortComplexFunctor C c i).map φ).τ₂ := h₂
  have : Mono ((shortComplexFunctor C c i).map φ).τ₃ :=
    inferInstanceAs (Mono (φ.f (c.next i)))
  have : IsIso (ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)) :=
    ShortComplex.isIso_cyclesMap_of_isIso_of_mono _
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap _

end General

section Truncation

variable [HasZeroMorphisms C] [HasZeroObject C] (K : CochainComplex C ℤ) (a : ℤ)

/-- The stupid truncation in degrees `≥ a` has no terms below `a`. -/
@[sga "4 XVII 1.1.16" "partial"]
theorem isZero_X_stupidTrunc_embeddingUpIntGE (n : ℤ) (hn : n < a) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X n) := by
  refine K.isZero_stupidTrunc_X _ n fun i ↦ ?_
  rw [ComplexShape.embeddingUpIntGE_f]
  omega

/-- The inclusion of the stupid truncation in degrees `≥ a` is an isomorphism in every degree at
least `a`. -/
theorem isIso_ιStupidTrunc_embeddingUpIntGE_f (n : ℤ) (hn : a ≤ n) :
    IsIso ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f n) :=
  K.isIso_ιStupidTrunc_f _ (i := (n - a).toNat) (by
    rw [ComplexShape.embeddingUpIntGE_f, Int.toNat_of_nonneg (by omega)]; omega)

end Truncation

section TruncationHomology

variable [Abelian C] (K : CochainComplex C ℤ) (a : ℤ)

/-- The inclusion of the stupid truncation in degrees `≥ a` is an isomorphism in the degree
following any `n` with `a ≤ n + 1`. -/
private theorem isIso_ιStupidTrunc_embeddingUpIntGE_f_next (n : ℤ) (hn : a ≤ n + 1) :
    IsIso ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f ((ComplexShape.up ℤ).next n)) := by
  rw [CochainComplex.next]
  exact K.isIso_ιStupidTrunc_embeddingUpIntGE_f a _ hn

/-- The inclusion of the stupid truncation in degrees `≥ a` is an isomorphism on cohomology above
`a`. -/
theorem isIso_homologyMap_ιStupidTrunc_embeddingUpIntGE (j : ℤ) (hj : a < j) :
    IsIso (homologyMap (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)) j) :=
  isIso_homologyMap_of_isIso_f _ j
    (by
      rw [CochainComplex.prev]
      exact K.isIso_ιStupidTrunc_embeddingUpIntGE_f a (j - 1) (by omega))
    (K.isIso_ιStupidTrunc_embeddingUpIntGE_f a j hj.le)
    (K.isIso_ιStupidTrunc_embeddingUpIntGE_f_next a j (by omega))

/-- The inclusion of the stupid truncation in degrees `≥ a` is surjective on cohomology in degree
`a`. -/
theorem epi_homologyMap_ιStupidTrunc_embeddingUpIntGE :
    Epi (homologyMap (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)) a) :=
  epi_homologyMap_of_isIso_f _ a (K.isIso_ιStupidTrunc_embeddingUpIntGE_f a a le_rfl) 
    (K.isIso_ιStupidTrunc_embeddingUpIntGE_f_next a a (by omega))

end TruncationHomology

end HomologicalComplex

end
