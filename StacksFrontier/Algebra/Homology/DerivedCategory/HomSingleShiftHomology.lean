module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Morphisms out of a single object into a shifted bounded below object

Let `𝒜` be an abelian category with an unbounded derived category, let `L` be an object of `D(𝒜)`
with no cohomology below degree `j`, and let `U` be an object of `𝒜`.  Then degree-`j` cohomology
is surjective on morphisms

`Hom_{D(𝒜)}(U[0], L⟦j⟧) ⟶ Hom_𝒜(U, H^j(L))`,

so a vanishing statement about the left-hand group descends to the right-hand one.  That descent is
what this file records.

## Main results

* `DerivedCategory.eq_zero_of_forall_hom_single_shift_eq_zero` — if every morphism
  `U[0] ⟶ L⟦j⟧` is zero and `L` has no cohomology below degree `j`, then every morphism
  `U ⟶ H^j(L)` is zero.

## Implementation notes

The companion statement `DerivedCategory.bijective_homologyFromSingle_of_isGE` is the same fact in
the unshifted spelling, with `U` placed in degree `j` rather than in degree `0` and `L` unshifted.

## References

* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- **A vanishing of morphisms out of a single object into a shifted object descends to
cohomology.**  If `L` has no cohomology below degree `j` and every morphism `U[0] ⟶ L⟦j⟧` of
`D(𝒜)` is zero, then every morphism `U ⟶ H^j(L)` of `𝒜` is zero. -/
theorem eq_zero_of_forall_hom_single_shift_eq_zero (U : 𝒜) (L : DerivedCategory 𝒜) (j : ℤ)
    (hL : TStructure.t.IsGE L j)
    (hvan : ∀ φ : (singleFunctor 𝒜 0).obj U ⟶ L⟦j⟧, φ = 0)
    (s : U ⟶ (homologyFunctor 𝒜 j).obj L) : s = 0 := by
  have := hL
  obtain ⟨φ, hφ⟩ := (bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    ((singleFunctor 𝒜 0).obj U) L 0 j j j (by omega) le_rfl).surjective
    ((singleFunctorCompHomologyFunctorIso 𝒜 0).hom.app U ≫ s)
  dsimp only at hφ
  rw [hvan φ, Functor.shiftMap_zero] at hφ
  refine (cancel_epi ((singleFunctorCompHomologyFunctorIso 𝒜 0).hom.app U)).mp ?_
  rw [comp_zero]
  exact hφ.symm

end DerivedCategory

end
