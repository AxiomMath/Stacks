module

public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementDeltaFunctor

/-!
# Left derived functors as a homological δ-functor

The left derived functors `Lₙ F` of an additive functor `F` out of an abelian category with
enough projectives, with their connecting morphisms `CategoryTheory.Functor.leftDerivedδ`, form a
`Stacks.CategoryHomology.HomologicalDeltaFunctor`, the homological counterpart of the
δ-functors of Stacks 010Q.

## Main definitions

* `CategoryTheory.Functor.leftDerivedHomologicalDeltaFunctor`: the family `Lₙ F` with its
  connecting morphisms, as a homological δ-functor.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u v₂ u₂

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **The left derived functors of an additive functor form a homological δ-functor.**
The degree-`n` functor is `F.leftDerived n`, the connecting morphism is
`CategoryTheory.Functor.leftDerivedδ`. -/
def leftDerivedHomologicalDeltaFunctor (F : C ⥤ D) [F.Additive] :
    Stacks.CategoryHomology.HomologicalDeltaFunctor C D where
  functor n := F.leftDerived n
  δ hS n := F.leftDerivedδ hS n
  map_g_δ hS n := F.leftDerived_map_g_comp_δ hS n
  δ_map_f hS n := F.leftDerivedδ_comp_map_f hS n
  epi_map_g hS := F.epi_leftDerivedZero_map_g hS
  exact_map hS n := F.leftDerived_exact hS n
  exact_δ₁ hS n := F.leftDerived_exact_δ₁ hS n
  exact_δ₂ hS n := F.leftDerived_exact_δ₂ hS n
  δ_naturality hS hT φ n := F.leftDerivedδ_naturality hS hT φ n

/-- The degree-`n` functor of `leftDerivedHomologicalDeltaFunctor` is `F.leftDerived n`.
Not a `simp` lemma: it rewrites a whole functor, which can leave a later goal no longer
type-correct at `implicit` transparency. -/
lemma leftDerivedHomologicalDeltaFunctor_functor (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerivedHomologicalDeltaFunctor).functor n = F.leftDerived n := rfl

/-- The connecting morphism of `leftDerivedHomologicalDeltaFunctor` is
`CategoryTheory.Functor.leftDerivedδ`. Not a `simp` lemma, for the reason given at
`leftDerivedHomologicalDeltaFunctor_functor`. -/
lemma leftDerivedHomologicalDeltaFunctor_δ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (F.leftDerivedHomologicalDeltaFunctor).δ hS n = F.leftDerivedδ hS n := rfl

end CategoryTheory.Functor

end
