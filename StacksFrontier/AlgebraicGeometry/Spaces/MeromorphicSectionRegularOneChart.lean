module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularLocal

/-!
# Injectivity of multiplication by a meromorphic section is local at a single chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `s` be a
meromorphic section of a sheaf of `𝒪_F`-modules `L`. If multiplication by `s` is injective on
meromorphic functions over each member of a covering family of an étale scheme chart `V` of `F`,
then it is injective on meromorphic functions over `V`.

## Main results

* `AlgebraicGeometry.Space.injective_smul_eval_of_cover`: multiplication by a meromorphic section
  is injective over a chart as soon as it is injective over the members of a covering family of
  that chart.

## References

* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
-/

@[expose] public section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Multiplication by a meromorphic section `s` is injective on the meromorphic functions over
an étale scheme chart `V` as soon as it is injective over the members of a covering family of
`V`. -/
theorem injective_smul_eval_of_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (V : SmallEtale B S hS F) {I : Type w} (W : I → SmallEtale B S hS F)
    (a : ∀ i, W i ⟶ V)
    (hcov : Sieve.ofArrows W a ∈ SmallEtale.topology B S hS F V)
    (hinj : ∀ i, Function.Injective fun r :
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op (W i)) ↦
      r • s.eval (op (W i))) :
    Function.Injective fun r :
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      r • s.eval (op V) := by
  intro r r' hr
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
    (meromorphicRingedSite B S hS F hF).O).property.isSeparated V _ hcov r r' ?_
  rintro Z g ⟨Z', p, q, ⟨i⟩, rfl⟩
  have hi := hinj i (((meromorphicSectionSheaf_map_smul_eval B S hS F hF L s (a i) r).symm.trans
    (congrArg ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map (a i).op) hr)).trans
    (meromorphicSectionSheaf_map_smul_eval B S hS F hF L s (a i) r'))
  simp only [op_comp, Functor.map_comp, RingCat.comp_apply, hi]

end AlgebraicGeometry.Space

end
