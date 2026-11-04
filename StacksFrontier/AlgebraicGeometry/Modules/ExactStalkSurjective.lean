module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# A stalk map is surjective where the next stalk vanishes

For a complex of `𝒪_X`-modules exact at its middle term, the stalk map of its first arrow is
surjective at every point where the stalk of its last term vanishes.

## Main results

* `Stacks.SheafOfModules.surjective_stalkHom_of_forall_modStalk_eq_zero`: **the stalk map of
  `S.f` is surjective at a point where the stalk of `S.X₃` is zero.**

## Implementation notes

Exactness on stalks is `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`
(Tag 01AG), which is stated for the abelian-group stalk functor; `stalkFunctor_map_apply`
identifies the underlying map of that functor with `stalkHom`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-- **The stalk map of `S.f` is surjective wherever the stalk of `S.X₃` vanishes**, for a
complex `S` of `𝒪_X`-modules exact at its middle term. -/
public theorem surjective_stalkHom_of_forall_modStalk_eq_zero {S : ShortComplex X.Modules}
    (hS : S.Exact) {x : X} (h3 : ∀ a : modStalk S.X₃ x, a = 0) :
    Function.Surjective (stalkHom S.f x) := by
  have hSx := (_root_.AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheaf X.sheaf) S).mp hS x
  have hz : Limits.IsZero ((_root_.AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor
      (structureSheaf X.sheaf) x).obj S.X₃) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => (h3 a).trans (h3 b).symm⟩
  have hg : (_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
      (structureSheaf X.sheaf) S x).g = 0 := hz.eq_of_tgt _ _
  have hepi : Epi (_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
      (structureSheaf X.sheaf) S x).f :=
    ((_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
      (structureSheaf X.sheaf) S x).exact_iff_epi hg).1 hSx
  intro n
  obtain ⟨m, hm⟩ := (AddCommGrpCat.epi_iff_surjective
    (_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
      (structureSheaf X.sheaf) S x).f).1 hepi n
  exact ⟨m, (stalkFunctor_map_apply S.f x m).symm.trans hm⟩

end Stacks.SheafOfModules

end
