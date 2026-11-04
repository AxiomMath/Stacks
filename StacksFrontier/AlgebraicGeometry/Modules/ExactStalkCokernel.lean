module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Modules.ExactStalkSurjective

/-!
# The cokernel of a stalk map of a short exact complex of modules

For a short complex `S` of `𝒪_X`-modules which is exact at its middle term and whose last
arrow is an epimorphism, the quotient of the stalk of `S.X₂` by the image of the stalk map of
`S.f` is the stalk of `S.X₃`.

## Main results

* `Stacks.SheafOfModules.surjective_stalkHom_of_epi`: **an epimorphism of `𝒪_X`-modules is
  surjective on every stalk**, in the `stalkHom` spelling.
* `Stacks.SheafOfModules.range_stalkHom_eq_ker`: the image of the stalk map of `S.f` is the
  kernel of the stalk map of `S.g`.
* `Stacks.SheafOfModules.quotientRangeStalkHomEquiv`: **the cokernel of the stalk map of
  `S.f` is the stalk of `S.X₃`.**

## Implementation notes

Exactness on stalks is `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`
(Tag 01AG) and epimorphy on stalks is
`AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap`; in both cases
`stalkFunctor_map_apply` identifies the underlying map with `stalkHom`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-- **An epimorphism of `𝒪_X`-modules is surjective on every stalk.** -/
public theorem surjective_stalkHom_of_epi {F G : X.Modules} (f : F ⟶ G) [Epi f] (x : X) :
    Function.Surjective (stalkHom f x) := by
  intro n
  have hepi : @Epi (_root_.SheafOfModules.{u} (structureSheaf X.sheaf)) _ F G f := ‹Epi f›
  obtain ⟨m, hm⟩ := (_root_.AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := structureSheaf X.sheaf) f).1 hepi x n
  exact ⟨m, (stalkFunctor_map_apply f x m).symm.trans hm⟩

/-- For a complex of `𝒪_X`-modules exact at its middle term, the image of the stalk map of
`S.f` is the kernel of the stalk map of `S.g`. -/
public theorem range_stalkHom_eq_ker {S : ShortComplex X.Modules} (hS : S.Exact) (x : X) :
    LinearMap.range (stalkHom S.f x) = LinearMap.ker (stalkHom S.g x) := by
  have hab := ((_root_.AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheaf X.sheaf) S).mp hS x).ab_range_eq_ker
  have hf := stalkFunctor_map_apply S.f x
  have hg := stalkFunctor_map_apply S.g x
  refine Submodule.ext fun m => ⟨?_, fun h => ?_⟩
  · rintro ⟨a, rfl⟩
    exact (hg _).symm.trans ((SetLike.ext_iff.1 hab _).1 ⟨a, hf a⟩)
  · obtain ⟨a, ha⟩ := (SetLike.ext_iff.1 hab m).2 ((hg m).trans h)
    exact ⟨a, (hf a).symm.trans ha⟩

/-- **The cokernel of the stalk map of `S.f` is the stalk of `S.X₃`**, for a complex `S` of
`𝒪_X`-modules exact at its middle term whose last arrow is an epimorphism. -/
public noncomputable def quotientRangeStalkHomEquiv {S : ShortComplex X.Modules} (hS : S.Exact)
    [Epi S.g] (x : X) :
    (modStalk S.X₂ x ⧸ LinearMap.range (stalkHom S.f x)) ≃ₗ[ringStalk X.sheaf x]
      modStalk S.X₃ x :=
  (Submodule.quotEquivOfEq _ _ (range_stalkHom_eq_ker hS x)).trans
    ((stalkHom S.g x).quotKerEquivOfSurjective (surjective_stalkHom_of_epi S.g x))

end Stacks.SheafOfModules

end
