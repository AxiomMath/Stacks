module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekFreeYoneda
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceFreeAbelianLowerShriekNaturalityOfEq
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceShriekRestrictionTransitionCompIso

/-!
# Stacks 0D87 part (2) at `ℤ_V^♯`, natural along a simplex map

Let `(C, J)` be a small site and `K` a simplicial object of `SR(C)`. In simplicial degree `p`,
`CategoryTheory.SimplicialSemiRepresentable.sliceFreeYonedaLowerShriekIso` identifies
`j_{p!}j_p^{-1} ℤ_V^♯` with the free abelian sheaf on `h_V × F(K_p)`. This module proves that
those identifications are natural along a simplex map `φ : m ⟶ n`, with the connecting morphism
written in the vocabulary of the simplicial development: the inverse of
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso`, followed by the
extension by zero along `j_m` of the `r_φ`-part.

This is the junction the chain behind the `hacyclic` hypothesis of Stacks 0D8G--0D8N needs: on one
side the naturality of Stacks 0D87 part (2) in the semi-representable object, which is proved at
the componentwise localized topologies, and on the other the composition comparison of the
extensions by zero of the simplicial degrees, which is stated at
`CategoryTheory.SimplicialSiteSituation.componentTopology`. The two meet here.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.sliceAbelianLowerShriekCompIso_comp_sliceFreeYonedaLowerShriekIso`: **the identifications
  `j_{p!}j_p^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` are natural along a simplex map.**

## Implementation notes

Both halves are transports of results stated at `componentwiseTopology`, and the two transports
are different in kind. `CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIsoOfEq` leaves the two
topologies as variables and takes their equality with the componentwise ones as hypotheses, so it
is instantiated by `CategoryTheory.SimplicialSemiRepresentable.componentTopology_eq` and nothing
else. `CategoryTheory.SimplicialSemiRepresentable`
`.shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso` cannot be reached that way,
because at that generality the statement can no longer mention `sliceAbelianLowerShriekCompIso`,
which is pinned at the component topology; it is stated at the component topology directly, which
is possible only through the instance device described in its own module.

That device does not leak into the statement here. Every object it names belongs to the simplicial
vocabulary, whose sites are spelled `(situation J K).component p` throughout, so the instances it
needs are the registered ones; `shriekRestrictionTransition`, the one object whose signature
spells those sites as `ComponentOver (K.obj (op p))` instead, occurs only inside the proof.

The statement lives in its own module: `SliceAbelianLowerShriekFreeYoneda` and the `...OfEq` module
put enough extra instances in scope to lengthen the `isDefEq` checks of the modules they are
imported into.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]
  [J.WEqualsLocallyBijective (Type u)]

/-- **The identifications `j_{p!}j_p^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` are natural along a simplex
map.** For `φ : m ⟶ n` the connecting morphism `j_{n!}j_n^{-1} ℤ_V^♯ ⟶ j_{m!}j_m^{-1} ℤ_V^♯` --
the inverse of `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso` at
`j_n^{-1}ℤ_V^♯`, then the extension by zero along `j_m` of the reindexing and the counit of
`r_{φ!} ⊣ r_φ^{-1}` -- is carried by the two identifications of
`CategoryTheory.SimplicialSemiRepresentable.sliceFreeYonedaLowerShriekIso` to the free abelian
sheaf of `h_V × F(K_φ)`.

This is `CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIsoOfEq` instantiated at the
component topologies through `CategoryTheory.SimplicialSemiRepresentable.componentTopology_eq`,
with the shriek restriction transition rewritten into the simplicial vocabulary by
`CategoryTheory.SimplicialSemiRepresentable`
`.shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso`. -/
theorem sliceAbelianLowerShriekCompIso_comp_sliceFreeYonedaLowerShriekIso
    {m n : SimplexCategory} (φ : m ⟶ n) (V : C) :
    ((sliceAbelianLowerShriekCompIso J K φ).inv.app
            (((sliceForget K (op n)).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).componentTopology n) J).obj
              (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
          (sliceAbelianLowerShriek J K m).map
            ((transitionAbelianLowerShriek J K φ).map
                ((sliceAbelianRestrictionCompIso J K φ).inv.app
                  (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
              (transitionAbelianLowerShriekAdjunction J K φ).counit.app
                (((sliceForget K (op m)).sheafPushforwardContinuous AddCommGrpCat.{u}
                  ((situation J K).componentTopology m) J).obj
                  (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) ≫
        (sliceFreeYonedaLowerShriekIso J K m V).hom =
      (sliceFreeYonedaLowerShriekIso J K n V).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (Limits.prod.map (𝟙 (yoneda.obj V))
            ((FormalCoproduct.yoneda (C := C)).map (K.map φ.op))) AddCommGrpCat.free) := by
  have := hasWeakSheafifyComponentOver (L := K.obj (op n))
    ((situation J K).componentTopology n)
  have := hasWeakSheafifyComponentOver (L := K.obj (op m))
    ((situation J K).componentTopology m)
  have : (componentOverForget (K.obj (op n))).IsContinuous
      ((situation J K).componentTopology n) J := sliceForget_isContinuous J K n
  have : (componentOverForget (K.obj (op m))).IsContinuous
      ((situation J K).componentTopology m) J := sliceForget_isContinuous J K m
  refine Eq.trans (eq_whisker (shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso
    J K φ (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)).symm _) ?_
  exact shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIsoOfEq J
    (K.map φ.op) (componentTopology_eq J K n) (componentTopology_eq J K m) V

end CategoryTheory.SimplicialSemiRepresentable

end
