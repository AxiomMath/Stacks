module

public import StacksFrontier.CategoryTheory.Sites.Continuous.FreeAbelianLowerShriekComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekTransition

/-!
# The simplicial composition comparison of extensions by zero is `lowerShriekComp`

Let `(C, J)` be a small site and `K` a simplicial object of `SR(C)`. For a simplex map
`φ : m ⟶ n` the comparison
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso`
is an isomorphism `r_{φ!} j_{m!} ≅ j_{n!}` of extensions by zero on abelian sheaves, built by
uniqueness of a left adjoint from the comparison
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianRestrictionCompIso` of the restrictions.

`CategoryTheory.Functor.lowerShriekComp` is the same comparison for an arbitrary triple of
continuous site functors, in the opposite direction and built by the same uniqueness from the
same comparison of restrictions. The two are inverse to each other.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso_eq_lowerShriekComp`:
  the identification.
* `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso_hom`: its `hom`
  form.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.componentLowerShriekCompAugmentationAbelianIso_transition_lowerShriekComp`:
  `CategoryTheory.SimplicialSemiRepresentable`
  `.componentLowerShriekCompAugmentationAbelianIso_transition` restated with the inverse of
  `CategoryTheory.Functor.lowerShriekComp` in place of the simplicial comparison.

## Implementation notes

No instance of continuity for `j_m` and `j_n` is registered at the spelling
`(situation J K).component p` of their source — see
`CategoryTheory.SimplicialSemiRepresentable.sliceForget_isContinuous_component` — so the two
have to be supplied by hand, in the statements as well as in the proofs.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The simplicial composition comparison of extensions by zero is the general one.** For a
simplex map `φ : m ⟶ n` the comparison `r_{φ!} j_{m!} ≅ j_{n!}` of
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso` is the inverse of
`CategoryTheory.Functor.lowerShriekComp` read at the three site functors `r_φ`, `j_m`, `j_n` and
the equality `r_φ ⋙ j_m = j_n`. -/
theorem sliceAbelianLowerShriekCompIso_eq_lowerShriekComp {m n : SimplexCategory} (φ : m ⟶ n) :
    haveI := sliceForget_isContinuous_component J K m
    haveI := sliceForget_isContinuous_component J K n
    sliceAbelianLowerShriekCompIso J K φ =
      (Functor.lowerShriekComp ((situation J K).componentTopology n)
        ((situation J K).componentTopology m) J (componentTransitionFunctor J K φ)
        (sliceForget K (op m)) (sliceForget K (op n)) AddCommGrpCat.{u}
        (eqToIso (componentTransitionFunctor_comp_sliceForget J K φ))).symm :=
  (Adjunction.leftAdjointUniq_ofNatIsoRight_comp
    (transitionAbelianLowerShriekAdjunction J K φ) (sliceAbelianLowerShriekAdjunction J K m)
    (sliceAbelianLowerShriekAdjunction J K n) (sliceAbelianRestrictionCompIso J K φ)).symm

/-- The `hom` form of
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso_eq_lowerShriekComp`:
the forward direction `r_{φ!} j_{m!} ⟶ j_{n!}` of the simplicial comparison is the inverse of
`CategoryTheory.Functor.lowerShriekComp`. -/
theorem sliceAbelianLowerShriekCompIso_hom {m n : SimplexCategory} (φ : m ⟶ n) :
    haveI := sliceForget_isContinuous_component J K m
    haveI := sliceForget_isContinuous_component J K n
    (sliceAbelianLowerShriekCompIso J K φ).hom =
      (Functor.lowerShriekComp ((situation J K).componentTopology n)
        ((situation J K).componentTopology m) J (componentTransitionFunctor J K φ)
        (sliceForget K (op m)) (sliceForget K (op n)) AddCommGrpCat.{u}
        (eqToIso (componentTransitionFunctor_comp_sliceForget J K φ))).inv :=
  congrArg Iso.hom (sliceAbelianLowerShriekCompIso_eq_lowerShriekComp J K φ)

/-- **The compatibility of the degreewise identification `a_! g_{p!} ≅ j_{p!}` with the
simplicial structure, against the canonical spelling of the composition comparison.** This is
`CategoryTheory.SimplicialSemiRepresentable`
`.componentLowerShriekCompAugmentationAbelianIso_transition` with
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso` replaced by the
inverse of `CategoryTheory.Functor.lowerShriekComp`. -/
theorem componentLowerShriekCompAugmentationAbelianIso_transition_lowerShriekComp
    {m n : SimplexCategory} (φ : m ⟶ n) :
    haveI := sliceForget_isContinuous_component J K m
    haveI := sliceForget_isContinuous_component J K n
    Functor.isoWhiskerLeft (transitionAbelianLowerShriek J K φ)
          (componentLowerShriekCompAugmentationAbelianIso J K m) ≪≫
        (Functor.lowerShriekComp ((situation J K).componentTopology n)
          ((situation J K).componentTopology m) J (componentTransitionFunctor J K φ)
          (sliceForget K (op m)) (sliceForget K (op n)) AddCommGrpCat.{u}
          (eqToIso (componentTransitionFunctor_comp_sliceForget J K φ))).symm =
      augmentationTransitionAbelianLowerShriekIso J K φ ≪≫
        componentLowerShriekCompAugmentationAbelianIso J K n :=
  (sliceAbelianLowerShriekCompIso_eq_lowerShriekComp J K φ) ▸
    componentLowerShriekCompAugmentationAbelianIso_transition J K φ

end CategoryTheory.SimplicialSemiRepresentable

end
