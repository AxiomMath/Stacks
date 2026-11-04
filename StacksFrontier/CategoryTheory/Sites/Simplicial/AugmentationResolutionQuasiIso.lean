module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionHomAcyclic

/-!
# The resolution of Stacks 0D78 as a resolution of complexes

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`G` an abelian sheaf on `(D, K)`. Stacks 0D78 gives an exact complex

`… ⟶ g_{2!}(a_2⁻¹G) ⟶ g_{1!}(a_1⁻¹G) ⟶ g_{0!}(a_0⁻¹G) ⟶ a⁻¹G ⟶ 0`

of abelian sheaves on the total site, carried by
`CategoryTheory.SimplicialSiteSituation.Augmentation.resolution` as exactness in every positive
degree, exactness at the augmentation and epimorphy of the augmentation. This module reads those
three statements as the one statement they amount to: the augmentation is a quasi-isomorphism onto
`a⁻¹G` placed in degree zero.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionComplex`: the complex of
  Stacks 0D78, the alternating-face complex of the resolving simplicial object.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionChainAugmentation`: its
  augmentation onto `a⁻¹G` in degree zero.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.quasiIso_resolutionChainAugmentation`: the
  augmentation of Stacks 0D78 is a quasi-isomorphism.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (G : Sheaf K Ab.{u})

/-- The complex of Stacks 0D78: the alternating-face complex of the simplicial abelian sheaf
whose degree-`n` term is `g_{n!}(a_n⁻¹G)`. -/
abbrev resolutionComplex : ChainComplex (Sheaf S.totalTopology Ab.{u}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
    (resolution S D K a G).simplicial

/-- The augmentation of the complex of Stacks 0D78 onto `a⁻¹G` placed in degree zero, as a
morphism of chain complexes. -/
def resolutionChainAugmentation :
    resolutionComplex S D K a G ⟶
      (ChainComplex.single₀ (Sheaf S.totalTopology Ab.{u})).obj
        ((totalInverseImageAb S D K a).obj G) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(resolution S D K a G).augmentation, (resolution S D K a G).augmentation_comp⟩

/-- **The complex of Stacks 0D78 is a resolution of `a⁻¹G`**: its augmentation is a
quasi-isomorphism. -/
instance quasiIso_resolutionChainAugmentation :
    QuasiIso (resolutionChainAugmentation S D K a G) := by
  constructor
  intro n
  match n with
  | 0 =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨(resolution S D K a G).exact_zero, (resolution S D K a G).augmentation_epi⟩
    all_goals rfl
  | (n + 1) =>
    rw [quasiIsoAt_iff_exactAt']
    · exact (resolution S D K a G).exact_positive (n + 1) (by omega)
    · exact ChainComplex.exactAt_succ_single_obj _ _

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
