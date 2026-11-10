module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre

/-!
# The inverse image along an augmentation is cartesian

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
Stacks 0D7H (1) says that the inverse image `a⁻¹𝒢` of a sheaf on `(D, K)` — of sets or of
abelian groups — is a cartesian sheaf on the total site, i.e. that every inverse-image transition
`f_φ⁻¹ (a⁻¹𝒢)_m ⟶ (a⁻¹𝒢)_n` of Stacks 09WF is invertible.

The reason is that `a_m ∘ f_φ = a_n`, which is the isomorphism
`CategoryTheory.SimplicialSiteSituation.Augmentation.transitionInverseImageIso` (Stacks 0D70,
compatibility (1)). The inverse image of the total augmentation is built as the
descent of the system of the inverse images along the component augmentations, so its restriction
to degree `n` *is* `a_n⁻¹𝒢` and its direct-image transition *is* the mate of that isomorphism —
this is `componentRestrictionIso_restrictTransition`. Taking mates back along the topos adjunction
of `f_φ` exhibits the inverse-image transition as a composite of three isomorphisms.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.fiberTransition_inverseImageSheaf`: the
  inverse-image transition of `a⁻¹𝒢` written as a composite of isomorphisms.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isCartesianSheaf_inverseImage`:
  **Stacks 0D7H (1)** for a sheaf of sets.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isCartesianAbSheaf_totalInverseImageAb`:
  **Stacks 0D7H (1)** for a sheaf of abelian groups.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.isIso_abelianFiberTransition_totalInverseImageAb`: the same, read through the abelian
  transition of Stacks 09WF rather than through the underlying sheaf of sets.

## Implementation notes

The statement for sheaves of sets is phrased for `Augmentation.inverseImage`, and restated for
the inverse image of the morphism of topoi `Augmentation.totalMorphismOfTopoi` of Stacks 0D70,
which is that functor on the nose.

Cartesianness of an abelian sheaf is, by the definition of
`CategoryTheory.SimplicialSiteSituation.IsCartesianAbSheaf`, cartesianness of its underlying
sheaf of sets, and the underlying sheaf of the canonical abelian inverse image is the inverse
image of the underlying sheaf definitionally — `Sites.abelianInverseImage_forgetIso` is the
identity isomorphism. So the abelian statement is the set-valued one applied to the underlying
sheaf, with no transport.

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The inverse-image transition of Stacks 09WF between the restrictions of `a⁻¹𝒢` is, under the
identifications of those restrictions with the inverse images along the component augmentations,
the inverse-image comparison `f_φ⁻¹ a_m⁻¹𝒢 ≅ a_n⁻¹𝒢` of Stacks 0D70. -/
theorem fiberTransition_inverseImageSheaf (G : Sheaf K (Type u)) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (fiberTransition S φ).app (inverseImageSheaf S D K a G) =
      (S.transitionMorphism φ).inverseImage.map (componentRestrictionIso S D K a G m).hom ≫
        ((transitionInverseImageIso S D K a φ).hom.app G ≫
          (componentRestrictionIso S D K a G n).inv) := by
  apply ((S.transitionMorphism φ).adj.homEquiv _ _).injective
  rw [fiberTransition_adj, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  have hdirect : (S.transitionMorphism φ).adj.homEquiv _ _
        ((transitionInverseImageIso S D K a φ).hom.app G) =
      (transitionDirectInverseImageTrans S D K a φ).app G := rfl
  rw [hdirect, ← Category.assoc, componentRestrictionIso_restrictTransition, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- The inverse image along the total augmentation of a sheaf of sets on the augmentation site is
a cartesian sheaf on the total site. -/
@[stacks 0D7H "part (1), sheaves of sets"]
theorem isCartesianSheaf_inverseImage (G : Sheaf K (Type u)) :
    IsCartesianSheaf S ((inverseImage S D K a).obj G) := by
  intro m n φ
  change IsIso ((fiberTransition S φ).app (inverseImageSheaf S D K a G))
  rw [fiberTransition_inverseImageSheaf]
  infer_instance

/-- **Stacks 0D7H (1)** for sheaves of sets, phrased through the morphism of topoi of
Stacks 0D70: `a⁻¹𝒢` is cartesian. -/
theorem isCartesianSheaf_totalMorphismOfTopoi_inverseImage (G : Sheaf K (Type u)) :
    IsCartesianSheaf S ((totalMorphismOfTopoi S D K a).inverseImage.obj G) :=
  isCartesianSheaf_inverseImage S D K a G

/-- The inverse image along the total augmentation of an abelian sheaf on the augmentation site
is a cartesian abelian sheaf on the total site. -/
@[stacks 0D7H "part (1), sheaves of abelian groups"]
theorem isCartesianAbSheaf_totalInverseImageAb (G : Sheaf K Ab.{u}) :
    IsCartesianAbSheaf S ((totalInverseImageAb S D K a).obj G) :=
  isCartesianSheaf_inverseImage S D K a ((sheafCompose K (forget Ab.{u})).obj G)

/-- **Stacks 0D7H (1)** for sheaves of abelian groups, read through the abelian transition of
Stacks 09WF: every comparison `f_φ⁻¹ (a⁻¹𝒢)_m ⟶ (a⁻¹𝒢)_n` of abelian sheaves on a component is
invertible. -/
theorem isIso_abelianFiberTransition_totalInverseImageAb (G : Sheaf K Ab.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((abelianFiberTransition S φ).app ((totalInverseImageAb S D K a).obj G)) :=
  (abelianFiberTransition_isIso_iff S φ _).mpr
    (isCartesianAbSheaf_totalInverseImageAb S D K a G φ)

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
