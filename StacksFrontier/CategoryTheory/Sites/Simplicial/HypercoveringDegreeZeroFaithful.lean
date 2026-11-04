module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism

/-!
# Faithfulness of the inverse image of the total augmentation of a hypercovering

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf. Stacks 0D70 attaches to the augmentation of the simplicial-site situation
`n ↦ C/K_n` a morphism of topoi `a : Sh((C/K)_total) ⟶ Sh(C)`. This file proves that its inverse
image is faithful, which is Stacks 0D8E (1).

Restriction to simplicial degree zero carries the inverse image of the total augmentation to the
inverse image of the degree-zero augmentation (Stacks 0D70, compatibility (b)), which is
restriction along the localization functor `j_0 : C/K_0 ⥤ C`; that functor is continuous and
cover dense by condition (1) of Stacks 09VU.

All names are in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

## Main results

* `isCoverDense_sliceForgetZero` and `faithful_degreeZeroInverseImage`: for a hypercovering, the
  degree-zero localization functor is cover dense and restriction along it is faithful.
* `faithful_componentAugmentationZeroInverseImage`: the inverse image of the degree-zero
  component augmentation is faithful.
* `faithful_situationTotalInverseImage`: **Stacks 0D8E (1), the faithfulness half**, for the
  inverse image of the total augmentation of Stacks 0D70.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
* [Stacks Project, Tag 0D9D](https://stacks.math.columbia.edu/tag/0D9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u, u} P)

/-- The degree-zero localization functor `j_0 : C/K_0 ⥤ C` of a hypercovering is cover dense
for the topology of the pretopology `P`; the covering is that of condition (1) of Stacks 09VU. -/
theorem isCoverDense_sliceForgetZero :
    (sliceForget H.toSimplicialObject (op ⦋0⦌)).IsCoverDense P.toGrothendieck :=
  ⟨fun V => GrothendieckTopology.superset_covering _
    (by rintro W g ⟨i, ⟨p⟩⟩; exact ⟨⟨⟨i, Over.mk p⟩, 𝟙 W, g, Category.id_comp g⟩⟩)
    (degreeZeroSieve_mem P H V)⟩

/-- Restriction along the degree-zero localization functor of a hypercovering is faithful, as
restriction along a continuous cover-dense functor is (Stacks 04D9). -/
theorem faithful_degreeZeroInverseImage :
    (localizationMorphism P.toGrothendieck H.toSimplicialObject ⦋0⦌).inverseImage.Faithful :=
  let := isCoverDense_sliceForgetZero P H
  sheafPushforwardContinuous_faithful_of_isCoverDense
    (sliceForget H.toSimplicialObject (op ⦋0⦌))
    ((situation P.toGrothendieck H.toSimplicialObject).componentTopology ⦋0⦌)
    P.toGrothendieck (Type u)

/-- The inverse image of the degree-zero component augmentation of a hypercovering, which is
isomorphic to restriction along `j_0` (Stacks 0D8B), is faithful. -/
theorem faithful_componentAugmentationZeroInverseImage :
    (SimplicialSiteSituation.Augmentation.componentAugmentation
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject) ⦋0⦌).inverseImage.Faithful :=
  @Functor.Faithful.of_iso _ _ _ _ _ _ (faithful_degreeZeroInverseImage P H)
    (componentInverseImageIso P.toGrothendieck H.toSimplicialObject ⦋0⦌).symm

/-- **Stacks 0D8E (1), the faithfulness half**, for the inverse image of the total augmentation
as Stacks 0D70 constructs it from the simplicial-site situation of a hypercovering: that inverse
image is faithful. -/
@[stacks 0D8E "part (1): a^{-1} of Stacks 0D70 on sheaves of sets is faithful, for the \
simplicial-site situation attached to a hypercovering"]
theorem faithful_situationTotalInverseImage :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).inverseImage.Faithful :=
  have : (SimplicialSiteSituation.Augmentation.inverseImage
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject) ⋙
        (situation P.toGrothendieck H.toSimplicialObject).restrict ⦋0⦌).Faithful :=
    @Functor.Faithful.of_iso _ _ _ _ _ _ (faithful_componentAugmentationZeroInverseImage P H)
      (SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso
        (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject) ⦋0⦌).symm
  Functor.Faithful.of_comp
    (SimplicialSiteSituation.Augmentation.inverseImage
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject))
    ((situation P.toGrothendieck H.toSimplicialObject).restrict ⦋0⦌)

end CategoryTheory.SimplicialSemiRepresentable

end
