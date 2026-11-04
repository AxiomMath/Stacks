module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringEssSurj
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of `a⁻¹` for the morphism of topoi of Stacks 0D70

Let `(C, J)` be a site with equalizers and fibre products and `K` a hypercovering of its final
presheaf. That the essential image of `a⁻¹` on sheaves of sets is exactly the cartesian sheaves is
proved in `StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringEssSurj.lean` for restriction
along the localization functor `j_total`. The sheaves of modules on the total ringed topos are
formed along the morphism of topoi which Stacks 0D70 attaches to the augmentation of the
simplicial-site *situation*, whose direct image is the limit of the cosimplicial sheaf of the
component direct images; this file carries the essential-image clause across the identification of
the two, as `StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringUnit.lean` carries full
faithfulness.

The same two files between them give the clause for a hypercovering `K` of an *object* `X` of `C`,
which is Stacks 0D8K (1): a hypercovering of `X` in `C` is a hypercovering of the final presheaf
of the localized site `C/X` with the *same* simplicial object, by
`Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_over_of_isHypercovering`, so
the total site, the total topology and the localization morphism are the same and the clause
transports verbatim; and the unit over `C/X` is invertible by
`CategoryTheory.SimplicialSemiRepresentable.isIso_situationTotalAdjunctionUnit_over`, which gives
fullness of `a⁻¹` in the Stacks 0D70 spelling. Those are the second half of this file, and they
are the clauses of Stacks 0D8K that
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDescent.lean` cannot reach: it
sits below `HypercoveringEssSurj.lean` and `HypercoveringUnit.lean` in the import order.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.essImage_situationTotalInverseImage_of_isCartesianSheaf`: **Stacks 0D8E (1)**, every cartesian
  sheaf of sets on the total site is an `a⁻¹E` for the morphism of topoi of Stacks 0D70.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.mem_essImage_situationTotalInverseImage_iff_isCartesianSheaf`: **Stacks 0D8E (1)**, the
  essential image of that `a⁻¹` is exactly the cartesian sheaves of sets.
* `CategoryTheory.SimplicialSemiRepresentable.essImage_of_isCartesianSheaf_over` and
  `.mem_essImage_inverseImage_iff_isCartesianSheaf_over`: **Stacks 0D8K (1)**, for a hypercovering
  of an object `X`, every cartesian sheaf of sets on the total site is an `a⁻¹E` and the essential
  image of `a⁻¹` is exactly the cartesian sheaves, `a⁻¹` being restriction along `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_counit_app_over`: **Stacks 0D8K (1)**, `a_*`
  is a quasi-inverse on the cartesian sheaves of sets — the counit `a⁻¹a_*F ⟶ F` is invertible at
  every cartesian `F`.
* `CategoryTheory.SimplicialSemiRepresentable.full_situationTotalInverseImage_over` and
  `.essImage_situationTotalInverseImage_of_isCartesianSheaf_over` and
  `.mem_essImage_situationTotalInverseImage_iff_isCartesianSheaf_over`: the same three statements
  over an object, for the inverse image of the morphism of topoi of Stacks 0D70.

## Implementation notes

The identification is taken in the two steps the tree has: the inverse image of Stacks 0D70 at
the simplicial-site situation is the inverse image along the cocontinuous functor out of the total
category by `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalInverseImageIso`, and
that one is restriction along `j_total` by
`CategoryTheory.SimplicialSemiRepresentable.totalInverseImageIso`, which is Stacks 0D8B. Both come
from uniqueness of left adjoints, so neither is an arbitrary comparison, and the essential image
is invariant under isomorphism of functors by `CategoryTheory.Functor.essImage.ofNatIso`.

The hypercovering of the final presheaf which the slice bridge produces is one for the pretopology
of covering families of `C/X`, which generates the localized topology `P.toGrothendieck.over X`
itself by the Galois insertion between pretopologies and topologies; so in
`essImage_of_isCartesianSheaf_over` the sheaf is quantified inside the statement, its category
depending on that topology.

Over `C/X` the hypothesis `HasEqualizers C` of the clause for the final presheaf is not needed and
is omitted: `C/X` has a final object and, from `HasPullbacks C`, fibre products, hence all finite
limits.

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u, u} P)

/-- **Stacks 0D8E (1), essential surjectivity onto the cartesian sheaves of sets**, for the
inverse image of the morphism of topoi which Stacks 0D70 attaches to the augmentation of the
simplicial-site situation of a hypercovering.

By Stacks 0D8B that inverse image is restriction along `j_total`, for which every cartesian sheaf
of sets is an inverse image by
`CategoryTheory.SimplicialSemiRepresentable.essImage_of_isCartesianSheaf`. -/
@[stacks 0D8E "part (1): every cartesian sheaf of sets is an a^{-1}E for the a of Stacks 0D70 at \
the simplicial-site situation"]
theorem essImage_situationTotalInverseImage_of_isCartesianSheaf
    (E : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u))
    (hE : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf E) :
    (Augmentation.totalMorphismOfTopoi
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).inverseImage.essImage E :=
  Functor.essImage.ofNatIso
    (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
          (augmentation P.toGrothendieck H.toSimplicialObject) ≪≫
        totalInverseImageIso P.toGrothendieck H.toSimplicialObject).symm
    (essImage_of_isCartesianSheaf P H E hE)

/-- **Stacks 0D8E (1), the essential image is exactly the cartesian sheaves of sets**, for the
inverse image of the morphism of topoi of Stacks 0D70 at the simplicial-site situation. One
inclusion is `mem_essImage_iff_isCartesianSheaf'` carried across Stacks 0D8B, the other is
`essImage_situationTotalInverseImage_of_isCartesianSheaf`. -/
@[stacks 0D8E "part (1): the essential image of the a^{-1} of Stacks 0D70 at the \
simplicial-site situation is exactly the cartesian sheaves of sets"]
theorem mem_essImage_situationTotalInverseImage_iff_isCartesianSheaf
    (E : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u)) :
    (Augmentation.totalMorphismOfTopoi
        (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject)).inverseImage.essImage E ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf E :=
  ⟨fun hE => (mem_essImage_iff_isCartesianSheaf' P H E).mp
      (Functor.essImage.ofNatIso
        (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
            (augmentation P.toGrothendieck H.toSimplicialObject) ≪≫
          totalInverseImageIso P.toGrothendieck H.toSimplicialObject) hE),
    essImage_situationTotalInverseImage_of_isCartesianSheaf P H E⟩

/-! ### The essential image for a hypercovering of an object -/

section Over

omit [HasEqualizers C]

variable {X : C} (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **Stacks 0D8K (1), essential surjectivity onto the cartesian sheaves of sets**, for
restriction along the localization functor `j_total` of a hypercovering `K` of an object `X`:
every cartesian sheaf of sets on the total site is isomorphic to a restriction of a sheaf on
`C/X`.

A hypercovering of `X` in `C` is a hypercovering of the final presheaf of the localized site
`C/X` with the same simplicial object, by
`Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_over_of_isHypercovering`, and
hence has the same total site, total topology and localization morphism; so this is Stacks
0D8E (1) read over `C/X`. The hypercovering that identification produces is one for the
pretopology of covering families of `C/X`, which generates the localized topology
`P.toGrothendieck.over X` itself by the Galois insertion between pretopologies and topologies;
the sheaf is quantified inside the statement because its category depends on that topology. -/
@[stacks 0D8K "part (1): every cartesian sheaf of sets on the total site is an a^{-1}E"]
theorem essImage_of_isCartesianSheaf_over (hK : IsHypercovering P K) :
    ∀ E : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u),
      (situation (P.toGrothendieck.over X) K).IsCartesianSheaf E →
        (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.essImage E := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨H, hH⟩ := exists_hypercoveringOfTerminal_over_of_isHypercovering P K hK
  have hQ : ((P.toGrothendieck.over X).toPretopology).toGrothendieck =
      P.toGrothendieck.over X := (Pretopology.gi (C := Over X)).l_u_eq _
  rw [← hQ, ← hH]
  exact fun E hE => essImage_of_isCartesianSheaf _ H E hE

/-- **Stacks 0D8K (1), the essential image is exactly the cartesian sheaves of sets**, for
restriction along `j_total` for a hypercovering of an object `X`. One inclusion is
`isCartesianSheaf_of_mem_essImage_over`, which is Stacks 0D7H (1) and uses no condition on `K`;
the other is `essImage_of_isCartesianSheaf_over`. -/
@[stacks 0D8K "part (1): the essential image of a^{-1} on sheaves of sets is exactly the \
cartesian sheaves of sets"]
theorem mem_essImage_inverseImage_iff_isCartesianSheaf_over (hK : IsHypercovering P K)
    (E : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u)) :
    (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.essImage E ↔
      (situation (P.toGrothendieck.over X) K).IsCartesianSheaf E :=
  ⟨isCartesianSheaf_of_mem_essImage_over K P.toGrothendieck,
    essImage_of_isCartesianSheaf_over P K hK E⟩

/-- **Stacks 0D8K (1), `a_*` is a quasi-inverse on the cartesian sheaves of sets.** For a
cartesian sheaf of sets `F` on the total site of a hypercovering of an object `X` the counit
`a⁻¹ a_* F ⟶ F` is an isomorphism.

`a⁻¹` is fully faithful, so its counit is invertible at exactly the objects of its essential
image, and `essImage_of_isCartesianSheaf_over` puts `F` there. -/
@[stacks 0D8K "part (1): a^{-1} a_* F = F for cartesian F on sheaves of sets"]
theorem isIso_counit_app_over (hK : IsHypercovering P K)
    (E : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u))
    (hE : (situation (P.toGrothendieck.over X) K).IsCartesianSheaf E) :
    IsIso ((totalLocalizationMorphism (P.toGrothendieck.over X) K).adj.counit.app E) :=
  (isIso_counit_app_iff_mem_essImage_of_isLocallyFull (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1) (isLocallyFull_totalForget_over P K hK) E).mpr
    (essImage_of_isCartesianSheaf_over P K hK E hE)

/-- **Stacks 0D8K (1), the fullness half**, for the inverse image of the total augmentation as
Stacks 0D70 constructs it from the simplicial-site situation of `C/X`.

The unit of that adjunction is invertible by
`CategoryTheory.SimplicialSemiRepresentable.isIso_situationTotalAdjunctionUnit_over`, and the left
adjoint of an adjunction with invertible unit is fully faithful. -/
theorem full_situationTotalInverseImage_over (hK : IsHypercovering P K) :
    (Augmentation.totalMorphismOfTopoi
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).inverseImage.Full :=
  (@Adjunction.fullyFaithfulLOfIsIsoUnit _ _ _ _ _ _
    (Augmentation.totalMorphismOfTopoi
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).adj
    (isIso_situationTotalAdjunctionUnit_over P K hK)).full

/-- **Stacks 0D8K (1), essential surjectivity onto the cartesian sheaves of sets**, for the
inverse image of the total augmentation as Stacks 0D70 constructs it from the simplicial-site
situation of `C/X`.

By Stacks 0D8B that inverse image is restriction along `j_total`, for which every cartesian
sheaf of sets is an inverse image by `essImage_of_isCartesianSheaf_over`; the essential image is
invariant under isomorphism of functors. -/
@[stacks 0D8K "part (1): every cartesian sheaf of sets is an a^{-1}E for the a of Stacks 0D70 at \
the simplicial-site situation of C/X"]
theorem essImage_situationTotalInverseImage_of_isCartesianSheaf_over (hK : IsHypercovering P K)
    (E : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u))
    (hE : (situation (P.toGrothendieck.over X) K).IsCartesianSheaf E) :
    (Augmentation.totalMorphismOfTopoi
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).inverseImage.essImage E :=
  Functor.essImage.ofNatIso
    (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
          (augmentation (P.toGrothendieck.over X) K) ≪≫
        totalInverseImageIso (P.toGrothendieck.over X) K).symm
    (essImage_of_isCartesianSheaf_over P K hK E hE)

/-- **Stacks 0D8K (1), the essential image is exactly the cartesian sheaves of sets**, for the
inverse image of the morphism of topoi of Stacks 0D70 at the simplicial-site situation of `C/X`.
One inclusion is `mem_essImage_inverseImage_iff_isCartesianSheaf_over` carried across
Stacks 0D8B, the other is `essImage_situationTotalInverseImage_of_isCartesianSheaf_over`. -/
@[stacks 0D8K "part (1): the essential image of the a^{-1} of Stacks 0D70 at the \
simplicial-site situation of C/X is exactly the cartesian sheaves of sets"]
theorem mem_essImage_situationTotalInverseImage_iff_isCartesianSheaf_over
    (hK : IsHypercovering P K)
    (E : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u)) :
    (Augmentation.totalMorphismOfTopoi
        (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
        (situationAugmentation (P.toGrothendieck.over X) K)).inverseImage.essImage E ↔
      (situation (P.toGrothendieck.over X) K).IsCartesianSheaf E :=
  ⟨fun hE => (mem_essImage_inverseImage_iff_isCartesianSheaf_over P K hK E).mp
      (Functor.essImage.ofNatIso
        (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
            (augmentation (P.toGrothendieck.over X) K) ≪≫
          totalInverseImageIso (P.toGrothendieck.over X) K) hE),
    essImage_situationTotalInverseImage_of_isCartesianSheaf_over P K hK E⟩

end Over

end CategoryTheory.SimplicialSemiRepresentable

end
