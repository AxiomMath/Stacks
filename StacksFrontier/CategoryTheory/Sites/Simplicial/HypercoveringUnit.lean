module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDegreeZeroFaithful
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocallyFull
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationPushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianAdjunctionForget
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# `E = a_* a⁻¹ E` for the augmentation of a hypercovering

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf, in the sense of Stacks 09VU. Let `a : Sh((C/K)_total) ⟶ Sh(C)` be the
augmentation of Stacks 0D8B, given by the degree-zero localization functor. This file proves that
the unit `E ⟶ a_* a⁻¹ E` of `a⁻¹ ⊣ a_*` is an isomorphism, on sheaves of sets and on sheaves of
abelian groups, together with the full faithfulness of `a⁻¹` it comes from. These are three of
the five clauses of Stacks 0D8E, in each of its two parts, and they are registered here.

The input is that `j_total` is cover dense, which is the degree-zero condition on a hypercovering
(`CategoryTheory.SimplicialSemiRepresentable.isCoverDense_totalForget`), and that it is locally
full, which is
`CategoryTheory.SimplicialSemiRepresentable.isLocallyFull_totalForget`. Together they make
restriction along `j_total` fully faithful at any coefficients, and the unit of an adjunction
with fully faithful left adjoint is invertible.

The passage from one spelling of `a⁻¹ ⊣ a_*` to another is isolated here as a statement about an
arbitrary simplicial semi-representable object of an arbitrary site, carrying no hypercovering
condition at all: `isIso_situationTotalAdjunctionUnit_of_isIso_unit`. Everything else below is
that comparison applied at a particular site — at the site of a hypercovering of the final
presheaf, and, in the last section, at the localized site `C/X` of a hypercovering of an object,
which is Stacks 0D8K.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isIso_unit_hypercovering'` and
  `.isIso_abelianUnit_hypercovering'`: **Stacks 0D8E (1) and (2)**, `E = a_* a⁻¹ E`, for sheaves
  of sets and for sheaves of abelian groups, with `a⁻¹` read as restriction along `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.full_inverseImage'`,
  `.fullyFaithfulInverseImageHypercovering'`, `.full_abelianInverseImage'` and
  `.fullyFaithfulAbelianInverseImageHypercovering'`: **Stacks 0D8E (1) and (2)**, `a⁻¹` is full
  and `a⁻¹` is fully faithful.
* `CategoryTheory.SimplicialSemiRepresentable.full_totalInverseImage` and
  `.isIso_totalAdjunctionUnit`: the same for the morphism of topoi which Stacks 0D70 attaches to
  the augmentation of the *cocontinuous simplicial site* of `K`.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_situationTotalInverseImageAb`: the
  faithfulness half at abelian coefficients, for the inverse image of the morphism of topoi which
  Stacks 0D70 attaches to the *simplicial-site situation* of `K`.
* `CategoryTheory.SimplicialSemiRepresentable.full_situationTotalInverseImage`,
  `.isIso_situationTotalAdjunctionUnit` and `.isIso_situationAbelianTotalAdjunctionUnit`: the
  same for the morphism of topoi of Stacks 0D70 read at the simplicial-site *situation* of `K`,
  which is the spelling the derived statements of Stacks 0D8G consume.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_situationTotalAdjunctionUnit_of_isIso_unit`
  and `.isIso_situationAbelianTotalAdjunctionUnit_of_isIso_unit`: the comparison of the two
  spellings, for an arbitrary simplicial semi-representable object of an arbitrary site — the
  unit in the spelling of Stacks 0D70 is invertible as soon as the unit of restriction along
  `j_total` is. The two statements above are this comparison at a hypercovering of the final
  presheaf.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_situationTotalAdjunctionUnit_over` and
  `.isIso_situationAbelianTotalAdjunctionUnit_over`: **Stacks 0D8K (1) and (2)**, the
  degree-zero identification `E = a_* a^{-1} E` in the spelling of Stacks 0D70, for a
  hypercovering of an *object* `X`. This is the comparison at the site `C/X`, applied to
  `CategoryTheory.SimplicialSemiRepresentable.isIso_unit_over`.

## Implementation notes

The two spellings of `a⁻¹` — restriction along `j_total`, and the inverse image of the morphism
of topoi which Stacks 0D70 attaches to the cocontinuous simplicial site — are identified by
`CategoryTheory.SimplicialSemiRepresentable.totalInverseImageIso`, which is Stacks 0D8B, and full
faithfulness is invariant under isomorphism of functors.

There is a third spelling, the one the derived statements of Stacks 0D8G use: the morphism of
topoi which Stacks 0D70 attaches to the simplicial-site *situation* of `K`, whose direct image is
built as the limit of the cosimplicial diagram of the component direct images rather than along
the cocontinuous functor `j_total`. It is reached from the second one by
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalPushforwardIso`, which identifies the
two direct images for a general augmentation of case (B) — both are limits of the cosimplicial
sheaf of the component direct images, the second by Stacks 0D70 (3) — and by
`.totalInverseImageIso`, which is that identification carried to the inverse images by uniqueness
of adjoints. Both fullness and faithfulness transport along the latter, and
`Adjunction.unit_isIso_of_L_fully_faithful` then gives the unit in the third spelling. That chain
is `isIso_situationTotalAdjunctionUnit_of_isIso_unit`, and it carries nothing: full faithfulness
of the first spelling is read off *its* unit by `Adjunction.fullyFaithfulLOfIsIsoUnit`, rather
than being taken as a separate input, which is what makes the comparison a statement about an
arbitrary simplicial semi-representable object of an arbitrary site. In particular the
degree-zero faithfulness route of `faithful_situationTotalInverseImage` is not needed for it.

At abelian coefficients the unit is read off the geometric one:
`Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget` identifies the
abelian unit with the geometric unit after forgetting the group operations, and the forgetful
functor on abelian sheaves reflects isomorphisms. For the restriction spelling that step is not
needed, since `Functor.IsCoverDense.full_sheafPushforwardContinuous` applies at any coefficients.

The generic criteria these clauses instantiate — restriction along a continuous functor which is
cover dense and locally full is fully faithful, and the unit of an adjunction with fully faithful
left adjoint is invertible — are in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringDescent.lean`. The remaining two
clauses of Stacks 0D8E, the description of the essential image and the invertibility of the
counit on it, are registered in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringEssSurj.lean` and
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringEssSurjAb.lean`.

The statements of the last section carry a `0D8K` attribute instead, that tag being the one for a
hypercovering of an *object* rather than of the final presheaf; they are the clauses which
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDescent.lean` proves in the
restriction spelling, read here in the spelling of Stacks 0D70, and they are what the derived
statements of Stacks 0D8L consume.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C]
  (P : Pretopology C) (H : HypercoveringOfTerminal.{u, u, u} P)

/-! ### The comparison of the two spellings of the unit -/

section Comparison

variable (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{u} C))
  [J.toCoverage.HasPullbacks]

omit [HasEqualizers C] [HasPullbacks C]

/-- **The unit of the augmentation adjunction of Stacks 0D70 is invertible as soon as the unit of
restriction along `j_total` is**, for an arbitrary simplicial semi-representable object `K` of an
arbitrary site `(C, J)`.

This is the comparison of the two spellings of `a^{-1} ⊣ a_*` which the simplicial-site
apparatus of Stacks 0D8B carries, and it is what lets the unit, proved in either spelling, be
used in the other. The hypothesis is invertibility of the unit of `a^{-1} ⊣ a_*` with `a^{-1}`
read as restriction along the cocontinuous functor `j_total`; the conclusion is invertibility of
the unit of the adjunction of the morphism of topoi which Stacks 0D70 attaches to the
*simplicial-site situation* of `K`, whose inverse image is built degreewise from the component
augmentations and sheafified.

Nothing is transported by hand: invertibility of the unit of an adjunction is full faithfulness
of its left adjoint, that is invariant under isomorphism of functors, and the two functors are
identified by `totalInverseImageIso` (Stacks 0D8B) followed by
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalInverseImageIso` (uniqueness of
adjoints, Stacks 0D70 (3)). -/
theorem isIso_situationTotalAdjunctionUnit_of_isIso_unit
    (h : IsIso (totalLocalizationMorphism J K).adj.unit) :
    IsIso (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K)
      (Cat.of C) J (situationAugmentation J K)).adj.unit := by
  have := h
  have hff := ((Adjunction.fullyFaithfulLOfIsIsoUnit
    (totalLocalizationMorphism J K).adj).ofIso (totalInverseImageIso J K).symm).ofIso
      (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso (augmentation J K)).symm
  exact @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K)
      (Cat.of C) J (situationAugmentation J K)).adj hff.full hff.faithful

/-- **The abelian unit of the augmentation adjunction of Stacks 0D70 is invertible as soon as the
geometric unit of restriction along `j_total` is**, for an arbitrary simplicial semi-representable
object `K` of an arbitrary site `(C, J)`.

This is `isIso_situationTotalAdjunctionUnit_of_isIso_unit` read at abelian coefficients:
`Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget` identifies the
abelian unit with the geometric one after forgetting the group operations, and forgetting the
group operations on abelian sheaves reflects isomorphisms. No abelian hypothesis is needed,
because the geometric statement is one about the site. -/
theorem isIso_situationAbelianTotalAdjunctionUnit_of_isIso_unit
    (h : IsIso (totalLocalizationMorphism J K).adj.unit) :
    IsIso (SimplicialSiteSituation.Augmentation.abelianTotalAdjunction (situation J K)
      (Cat.of C) J (situationAugmentation J K)).unit := by
  have := isIso_situationTotalAdjunctionUnit_of_isIso_unit J K h
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun G => ?_
  have hforget : (sheafCompose J (forget AddCommGrpCat.{u})).map
        ((SimplicialSiteSituation.Augmentation.abelianTotalAdjunction (situation J K)
          (Cat.of C) J (situationAugmentation J K)).unit.app G) =
      (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K)
          (Cat.of C) J (situationAugmentation J K)).adj.unit.app
        ((sheafCompose J (forget AddCommGrpCat.{u})).obj G) :=
    Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget _ _ G
  have : IsIso ((sheafCompose J (forget AddCommGrpCat.{u})).map
      ((SimplicialSiteSituation.Augmentation.abelianTotalAdjunction (situation J K)
        (Cat.of C) J (situationAugmentation J K)).unit.app G)) := by
    rw [hforget]
    exact NatIso.isIso_app_of_isIso _ _
  exact isIso_of_reflects_iso _ (sheafCompose J (forget AddCommGrpCat.{u}))

end Comparison

/-! ### Full faithfulness of restriction along `j_total` -/

/-- **Stacks 0D8E (1), fullness.** For a hypercovering `K` the inverse image
`a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` of the augmentation is full.

The localization functor `j_total` is cover dense by `isCoverDense_totalForget` and locally full
by `isLocallyFull_totalForget`, and restriction along a continuous functor which is both is
full. -/
@[stacks 0D8E "part (1): a^{-1} on sheaves of sets is full"]
theorem full_inverseImage' :
    (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).inverseImage.Full :=
  full_inverseImage_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H)

/-- **Stacks 0D8E (1), full faithfulness.** For a hypercovering `K` the inverse image
`a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` of the augmentation is fully faithful: it is faithful by
`faithful_inverseImage_of_isCoverDense` and full by `full_inverseImage'`. -/
@[stacks 0D8E "part (1): a^{-1} on sheaves of sets is fully faithful"]
def fullyFaithfulInverseImageHypercovering' :
    (totalLocalizationMorphism P.toGrothendieck
      H.toSimplicialObject).inverseImage.FullyFaithful :=
  fullyFaithfulInverseImage P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H)

/-- **Stacks 0D8E (1), `E = a_* a^{-1} E`.** For every sheaf of sets `E` on `C` the canonical
map `E ⟶ a_* a^{-1} E` is an isomorphism, `a^{-1}` being restriction along `j_total`. This is the
half of "`a_*` is a quasi-inverse" that holds on all of `Sh(C)`: the unit of an adjunction with
fully faithful left adjoint is invertible. -/
@[stacks 0D8E "part (1): E = a_* a^{-1} E on sheaves of sets"]
theorem isIso_unit_hypercovering' :
    IsIso (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).adj.unit :=
  isIso_unit_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H)

/-- **Stacks 0D8E (2), fullness.** For a hypercovering `K` the inverse image
`a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` of the augmentation is full. Cover density and local fullness
of `j_total` are conditions on the site, so the same input serves at abelian coefficients. -/
@[stacks 0D8E "part (2): a^{-1} on abelian sheaves is full"]
theorem full_abelianInverseImage' :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
      ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      P.toGrothendieck).Full :=
  full_abelianInverseImage_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H)

/-- **Stacks 0D8E (2), full faithfulness.** For a hypercovering `K` the inverse image
`a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` of the augmentation is fully faithful. -/
@[stacks 0D8E "part (2): a^{-1} on abelian sheaves is fully faithful"]
def fullyFaithfulAbelianInverseImageHypercovering' :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
      ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      P.toGrothendieck).FullyFaithful :=
  fullyFaithfulAbelianInverseImage P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H)

/-- **Stacks 0D8E (2), `E = a_* a^{-1} E`.** For every sheaf of abelian groups `E` on `C` the
canonical map `E ⟶ a_* a^{-1} E` is an isomorphism, `a^{-1}` being restriction along
`j_total`. -/
@[stacks 0D8E "part (2): E = a_* a^{-1} E on abelian sheaves"]
theorem isIso_abelianUnit_hypercovering' :
    IsIso (abelianTotalAdjunction P.toGrothendieck H.toSimplicialObject).unit :=
  isIso_abelianUnit_of_isLocallyFull P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H)

/-! ### The unit of the adjunction of the morphism of topoi of Stacks 0D70 -/

/-- **Stacks 0D8E (1), fullness**, for the inverse image of the morphism of topoi which
Stacks 0D70 attaches to the augmentation. By Stacks 0D8B that functor is isomorphic to
restriction along `j_total`, and fullness is invariant under isomorphism of functors. -/
theorem full_totalInverseImage :
    Functor.Full
      (augmentation P.toGrothendieck H.toSimplicialObject).totalMorphismOfTopoi.inverseImage :=
  @Functor.Full.of_iso _ _ _ _ _ _ (full_inverseImage' P H)
    (totalInverseImageIso P.toGrothendieck H.toSimplicialObject).symm

/-- **The unit `E ⟶ a_* a^{-1} E` of Stacks 0D70 is invertible on sheaves of sets.** -/
theorem isIso_totalAdjunctionUnit :
    IsIso (augmentation P.toGrothendieck H.toSimplicialObject).totalMorphismOfTopoi.adj.unit :=
  @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _
    (augmentation P.toGrothendieck H.toSimplicialObject).totalMorphismOfTopoi.adj
    (full_totalInverseImage P H) (faithful_totalInverseImage P H)

/-- The abelian adjunction `a^{-1} ⊣ a_*` of the total augmentation is, by definition, the
abelian adjunction of the morphism of topoi which Stacks 0D70 attaches to it. -/
theorem abelianTotalAdjunction_def (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : SimplicialSiteSituation.Augmentation S D K) :
    SimplicialSiteSituation.Augmentation.abelianTotalAdjunction S D K a =
      Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward S.totalTopology
        (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi S D K a) :=
  rfl

/-- **Stacks 0D8E (2), the faithfulness half**, for the inverse image of abelian sheaves along
the total augmentation as Stacks 0D70 constructs it from the simplicial-site situation of a
hypercovering.

Forgetting the abelian-group operations is restriction of the geometric inverse image, by
`Stacks.Topos.AbelianInverseImage.abelianInverseImage_forgetIso`, and that geometric inverse
image is faithful by `faithful_situationTotalInverseImage`; a functor whose composite with
another is faithful is itself faithful. -/
theorem faithful_situationTotalInverseImageAb :
    (SimplicialSiteSituation.Augmentation.totalInverseImageAb
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).Faithful :=
  have h₁ : (sheafCompose P.toGrothendieck (forget AddCommGrpCat.{u}) ⋙
      (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi
        (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject)).inverseImage).Faithful :=
    @Functor.Faithful.comp _ _ _ _ _ _ _ _ inferInstance (faithful_situationTotalInverseImage P H)
  have : (SimplicialSiteSituation.Augmentation.totalInverseImageAb
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject) ⋙
        sheafCompose ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
          (forget AddCommGrpCat.{u})).Faithful := h₁
  Functor.Faithful.of_comp
    (SimplicialSiteSituation.Augmentation.totalInverseImageAb
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject))
    (sheafCompose ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      (forget AddCommGrpCat.{u}))

/-! ### The unit of the adjunction of the morphism of topoi of the simplicial-site situation -/

/-- **Stacks 0D8E (1), fullness**, for the inverse image of the morphism of topoi which
Stacks 0D70 attaches to the *simplicial-site situation* of a hypercovering.

That inverse image is the descent of the inverse images of the simplicial degrees, and
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalInverseImageIso` identifies it with
the inverse image along the cocontinuous functor `j_total` out of the total category, which is
full by `full_totalInverseImage`; fullness is invariant under isomorphism of functors. -/
theorem full_situationTotalInverseImage :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).inverseImage.Full :=
  @Functor.Full.of_iso _ _ _ _ _ _ (full_totalInverseImage P H)
    (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
      (augmentation P.toGrothendieck H.toSimplicialObject)).symm

/-- **Stacks 0D8E (1), the unit is invertible**, with no condition carried, for the morphism of
topoi which Stacks 0D70 attaches to the *simplicial-site situation* of a hypercovering: for every
sheaf of sets `E` on `C` the canonical map `E ⟶ a_* a^{-1} E` is an isomorphism.

This is `isIso_situationTotalAdjunctionUnit_of_isIso_unit` at the unit of restriction along
`j_total`, which is invertible by `isIso_unit_hypercovering'`. -/
theorem isIso_situationTotalAdjunctionUnit :
    IsIso (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).adj.unit :=
  isIso_situationTotalAdjunctionUnit_of_isIso_unit P.toGrothendieck H.toSimplicialObject
    (isIso_unit_hypercovering' P H)

/-- **Stacks 0D8E (2), the unit is invertible**, with no condition carried, for the morphism of
topoi which Stacks 0D70 attaches to the *simplicial-site situation* of a hypercovering: for every
sheaf of abelian groups `E` on `C` the canonical map `E ⟶ a_* a^{-1} E` is an isomorphism.

This is `isIso_situationAbelianTotalAdjunctionUnit_of_isIso_unit` at the unit of restriction
along `j_total`, which is invertible by `isIso_unit_hypercovering'`. -/
theorem isIso_situationAbelianTotalAdjunctionUnit :
    IsIso (SimplicialSiteSituation.Augmentation.abelianTotalAdjunction
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).unit :=
  isIso_situationAbelianTotalAdjunctionUnit_of_isIso_unit P.toGrothendieck
    H.toSimplicialObject (isIso_unit_hypercovering' P H)

/-! ### The unit for a hypercovering of an object -/

section Over

omit [HasEqualizers C]

variable {X : C} (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **Stacks 0D8K (1), the degree-zero identification `E = a_* a^{-1} E`**, for the morphism of
topoi which Stacks 0D70 attaches to the *simplicial-site situation* of a hypercovering `K` of an
object `X`: for every sheaf of sets `E` on `C/X` the canonical map `E ⟶ a_* a^{-1} E` is an
isomorphism, with no condition carried beyond `K` being a hypercovering of `X`.

This is the comparison `isIso_situationTotalAdjunctionUnit_of_isIso_unit` at the site `C/X`,
applied to `isIso_unit_over`. -/
@[stacks 0D8K "part (1): the unit E = a_*a⁻¹E of the morphism of topoi of Stacks 0D70 on sheaves \
of sets is an isomorphism"]
theorem isIso_situationTotalAdjunctionUnit_over (hK : IsHypercovering P K) :
    IsIso (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).adj.unit :=
  isIso_situationTotalAdjunctionUnit_of_isIso_unit (P.toGrothendieck.over X) K
    (isIso_unit_over P K hK)

/-- **Stacks 0D8K (2), the degree-zero identification `M = a_* a^{-1} M`** on sheaves of abelian
groups, for the morphism of topoi which Stacks 0D70 attaches to the *simplicial-site situation*
of a hypercovering `K` of an object `X`: for every sheaf of abelian groups `M` on `C/X` the
canonical map `M ⟶ a_* a^{-1} M` is an isomorphism, with no condition carried beyond `K` being a
hypercovering of `X`.

This is the spelling of the unit which the derived statements of Stacks 0D8L consume, and it
discharges the clause those statements would otherwise carry as a hypothesis. -/
@[stacks 0D8K "part (2): the unit M = a_*a⁻¹M of the morphism of topoi of Stacks 0D70 on abelian \
sheaves is an isomorphism"]
theorem isIso_situationAbelianTotalAdjunctionUnit_over (hK : IsHypercovering P K) :
    IsIso (SimplicialSiteSituation.Augmentation.abelianTotalAdjunction
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).unit :=
  isIso_situationAbelianTotalAdjunctionUnit_of_isIso_unit (P.toGrothendieck.over X) K
    (isIso_unit_over P K hK)

end Over

end CategoryTheory.SimplicialSemiRepresentable

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialSemiRepresentable
open CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)

/-- **Stacks 0D8G**, granted the one input the library does not have. For a site `C` with
equalizers and fibre products, a hypercovering `K` of it, and the augmentation
`a : Sh((C/K)_total) ⟶ Sh(C)` of Stacks 0D8B, the canonical map `E ⟶ R a_* a⁻¹ E` is an
isomorphism for every object `E` of the unbounded derived category of abelian sheaves on `C`.

`E` is arbitrary: no boundedness is assumed, and the coefficients are the full category of
abelian sheaves.

The underived unit `F ⟶ a_*a⁻¹F` is invertible with nothing carried, by
`CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit`, which is
Stacks 0D8E in its abelian form for this very augmentation. The one hypothesis left is
`hacyclic`, that `a⁻¹` of a K-injective complex of abelian sheaves on `C` computes `R a_*`. It is
*proved* for a hypercovering, by `CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`, and
`CategoryTheory.SimplicialSemiRepresentable`
`.isIso_derivedAugmentationUnit_app_of_hypercovering_unconditional` is this statement with it
discharged. It remains a binder here only because that proof rests on the resolution of
Stacks 0D78 and on Stacks 01GE, which sit far above this module in the import order; this module
defines `InverseImageComputesDerivedPushforward` itself. -/
@[stacks 0D8G "the Ra_*-acyclicity of a⁻¹ of a K-injective complex taken as an explicit input; it
is discharged for a hypercovering in
...SimplicialSemiRepresentable.isIso_derivedAugmentationUnit_app_of_hypercovering_unconditional,
which carries the tag unconditionally"]
theorem isIso_derivedAugmentationUnit_app_of_hypercovering'
    (hacyclic : Augmentation.InverseImageComputesDerivedPushforward
      (hypercoveringSituation J H) (Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H))
    (E : DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})) :
    IsIso ((Augmentation.derivedAugmentationUnit (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)).app E) :=
  have : IsIso (Augmentation.derivedAugmentationUnit (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)) :=
    Augmentation.isIso_derivedAugmentationUnit (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)
      (CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit J H)
      hacyclic
  NatIso.isIso_app_of_isIso _ E

end Stacks.CategoryTheory.Hypercovering

end
