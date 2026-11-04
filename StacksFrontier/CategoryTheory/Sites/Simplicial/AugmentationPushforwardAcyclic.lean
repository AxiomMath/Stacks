module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveSubcategory
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedPushforwardCriterion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionHomAcyclic
public import StacksFrontier.Homology.KFlat.Bifunctor

/-!
# Acyclicity of the direct image along an augmentation

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
For a complex `W` of abelian sheaves on the total site, the direct image `a_*W` is acyclic as
soon as the Hom complex `Hom(a⁻¹G, W^•)` is acyclic for every abelian sheaf `G` on `(D, K)`:
acyclicity of a complex of abelian sheaves is detected by the Hom complexes out of objects, and
the adjunction `a⁻¹ ⊣ a_*` identifies `Hom(G, (a_*W)^•)` with `Hom(a⁻¹G, W^•)`.

This is the bridge between the Hom-complex computations of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolutionHomAcyclic.lean` and the
criterion of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationDerivedPushforwardCriterion.lean`, which
asks for a quasi-isomorphism after `a_*`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex`: the statement above.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageComputesDerivedPushforward_of_acyclic_coyonedaComplex`: the predicate
  `InverseImageComputesDerivedPushforward` follows, by way of the cone of a K-injective
  resolution of `a⁻¹I`.

## Implementation notes

The detection of acyclicity is `CochainComplex.acyclic_of_acyclic_coyonedaComplex` and the
adjunction identification is `CochainComplex.coyonedaComplexAdjIso` at
`CategoryTheory.SimplicialSiteSituation.Augmentation.abelianTotalAdjunction`; both are stated for
an arbitrary abelian category and an arbitrary adjunction, so nothing here is specific to the
augmentation beyond naming that adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The direct image of a complex along the total augmentation is acyclic as soon as the Hom
complexes out of the inverse images are.** -/
theorem acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex
    (W : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ)
    (h : ∀ G : Sheaf K AddCommGrpCat.{u},
      (CochainComplex.coyonedaComplex ((totalInverseImageAb S D K a).obj G) W).Acyclic) :
    (((abelianTotalPushforward S D K a).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj W).Acyclic :=
  CochainComplex.acyclic_of_acyclic_coyonedaComplex _ fun G i =>
    (h G i).of_iso (CochainComplex.coyonedaComplexAdjIso (abelianTotalAdjunction S D K a) G W)

/-- **`InverseImageComputesDerivedPushforward` from acyclicity of the Hom complexes out of the
inverse images.** For a K-injective complex `I` on `(D, K)` take a K-injective resolution
`q : a⁻¹I ⟶ J` on the total site; its cone `W` is acyclic, and its restrictions to the components
are K-injective, so the hypothesis makes `Hom(a⁻¹G, W^•)` acyclic for every `G`, hence `a_*W`
acyclic, hence `a_*q` a quasi-isomorphism, which is what the criterion of
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.inverseImageComputesDerivedPushforward_of_quasiIso` asks for.

The first hypothesis is that `a⁻¹` of a K-injective complex restricts to a K-injective complex on
every component; for the simplicial site of a hypercovering it is Stacks 0D88, the component
inverse images being inverse images along localizations at semi-representable objects. -/
theorem inverseImageComputesDerivedPushforward_of_acyclic_coyonedaComplex
    (hrestr : ∀ (p : SimplexCategory) (I : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ),
      I.IsKInjective → CochainComplex.IsKInjective
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (hhom : ∀ (G : Sheaf K AddCommGrpCat.{u})
      (W : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ), W.Acyclic →
      (∀ p : SimplexCategory, CochainComplex.IsKInjective
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj W)) →
      (CochainComplex.coyonedaComplex ((totalInverseImageAb S D K a).obj G) W).Acyclic) :
    InverseImageComputesDerivedPushforward S D K a := by
  refine inverseImageComputesDerivedPushforward_of_quasiIso S D K a fun I hI => ?_
  obtain ⟨J, q, hJ, hq⟩ := exists_kInjective_resolution_total S
    (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  refine ⟨J, hJ, q, hq, ?_⟩
  have hWac : (CochainComplex.mappingCone q).Acyclic :=
    (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone q).mp hq
  have hWp : ∀ p : SimplexCategory, CochainComplex.IsKInjective
      (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone q)) := by
    intro p
    have h1 := hrestr p I hI
    have h2 : CochainComplex.IsKInjective
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) := by
      have := hJ
      exact isKInjective_componentRestriction S p J
    have h3 : CochainComplex.IsKInjective (CochainComplex.mappingCone
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
      CochainComplex.isKInjective_mappingCone _
    exact CochainComplex.isKInjective_of_iso
      (CochainComplex.mappingCone.mapHomologicalComplexIso q (restrictAb S p)).symm
  have hac := acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex S D K a
    (CochainComplex.mappingCone q) fun G => hhom G _ hWac hWp
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  exact fun i => (hac i).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso q (abelianTotalPushforward S D K a))

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
