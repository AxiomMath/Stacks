module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartPresentationTransport
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionComparisonNaturality

/-!
# The chart condition on a completed morphism of Noetherian affine schemes

Let `S` be a scheme contained in a big fppf site `B`, let `φ : A → C` be a homomorphism of
Noetherian rings whose spectra lie in the site, and let `I ⊆ A` be an ideal. The morphism
`Spec C ⟶ Spec A` induces a morphism of completions
`(Spec C)_{/|φ|⁻¹ V(I)} ⟶ (Spec A)_{/V(I)}`, and by **Stacks 0GBA (2)** — the identification of
the completion along `V(I)` with the formal spectrum of the `I`-adic completion, which is natural
in `φ` (`AlgebraicGeometry.FormalSpace.completionComparison_naturality_completionSheafMap`) —
that morphism is the formal spectrum of the induced map `A^∧ → C^∧` of adic completions.

So the chart condition of Stacks 0ANG on this morphism, for the class `WAdm^{Noeth}` and a
property `P` invariant under isomorphism of source and target, is the property `P` of the single
arrow `A^∧ → C^∧`: every other presentation of the chart map differs from this one by
isomorphisms of topological rings (Stacks 0AN0 and Stacks 0AIC).

This is the affine step of the source's proofs of Stacks 0GDH and Stacks 0AR2: "We have
`X_{/T} = Spf(A^∧)` and `X'_{/T'} = Spf((A')^∧)`, see proof of Formal Spaces, Lemma 0AQ1."

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_completionSheafMap_spec`: the chart
  condition on the completion of `Spec C ⟶ Spec A` from `P` of the map of adic completions.

## References

* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

/-- The `K`-adic topology of the `K`-adic completion as a module, the topology in which the
completion presents the completion along `V(K)` by Stacks 0GBA (2). -/
abbrev adicCompletionModuleTopology {R : Type u} [CommRing R] (K : Ideal R) :
    TopologicalSpace (AdicCompletion K R) :=
  K.adicModuleTopology (AdicCompletion K R)

attribute [local instance] adicCompletionModuleTopology

/-- Over a Noetherian ring the module topology makes the adic completion a topological ring. -/
theorem isTopologicalRing_adicCompletionModuleTopology {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : Ideal R) : IsTopologicalRing (AdicCompletion K R) :=
  isTopologicalRing_adicModuleTopology K (IsNoetherian.noetherian K)

/-- Over a Noetherian ring the module topology on the adic completion is linear. -/
theorem isLinearTopology_adicCompletionModuleTopology {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : Ideal R) :
    IsLinearTopology (AdicCompletion K R) (AdicCompletion K R) :=
  isLinearTopology_adicModuleTopology K (IsNoetherian.noetherian K)

attribute [local instance] isTopologicalRing_adicCompletionModuleTopology
  isLinearTopology_adicCompletionModuleTopology

/-- The `K`-adic completion of a Noetherian ring, with its module topology, is an object of
`WAdm^{Noeth}`. -/
theorem isNoetherianAdic_adicCompletion {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : Ideal R) : TopologicalRing.IsNoetherianAdic (AdicCompletion K R) :=
  ⟨isAdic_adicModuleTopology K (IsNoetherian.noetherian K), inferInstance⟩

/-- Rings of `WAdm^{Noeth}` are weakly admissible. -/
theorem isWeaklyAdmissible_of_isNoetherianAdic (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : TopologicalRing.IsNoetherianAdic R) :
    TopologicalRing.IsWeaklyAdmissible R :=
  TopologicalRing.IsAdic.isWeaklyAdmissible hR.1

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [CommRing C] [IsNoetherianRing A] [IsNoetherianRing C]
  (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
  (f : Spec (.of A) ⟶ S) (φ : A →+* C) (I : Ideal A)
  (specMap : affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) ⟶
    affineOver B S hS hA f)

/-- **The chart condition on a completed morphism of Noetherian affine schemes.** For a property
`P` of arrows of `WAdm^{Noeth}` invariant under isomorphism of source and target, the morphism of
completions `(Spec C)_{/|φ|⁻¹ V(I)} ⟶ (Spec A)_{/V(I)}` induced by `φ : A → C` satisfies the
chart condition of Stacks 0ANG for `P` as soon as the induced map `A^∧ → C^∧` of adic
completions has `P`. -/
theorem hasPropertyOnAffineChartMap_completionSheafMap_spec
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPiso : PropertyInvariantUnderRingEquiv TopologicalRing.IsNoetherianAdic P)
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (hP : P (adicCompletionMap φ I (I.map φ) le_rfl)) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic P
      (Space.completionSheafMap B S hS (yoneda.map specMap) (zeroLocusPoints B S hS hA f I)) := by
  obtain ⟨D, hD⟩ := exists_adicQuotientSystem_compatible B S hS hA f I
    (IsNoetherian.noetherian I)
  obtain ⟨E, hE⟩ := exists_adicQuotientSystem_compatible B S hS hC
    (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ) (IsNoetherian.noetherian _)
  have hwa := isWeaklyAdmissible_of_isNoetherianAdic _ (isNoetherianAdic_adicCompletion I)
  let g₀ := adicCompletionContinuousHom B S hS f φ I (I.map φ) D hD E hE le_rfl
  have hiA := isIso_completionComparison B S hS hA f I (IsNoetherian.noetherian I) D hD
  have hiC := isIso_completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)
    (I.map φ) (IsNoetherian.noetherian _) E hE
  have hpts := zeroLocusPoints_map_eq_preimage_zeroLocusPoints B S hS hA hC f φ I specMap hspec
  have hsq := completionComparison_naturality_adicCompletionMap B S hS hA hC f φ I (I.map φ)
    specMap D hD E hE hspec hwa le_rfl
  rw [Space.completionSheafRestrict_eq_eqToHom_comp (hT' := hpts)] at hsq
  refine hasPropertyOnAffineChartMap_of_presentation_of_propertyInvariantUnderRingEquiv
    isWeaklyAdmissible_of_isNoetherianAdic hPiso
    _ (isNoetherianAdic_adicCompletion I) (isNoetherianAdic_adicCompletion (I.map φ)) D E
    ((eqToIso (congrArg (Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))) hpts)).symm ≪≫
      (asIso (completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ)
        E hE)).symm)
    (asIso (completionComparison B S hS hA f I D hD)).symm g₀ ?_ hP
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, asIso_inv, Iso.symm_inv, asIso_hom,
    Category.assoc]
  rw [← hsq]
  simp

end AlgebraicGeometry.FormalSpace

end
