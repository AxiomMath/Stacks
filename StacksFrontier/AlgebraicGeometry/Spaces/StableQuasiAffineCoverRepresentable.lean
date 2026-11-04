module

public import StacksFrontier.AlgebraicGeometry.Descent.PointSetCoverLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Descent.StableQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiAffineChart

/-!
# An algebraic space covered by stable quasi-affine opens of a chart over an affine base

Let `G` be an algebraic space with a morphism `π : G ⟶ yoneda a`, let `q : c ⟶ a` be a surjective
étale morphism of the site with `c` affine, and let `g : yoneda U ⟶ G`, `ρ : yoneda U ⟶ yoneda c`
present `yoneda U` as `G ×_a c`. Let `π₁ π₂ : D ⟶ U` present `yoneda D` as the fibre product of
`g` with itself, with `π₁` quasi-compact. If every point of `U` lies in an open `T` of `U` which
is stable for the relation, `π₂(π₁⁻¹ T) ⊆ T`, and is a quasi-affine scheme, then `G` is a scheme.

This is the glueing step of the proof of [Stacks, Tag 0D35]: there the opens `T` are the
nonvanishing loci, in the chart `Y = V ×_U X`, of the sections of the powers of `L` defined on
`X`, which are stable because the sections come from `X` and quasi-affine because the pullback
of `L` to `Y` is ample.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_forall_mem_stable_isQuasiAffine`: the statement
  above.

## Proof

The cover is indexed by the affine opens `A` of `U` lying in some stable quasi-affine open `T`;
by the basis property of affine opens they cover `U`. The open subspace of `G` cut out by the
image of `A` pulls back, cartesianly, to the open subscheme `b` of `U` cutting out the saturation
`π₂(π₁⁻¹ A)` of `A` (`AlgebraicGeometry.Space.exists_isPullback_ι_openSubspaceOfPoints_image`).
That saturation lies in `T`, by stability, and is quasi-compact, `π₁` being quasi-compact; so
`b` is a quasi-compact scheme with an open immersion into the quasi-affine scheme `T`, hence is
quasi-affine, and so quasi-affine over the affine `c`. Hence the open subspace is representable
(`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom_chart`), and
these representable open subspaces cover the points of `G`, which makes `G` representable by
`AlgebraicGeometry.Space.isRepresentable_of_isOpenImmersion_cover`, with the size bound of
`AlgebraicGeometry.Space.exists_lt_cutoff_size_le_of_isOpenSubspace`.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space covered by stable quasi-affine opens of a chart over an affine base is a
scheme.** For a chart `g : yoneda U ⟶ G` presenting `yoneda U` as the base change of a surjective
étale `q : c ⟶ a` with `c` affine, and a presentation `π₁ π₂ : D ⟶ U` of the fibre product of
`g` with itself with `π₁` quasi-compact, if every point of `U` lies in an open which is stable,
`π₂(π₁⁻¹ T) ⊆ T`, and is a quasi-affine scheme, then `G` is representable. -/
theorem isRepresentable_of_forall_mem_stable_isQuasiAffine
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (q : c ⟶ a)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map q))
    {D : BigFppfOver B S hS} {π₁ π₂ : D ⟶ U}
    (sqD : IsPullback (yoneda.map π₁) (yoneda.map π₂) g g)
    (hπ₁ : QuasiCompact ((BigFppfOver.toScheme B S hS).map π₁))
    (H : ∀ y : (BigFppfOver.toScheme B S hS).obj U,
      ∃ T : ((BigFppfOver.toScheme B S hS).obj U).Opens, y ∈ T ∧
        (BigFppfOver.toScheme B S hS).map π₂ ''
            ((BigFppfOver.toScheme B S hS).map π₁ ⁻¹' (T : Set _)) ⊆ (T : Set _) ∧
          T.toScheme.IsQuasiAffine) :
    G.IsRepresentable := by
  classical
  have hg := presheafIsOpenMap_of_isPullback_of_etale B S hS sqg hqe
  have hsurj := surjective_pointsMap_of_isPullback_of_surjective B S hS sqg hqs
  -- the affine opens of the chart lying in a stable quasi-affine open
  let ι := {A : ((BigFppfOver.toScheme B S hS).obj U).affineOpens //
    ∃ T : ((BigFppfOver.toScheme B S hS).obj U).Opens, A.1 ≤ T ∧
      (BigFppfOver.toScheme B S hS).map π₂ ''
          ((BigFppfOver.toScheme B S hS).map π₁ ⁻¹' (T : Set _)) ⊆ (T : Set _) ∧
        T.toScheme.IsQuasiAffine}
  let Wp : ι → Set (points B S hS G) := fun A =>
    pointsMap B S hS (yoneda.obj U) g ''
      (pointsToScheme B S hS U ⁻¹' (A.1.1 : Set _))
  have hWopen : ∀ A, IsOpen (Wp A) := fun A =>
    isOpen_image_pointsMap_of_isOpen B S hS g hg A.1.1.isOpen
  -- each piece is representable
  have hrep : ∀ A : ι, (openSubspaceOfPoints B S hS G (Wp A)).toFunctor.IsRepresentable := by
    intro A
    obtain ⟨T, hAT, hTst, hTqa⟩ := A.2
    obtain ⟨b, i, k, hi, hirange, hsqb⟩ :=
      exists_isPullback_ι_openSubspaceOfPoints_image B S hS g hg A.1.1.isOpen
    have hcpt := isCompact_preimage_image_pointsMap B S hS g sqD hπ₁ A.1.1.isOpen
      A.1.2.isCompact
    rw [← hirange] at hcpt
    rw [image_pointsToScheme_preimage_image_pointsMap B S hS g sqD] at hirange
    have hsub : Set.range ((BigFppfOver.toScheme B S hS).map i) ⊆ (T : Set _) := by
      rw [hirange]
      exact (Set.image_mono (Set.preimage_mono hAT)).trans hTst
    have _hi := hi
    have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) :=
      ⟨hi.base_open.isEmbedding.isCompact_iff.2 (by rwa [Set.image_univ])⟩
    have _ := hTqa
    have hrange' : Set.range ((BigFppfOver.toScheme B S hS).map i) ⊆ Set.range T.ι := by
      rw [Scheme.Opens.range_ι]
      exact hsub
    have hbqa : ((BigFppfOver.toScheme B S hS).obj b).IsQuasiAffine :=
      Scheme.IsQuasiAffine.of_isImmersion
        (IsOpenImmersion.lift T.ι ((BigFppfOver.toScheme B S hS).map i) hrange')
    have _ := hc
    exact isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom_chart hG.isSheaf π q hqs hqe
      sqg hsqb ((isQuasiAffineHom_iff_isQuasiAffine _).2 hbqa)
  have hex : ∀ A : ι, ∃ Wt : BigFppfOver B S hS,
      Nonempty (yoneda.obj Wt ≅ (openSubspaceOfPoints B S hS G (Wp A)).toFunctor) := by
    intro A
    have := hrep A
    exact ⟨_, ⟨(openSubspaceOfPoints B S hS G (Wp A)).toFunctor.reprW⟩⟩
  choose Wt hWt using hex
  -- the size bounds
  obtain ⟨μ, hμ, hbound⟩ := exists_lt_cutoff_size_le_of_isOpenSubspace B S hS hG
  have hι : Cardinal.mk ι < B.cutoff :=
    (Cardinal.mk_subtype_le _).trans_lt
      (((BigFppfOver.toScheme B S hS).obj U).mk_affineOpens_le_size.trans_lt U.left.property)
  -- the affine pieces cover the chart
  have hcovU : ⋃ A : ι, (A.1.1 : Set ((BigFppfOver.toScheme B S hS).obj U)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨T, hyT, hTst, hTqa⟩ := H y
    obtain ⟨A, hA, hyA, hAT⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens hyT
    exact Set.mem_iUnion.2 ⟨⟨⟨A, hA⟩, T, hAT, hTst, hTqa⟩, hyA⟩
  refine isRepresentable_of_isOpenImmersion_cover B S hS hG.isSheaf hι hμ (W := Wt)
    (fun A => hbound _ _ (isOpenSubspace_openSubspaceOfPoints B S hS hG _ (hWopen A)) (hWt A))
    (fun A => (hWt A).some.hom ≫ (openSubspaceOfPoints B S hS G (Wp A)).ι)
    (fun A => MorphismProperty.RespectsIso.precomp _ _ _
      (presheaf_isOpenImmersion_ι_openSubspaceOfPoints B S hS _ (hWopen A))) ?_
  have hrange : ∀ A : ι, Set.range (pointsMap B S hS (yoneda.obj (Wt A))
      ((hWt A).some.hom ≫ (openSubspaceOfPoints B S hS G (Wp A)).ι)) = Wp A := by
    intro A
    rw [pointsMap_comp, Set.range_comp,
      (pointsMap_surjective_of_isIso B S hS (hWt A).some.hom).range_eq, Set.image_univ,
      range_pointsMap_ι_openSubspaceOfPoints]
  simp only [hrange]
  exact iUnion_image_pointsMap_eq_univ B S hS g hsurj _ hcovU

end AlgebraicGeometry.Space

end
