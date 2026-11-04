module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.RelativeLinearAction
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension

/-!
# The translate `r_g(C)` of a closed subvariety contained in the domain of `r_g`

The projective transformation `r_g` attached to an endomorphism `g` of `V` is defined on the open
`U(g) ⊆ 𝐏(V)`. A closed subset `C` of `𝐏(V)` contained in `U(g)` is proper over the ground field,
being closed in `𝐏(V)`; so its translate `r_g(C)` — the set
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage` — is the image of a proper scheme
and is therefore closed, irreducible when `C` is, and of dimension at most that of `C`. These are
exactly the properties the fibres of the family `C'` of Tag 0B1T must have for the clauses of
that tag to be statements about closed subvarieties.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_comp_toSpec`: `r_g` is a morphism over
  the ground field.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isProper_range_eq_endProjectionImage`: the
  translate is the image of a proper scheme over the ground field, of dimension at most that of
  `C`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_endProjectionImage`: the translate is
  closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_mem_endProjection_eq`: a closed
  point of the translate is the image of a point of `C` which is closed in `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_endProjectionImage`: it is irreducible
  when `C` is.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_le`: its
  dimension is at most that of `C`.

## Implementation notes

The construction follows the properness step of
`StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines`, which does the same for the
linear projection away from a submodule: the reduced closed subscheme on `C` lifts along the open
immersion of `U(g)`, because its image is contained in `U(g)`, and the lift composed with `r_g`
is proper over the ground field because `r_g` is.

That `r_g` is a morphism over the ground field is the same computation as
`AlgebraicGeometry.ProjectiveSpaceOfModule.projection_comp_toSpec`: both morphisms are
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` of a graded homomorphism induced by a linear
map, and the degree-zero part of such a homomorphism is the identity on scalars
(`AlgebraicGeometry.ProjectiveSpaceOfModule.gradedZeroRingHom_gradedSymAlgMap_comp_algebraMap`).

The dimension bound is `AlgebraicGeometry.topologicalKrullDim_closure_image_le` applied to `r_g`
on the preimage of `C` in `U(g)`. That lemma needs a Noetherian source space: `𝐏(V)` is proper
over `Spec k`, hence locally of finite type over a field and quasi-compact, so it is a Noetherian
scheme, and `U(g)` is an open subspace of it. Irreducibility needs no such input: the preimage of
an irreducible set meeting `U(g)` under an open immersion is irreducible
(`IsIrreducible.preimage`), and the translate is its continuous image.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **`r_g` is a morphism over the ground field.** -/
public theorem endProjection_comp_toSpec (g : V →ₗ[k] V) :
    endProjection k V g ≫ projectiveSpaceOfModuleToSpec k V =
      (endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V := by
  rw [projectiveSpaceOfModuleToSpec, endProjection,
    ← Category.assoc, mapHom_toSpecZero, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, gradedZeroRingHom_gradedSymAlgMap_comp_algebraMap]

/-- The reduced closed subscheme on a closed `C ⊆ U(g)` lifts along the open immersion of `U(g)`,
with image the preimage of `C`. -/
private theorem exists_lift_closedImmersion_endDomain (g : V →ₗ[k] V)
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    ∃ (S : Scheme.{u}) (ι : S ⟶ projectiveSpaceOfModule k V) (j : S ⟶ (endDomain k V g).toScheme),
      IsClosedImmersion ι ∧ j ≫ (endDomain k V g).ι = ι ∧ Set.range ι.base = C ∧
        Set.range j.base = (endDomain k V g).ι.base ⁻¹' C := by
  set I : (projectiveSpaceOfModule k V).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩
  have hrange : Set.range I.subschemeι.base = C := range_vanishingIdeal_subschemeι C hC
  have hsub : Set.range I.subschemeι.base ⊆ Set.range (endDomain k V g).ι.base := by
    rw [hrange, Scheme.Opens.range_ι]
    exact hCg
  set j := IsOpenImmersion.lift (endDomain k V g).ι I.subschemeι hsub
  have hjfac : j ≫ (endDomain k V g).ι = I.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ y, (endDomain k V g).ι.base (j.base y) = I.subschemeι.base y := by
    intro y
    rw [← hjfac, Scheme.Hom.comp_base]
    rfl
  refine ⟨I.subscheme, I.subschemeι, j, inferInstance, hjfac, hrange, ?_⟩
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [Set.mem_preimage, hcomp, ← hrange]
    exact ⟨y, rfl⟩
  · obtain ⟨y, hy⟩ : (endDomain k V g).ι.base x ∈ Set.range I.subschemeι.base := by
      rw [hrange]; exact hx
    exact ⟨y, (endDomain k V g).ι.isOpenEmbedding.injective (by rw [hcomp, hy])⟩

variable [FiniteDimensional k V] [Nontrivial V]

/-- Composing a locally finite type morphism into `𝐏(V)` with the structure map is locally of
finite type. -/
private theorem locallyOfFiniteType_comp_toSpec {X : Scheme.{u}}
    (h : X ⟶ projectiveSpaceOfModule k V) [LocallyOfFiniteType h] :
    LocallyOfFiniteType (h ≫ projectiveSpaceOfModuleToSpec k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by infer_instance
  infer_instance

/-- **The translate of a closed subvariety contained in `U(g)` is the image of a proper scheme
over the ground field**, of dimension at most that of the subvariety. -/
public theorem exists_isProper_range_eq_endProjectionImage (g : V →ₗ[k] V)
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ projectiveSpaceOfModule k V), IsProper f ∧
      Set.range f.base = endProjectionImage k V g C ∧
      topologicalKrullDim Z ≤ topologicalKrullDim C := by
  obtain ⟨S, ι, j, hι, hjι, hrange, hrj⟩ := exists_lift_closedImmersion_endDomain k V g hC hCg
  have h2 : IsProper ((j ≫ endProjection k V g) ≫ projectiveSpaceOfModuleToSpec k V) := by
    rw [Category.assoc, endProjection_comp_toSpec, ← Category.assoc, hjι]
    infer_instance
  refine ⟨S, j ≫ endProjection k V g,
    IsProper.of_comp _ (projectiveSpaceOfModuleToSpec k V), ?_, ?_⟩
  · rw [endProjectionImage, ← hrj]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  · refine Topology.IsInducing.topologicalKrullDim_le (f := fun x : S =>
      (⟨ι.base x, hrange ▸ Set.mem_range_self x⟩ : ↥C)) ?_
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    exact ι.isClosedEmbedding.isInducing

/-- **A closed point of the translate is the image of a closed point of the subvariety.** The
preimage of the point in the reduced closed subscheme on `C`, read inside `U(g)`, is a nonempty
closed subset of a Jacobson space, so it has a point closed in that subscheme; its image in
`𝐏(V)` is a closed point of `𝐏(V)` lying in `C`, and `r_g` sends it to the given point. -/
public theorem exists_isClosed_mem_endProjection_eq [IsAlgClosed k] (g : V →ₗ[k] V)
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    {y : projectiveSpaceOfModule k V} (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V)))
    (hymem : y ∈ endProjectionImage k V g C) :
    ∃ (x : projectiveSpaceOfModule k V) (w : (endDomain k V g).toScheme),
      x ∈ C ∧ IsClosed ({x} : Set (projectiveSpaceOfModule k V)) ∧
        (endDomain k V g).ι.base w = x ∧ (endProjection k V g).base w = y := by
  obtain ⟨S, ι, j, hι, hjι, hrange, hrj⟩ := exists_lift_closedImmersion_endDomain k V g hC hCg
  have hlft := locallyOfFiniteType_comp_toSpec k V ι
  have hjac : JacobsonSpace S :=
    LocallyOfFiniteType.jacobsonSpace (ι ≫ projectiveSpaceOfModuleToSpec k V)
  have hne : ((j ≫ endProjection k V g).base ⁻¹' {y}).Nonempty := by
    obtain ⟨z, hz⟩ : y ∈ Set.range (j ≫ endProjection k V g).base := by
      rw [endProjectionImage, ← hrj] at hymem
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] using hymem
    exact ⟨z, hz⟩
  obtain ⟨z, hzy, hzc⟩ :=
    exists_isClosed_singleton_mem hne (hy.preimage (j ≫ endProjection k V g).continuous)
  refine ⟨ι.base z, j.base z, ?_, ?_, ?_, hzy⟩
  · rw [← hrange]; exact Set.mem_range_self z
  · exact isClosed_singleton_image_of_isClosed_singleton ι
      (ι ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) rfl z hzc
  · rw [← hjι]; rfl

/-- **The translate of a closed subvariety contained in `U(g)` is closed.** -/
public theorem isClosed_endProjectionImage (g : V →ₗ[k] V)
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    IsClosed (endProjectionImage k V g C) := by
  obtain ⟨Z, f, hf, hrange, -⟩ := exists_isProper_range_eq_endProjectionImage k V g hC hCg
  rw [← hrange]
  exact f.isClosedMap.isClosed_range

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The preimage of a closed subset of `𝐏(V)` contained in `U(g)` has, inside `U(g)`, at most the
dimension of that subset. -/
public theorem topologicalKrullDim_preimage_endDomain_le (g : V →ₗ[k] V)
    (C : Set (projectiveSpaceOfModule k V)) :
    topologicalKrullDim ((endDomain k V g).ι.base ⁻¹' C) ≤ topologicalKrullDim C :=
  Topology.IsInducing.topologicalKrullDim_le
    (f := fun z : ↥((endDomain k V g).ι.base ⁻¹' C) =>
      (⟨(endDomain k V g).ι.base z.1, z.2⟩ : ↥C))
    (Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val
      ((endDomain k V g).ι.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal))

/-- **The dimension of the translate is at most that of the subvariety.** The translate is the
image of the preimage of `C` in `U(g)` under a morphism over the ground field, and dimension does
not grow along an image. -/
public theorem topologicalKrullDim_endProjectionImage_le (g : V →ₗ[k] V)
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    topologicalKrullDim (endProjectionImage k V g C) ≤ topologicalKrullDim C := by
  have hclosed := isClosed_endProjectionImage k V g hC hCg
  have hlft := locallyOfFiniteType_comp_toSpec k V (endDomain k V g).ι
  have hnoeth : NoetherianSpace ((endDomain k V g).toScheme) := by
    have : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
      LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
    have : CompactSpace (projectiveSpaceOfModule k V) :=
      QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k V)
    have : IsNoetherian (projectiveSpaceOfModule k V) := {}
    have : NoetherianSpace (projectiveSpaceOfModule k V) := inferInstance
    exact (endDomain k V g).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have h := topologicalKrullDim_closure_image_le k (endProjection k V g)
    ((endDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V) (endProjection_comp_toSpec k V g)
    (A := (endDomain k V g).ι.base ⁻¹' C) (hC.preimage (endDomain k V g).ι.continuous)
  rw [show closure ((endProjection k V g).base '' ((endDomain k V g).ι.base ⁻¹' C)) =
      endProjectionImage k V g C from hclosed.closure_eq] at h
  exact h.trans (topologicalKrullDim_preimage_endDomain_le k V g C)

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **The translate of an irreducible closed subvariety contained in `U(g)` is irreducible.** -/
public theorem isIrreducible_endProjectionImage (g : V →ₗ[k] V)
    {C : Set (projectiveSpaceOfModule k V)}
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    (hCirr : IsIrreducible C) :
    IsIrreducible (endProjectionImage k V g C) := by
  have hne : (C ∩ Set.range (endDomain k V g).ι.base).Nonempty := by
    obtain ⟨x, hx⟩ := hCirr.nonempty
    exact ⟨x, hx, by rw [Scheme.Opens.range_ι]; exact hCg hx⟩
  have hirrpre : IsIrreducible ((endDomain k V g).ι.base ⁻¹' C) :=
    hCirr.preimage (endDomain k V g).ι.isOpenEmbedding hne
  rw [endProjectionImage]
  exact hirrpre.image _ (Continuous.continuousOn (by fun_prop))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
