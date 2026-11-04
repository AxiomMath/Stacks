module

public import StacksFrontier.AlgebraicGeometry.Descent.PointSetCoverLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Representability from a covering by representable open subfunctors

Let `F` be a sheaf for the fppf topology of the big fppf site of a scheme `S`, and let
`k i : yoneda.obj (W i) ⟶ F` be a family of morphisms from representable presheaves, each a
representable open immersion, whose point sets cover the point space of `F`. Then `F` is
representable, provided the index type and the sizes of the `W i` stay below the site's cutoff.

This is the shape in which a geometric construction produces a Zariski covering: what such a
construction knows about its charts is that their *point sets* exhaust the point space, not that
the induced morphism out of the coproduct is locally surjective, which is what the glueing step
`AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le` asks for. The passage between the
two is `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints`,
which is stated for charts whose ranges are the open subfunctors cut out by their point sets;
this file supplies that identification for an arbitrary representable open immersion, so that
only the point-set covering has to be checked.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_isLocallySurjective`: a locally surjective morphism of
  presheaves is surjective on the point sets of Tag 03BU.
* `AlgebraicGeometry.Space.range_eq_openSubspaceOfPoints_of_isOpenImmersion`: the range of a
  representable open immersion from a representable presheaf is the open subspace cut out by its
  point set.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_isOpenImmersion`: **part (2) of Tag
  03BZ for representable open subfunctors.** A family of representable open immersions whose
  point sets cover induces a locally surjective morphism out of the coproduct.
* `AlgebraicGeometry.Space.isRepresentable_of_isOpenImmersion_cover`: **Tag 01JJ for the big fppf
  site of `S` in point-set form.** A sheaf covered by representable open subfunctors whose point
  sets exhaust its point space is representable.
* `AlgebraicGeometry.Space.isRepresentable_of_isOpenImmersion_cover_of_chart` is the same with
  the point-set covering tested against one locally surjective morphism, which is the shape a
  quotient construction supplies.

## Implementation notes

Part (2) of Tag 03BZ is not available for an arbitrary family of open subspaces: as
`StacksFrontier/AlgebraicGeometry/Spaces/OpenSubspaceCorrespondence.lean` records, it needs Tag 03H5
for the morphism out of a coproduct of open subspaces, which is not relatively representable
without Tag 02WO. For *representable* pieces no such input is needed, because
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints` argues
one test object at a time and never forms the coproduct of the subspaces.

The identification of the range with the open subspace cut out by the point set uses both halves
of part (1) of Tag 03BZ. A representable open immersion is a monomorphism, so
`CategoryTheory.Subfunctor.toRange` is an isomorphism onto its range; algebraicity and openness
of the inclusion of the range transport along it, which makes the range an *open subspace*, and
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset` then compares it with the subspace cut
out by the point set in one direction. The other direction is immediate and needs no openness:
every point of a section in the range of a morphism is in the image of that morphism on points.
Notably no hypothesis that the ambient presheaf is an algebraic space is used anywhere, which
matters because the intended application is to a quotient sheaf whose representability is the
conclusion.

Surjectivity on points from local surjectivity is proved from the same two geometric inputs the
representable case uses — joint surjectivity of a covering sieve on the points of the underlying
scheme, and the residue field at a point as an object of the site — and not from
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`, which would need the morphism to be
relatively representable.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A locally surjective morphism of presheaves is surjective on the point sets of Tag 03BU.**
No representability of the morphism or of either presheaf is needed, in contrast with
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`, which tests surjectivity after
every represented base change.

A point of the target is a section over the spectrum of a field inside the site. Its image sieve
is a covering sieve, and every covering sieve of the big fppf site over `S` is jointly surjective
on the points of the underlying scheme
(`AlgebraicGeometry.BigFppfOver.exists_mem_arrows_mem_range`), so some arrow of it carries a lift
of the section. The residue field at a point of that arrow's source is again an object of the
site, by `AlgebraicGeometry.Space.exists_fieldSpec_at_point`, and restricting the lift there
gives a field-valued point of the source whose image dominates the given point. -/
theorem isSurjective_of_isLocallySurjective {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    IsSurjective B S hS f := by
  intro y
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  have _ := hf
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj
      (FieldValuedPoint.siteObject B S hS G q)) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of q.carrier)))
  obtain ⟨c, g, ⟨t, ht⟩, z, -⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f
      (U := op (FieldValuedPoint.siteObject B S hS G q)) q.value) (Classical.arbitrary _)
  obtain ⟨Ω, instΩ, hΩ, ρ, -⟩ := exists_fieldSpec_at_point B c.left.2 z
  set W : BigFppfOver B S hS := Over.mk (⟨ρ ≫ c.hom.hom⟩ : B.obj hΩ ⟶ B.obj hS) with hW
  set σ : W ⟶ c := Over.homMk (⟨ρ⟩ : B.obj hΩ ⟶ c.left) (by ext; rfl) with hσ
  refine ⟨FieldValuedPoint.class B S hS F
      { carrier := Ω, contained := hΩ, toBase := ρ ≫ c.hom.hom, value := F.map σ.op t }, ?_⟩
  rw [pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G
    ⟨_, FieldValuedPoint.dominates_refl B S hS G _, ⟨σ ≫ g, ?_⟩⟩
  show G.map (σ ≫ g).op q.value = f.app _ (F.map σ.op t)
  rw [NatTrans.naturality_apply f σ.op t, ht, op_comp, G.map_comp, types_comp_apply]

/-- The range of a morphism from a representable presheaf is contained in the open subspace cut
out by its point set: every point of a section in the range is the image of a point of the
source. -/
theorem range_le_openSubspaceOfPoints_range {W : BigFppfOver B S hS} (k : yoneda.obj W ⟶ G) :
    Subfunctor.range k ≤
      openSubspaceOfPoints B S hS G (Set.range (pointsMap B S hS (yoneda.obj W) k)) := by
  intro T x hx
  obtain ⟨t, ht⟩ := hx
  rw [mem_openSubspaceOfPoints_iff]
  rintro y ⟨p, rfl⟩
  have hx' : yonedaEquiv.symm x = yonedaEquiv.symm t ≫ k := by
    rw [yonedaEquiv_symm_naturality_right, ht]
  rw [hx', pointsMap_comp_apply]
  exact ⟨_, rfl⟩

/-- **Stacks 03BZ, part (1), at a representable open immersion.** The range of a representable
open immersion from a representable presheaf is the open subspace cut out by its point set.

This is the hypothesis which
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints` asks
for, and it holds with no hypothesis on the ambient presheaf. -/
theorem range_eq_openSubspaceOfPoints_of_isOpenImmersion {W : BigFppfOver B S hS}
    (k : yoneda.obj W ⟶ G) (hk : IsOpenImmersion B S hS k) :
    Subfunctor.range k =
      openSubspaceOfPoints B S hS G (Set.range (pointsMap B S hS (yoneda.obj W) k)) := by
  have _ : Mono k := mono_of_presheaf_isOpenImmersion hk
  set e := asIso (Subfunctor.toRange k) with he
  have hιfac : e.inv ≫ k = (Subfunctor.range k).ι :=
    (Iso.inv_comp_eq e).2 (Subfunctor.toRange_ι k).symm
  have hι : IsOpenImmersion B S hS (Subfunctor.range k).ι := by
    rw [← hιfac]
    exact MorphismProperty.RespectsIso.precomp _ e.inv k hk
  have hspace : IsAlgebraicSpace B S hS (Subfunctor.range k).toFunctor :=
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W).of_iso e
  refine le_antisymm (range_le_openSubspaceOfPoints_range B S hS k) ?_
  refine le_of_range_pointsMap_ι_subset B S hS ⟨hspace, hι⟩ ?_
  rw [range_pointsMap_ι_openSubspaceOfPoints, range_pointsMap_ι_range]

/-- **Part (2) of Stacks 03BZ for representable open subfunctors.** A family of representable
open immersions into a presheaf on the big fppf site of `S` whose point sets cover the point
space of the target induces a locally surjective morphism out of the coproduct.

For an arbitrary family of open subspaces this implication is not available — it needs Tag 03H5
and, through it, Tag 02WO — but for representable pieces it follows from
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints`, which
tests one object of the site at a time and never forms the coproduct of the subspaces. -/
theorem isLocallySurjective_sigmaDesc_of_isOpenImmersion {ι : Type u}
    {W : ι → BigFppfOver B S hS} (k : ∀ i, yoneda.obj (W i) ⟶ G)
    (hk : ∀ i, IsOpenImmersion B S hS (k i))
    (hcov : ⋃ i, Set.range (pointsMap B S hS (yoneda.obj (W i)) (k i)) = Set.univ) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k) :=
  isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints B S hS _
    (fun i => isOpen_range_pointsMap_of_isOpenImmersion B S hS (k i) (hk i)) hcov k
    (fun i => range_eq_openSubspaceOfPoints_of_isOpenImmersion B S hS (k i) (hk i))

/-- **Tag 01JJ for the big fppf site of `S`, in point-set form.** A sheaf for the fppf topology
of the big fppf site of `S` which admits a family of representable open immersions whose point
sets cover its point space is representable, provided the index type has cardinality below the
site's cutoff and the sources have size uniformly below it.

This is `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le` with its local
surjectivity hypothesis replaced by the point-set covering, which is what a geometric
construction of the charts actually delivers. -/
theorem isRepresentable_of_isOpenImmersion_cover
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {ι : Type u} (hι : #ι < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    {W : ι → BigFppfOver B S hS}
    (hW : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ)
    (k : ∀ i, yoneda.obj (W i) ⟶ G) (hk : ∀ i, IsOpenImmersion B S hS (k i))
    (hcov : ⋃ i, Set.range (pointsMap B S hS (yoneda.obj (W i)) (k i)) = Set.univ) :
    G.IsRepresentable :=
  isRepresentable_of_zariskiCover_of_size_le B S hS hG hι hμ W hW k hk
    (isLocallySurjective_sigmaDesc_of_isOpenImmersion B S hS k hk hcov)

/-- **Tag 01JJ for the big fppf site of `S`, with the point-set covering tested on a chart.**
The same conclusion as `AlgebraicGeometry.Space.isRepresentable_of_isOpenImmersion_cover`, with
the point-set covering replaced by the containment of the point set of one locally surjective
morphism into the union of the point sets of the charts.

This is the form a quotient construction supplies: the canonical projection onto a quotient
sheaf is locally surjective, so it suffices to see that every point coming from the objects of
the relation already lies on one of the charts. -/
theorem isRepresentable_of_isOpenImmersion_cover_of_chart
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {ι : Type u} (hι : #ι < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    {W : ι → BigFppfOver B S hS}
    (hW : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ)
    (k : ∀ i, yoneda.obj (W i) ⟶ G) (hk : ∀ i, IsOpenImmersion B S hS (k i))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (chart : F ⟶ G)
    (hchart : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) chart)
    (hsub : Set.range (pointsMap B S hS F chart) ⊆
      ⋃ i, Set.range (pointsMap B S hS (yoneda.obj (W i)) (k i))) :
    G.IsRepresentable :=
  isRepresentable_of_isOpenImmersion_cover B S hS hG hι hμ hW k hk
    (Set.eq_univ_of_univ_subset
      (le_trans (le_of_eq (isSurjective_of_isLocallySurjective B S hS chart hchart).range_eq.symm)
        hsub))

end AlgebraicGeometry.Space

end

end
