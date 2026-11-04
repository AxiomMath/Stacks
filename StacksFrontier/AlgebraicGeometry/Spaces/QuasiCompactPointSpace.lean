module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# Quasi-compactness of an algebraic space is quasi-compactness of its point space

Tag 03E4 says that an algebraic space over a scheme `S` is quasi-compact, in the sense of Tag
03E3 — it receives a surjective étale morphism from a quasi-compact scheme of the site — if and
only if its space of points, with the topology of Tag 03BX, is quasi-compact.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.compactSpace_points_of_isQuasiCompactSpace`: the point space of a
  quasi-compact algebraic space is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_compactSpace_points`: an algebraic space with
  quasi-compact point space is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points` is Tag 03E4, the two
  together.

## Implementation notes

The point topology used is `AlgebraicGeometry.Space.pointTopology`, installed as a local
instance as elsewhere in this directory; all three clauses of the characterization of Tag 03BX
are available for it.

One direction is the source's: a surjective étale atlas by a quasi-compact scheme is surjective
on points by Tag 03H5 and continuous by clause (2) of Tag 03BX, and its source has quasi-compact
point space because that space is homeomorphic to the scheme by clause (1).

For the other direction the source refines a chosen atlas `U ⟶ X` to a quasi-compact open
`U' ⊆ U` which is still surjective on points. The refinement is carried out here by the
disjoint union of a finite subfamily of the affine open cover of `U`, which is what makes the
resulting object land in the size-bounded site: the images in `|X|` of the point sets of the
members of the affine cover of `U` are open, because `|U| ⟶ |X|` is open by clause (3) of Tag
03BX, and they cover `|X|` because the atlas is surjective on points; compactness of `|X|`
selects finitely many. Their disjoint union is affine, hence quasi-compact, and the size bound
is the one of Stacks 000R (2) for an at most countable coproduct, the summands being bounded by
Stacks 000R (3) as open subschemes of `U`.

That disjoint union is *not* surjective onto `U`, only onto `|X|`, so the construction is not
an instance of the affine refinement of Tag 03H6; what is needed and proved is surjectivity on
points of the composite, which Tag 03H5 turns back into the relatively representable
surjectivity that `AlgebraicGeometry.Space.IsQuasiCompactSpace` asks for.

## References

* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point space of a represented presheaf on the big fppf site of `S` is quasi-compact
when the representing scheme is, the two being homeomorphic by clause (1) of Tag 03BX. -/
theorem compactSpace_points_yoneda (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    CompactSpace (points B S hS (yoneda.obj U)) :=
  (schemePointsHomeomorph B S hS U).symm.compactSpace

/-- **Stacks 03E4, the forward implication.** The point space of a quasi-compact algebraic
space over `S` is quasi-compact.

An atlas as in Tag 03E3 is continuous on points by clause (2) of Tag 03BX and surjective on
points by Tag 03H5, and its source has quasi-compact point space by clause (1). -/
theorem compactSpace_points_of_isQuasiCompactSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (h : IsQuasiCompactSpace B S hS F) :
    CompactSpace (points B S hS F) := by
  obtain ⟨U, f, hcompact, hsurj, -⟩ := h
  exact @Function.Surjective.compactSpace _ _ _ _ _
    (continuous_pointsMap B S hS f) (@compactSpace_points_yoneda B S hS U hcompact)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF U f).1 hsurj)

/-- Finitely many members of the affine open cover of the source of an étale atlas which is
surjective on points have images covering a quasi-compact point space. -/
theorem exists_finset_affineOpenCover_points_cover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : CompactSpace (points B S hS F))
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) f))
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ σ : Finset ((BigFppfOver.toScheme B S hS).obj U).affineOpenCover.I₀,
      ∀ y, ∃ i ∈ σ, ∃ w, pointsToScheme B S hS U w ∈
        Set.range ⇑(((BigFppfOver.toScheme B S hS).obj U).affineOpenCover.f i) ∧
        pointsMap B S hS (yoneda.obj U) f w = y := by
  let 𝒜 := ((BigFppfOver.toScheme B S hS).obj U).affineOpenCover
  let O : 𝒜.I₀ → Set (points B S hS F) := fun i =>
    pointsMap B S hS (yoneda.obj U) f '' (pointsToScheme B S hS U ⁻¹' Set.range ⇑(𝒜.f i))
  have hOopen : ∀ i, IsOpen (O i) := fun i => by
    refine isOpenMap_pointsMap_of_presheafEtale B S hS f hetale _
      ((isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U _).mpr ?_)
    rw [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)]
    exact (𝒜.f i).opensRange.2
  have hOcover : (Set.univ : Set (points B S hS F)) ⊆ ⋃ i, O i := fun y _ => by
    obtain ⟨w, rfl⟩ := hsurj y
    exact Set.mem_iUnion.2 ⟨𝒜.idx (pointsToScheme B S hS U w), ⟨w, 𝒜.covers _, rfl⟩⟩
  obtain ⟨σ, hσ⟩ := (@isCompact_univ _ (pointTopology B S hS F) h).elim_finite_subcover
    O hOopen hOcover
  refine ⟨σ, fun y => ?_⟩
  obtain ⟨i, hi, w, hw, hwq⟩ := Set.mem_iUnion₂.1 (hσ (Set.mem_univ y))
  exact ⟨i, hi, w, hw, hwq⟩

/-- Precomposing a relatively étale map out of a represented presheaf with the Yoneda image of
a morphism of the site that is étale on schemes gives an étale map. -/
theorem isEtale_yoneda_map_comp_of_presheafEtale {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (hg : Etale ((BigFppfOver.toScheme B S hS).map g)) {f : yoneda.obj U ⟶ F}
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsEtale B S hS (yoneda.map g ≫ f) := by
  let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have _ := etale_isStableUnderComposition.{u}
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : Pe.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have _ : Pe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : (MorphismProperty.presheaf Pe).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  exact fun W φ hφ => MorphismProperty.comp_mem _ φ (yoneda.map g ≫ f) hφ
    (MorphismProperty.comp_mem _ (yoneda.map g) f
      ((MorphismProperty.relative_map_iff (P := Pe) (F := yoneda)).2 hg) hf)

/-- **Stacks 03E4, the reverse implication.** An algebraic space over `S` whose point space is
quasi-compact is quasi-compact.

The disjoint union of a finite subfamily of the affine open cover of a chosen atlas, chosen so
that the images of the summands cover the point space, is an affine scheme of the site which is
still surjective on points. -/
theorem isQuasiCompactSpace_of_compactSpace_points
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (h : CompactSpace (points B S hS F)) :
    IsQuasiCompactSpace B S hS F := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  let G := BigFppfOver.toScheme B S hS
  let T : Scheme.{u} := G.obj U
  let 𝒜 : T.AffineOpenCover := T.affineOpenCover
  obtain ⟨σ, hσ⟩ := exists_finset_affineOpenCover_points_cover B S hS h f
    ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF U f).1 hsurj) hetale
  -- The disjoint union of the chosen finitely many affine summands.
  let Y : {i // i ∈ σ} → Scheme.{u} := fun i => Spec (𝒜.X i.1)
  let A : Scheme.{u} := ∐ Y
  let a : A ⟶ T := Sigma.desc fun i => 𝒜.f i.1
  have hAsmall : A.size < B.cutoff :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Y
      fun i => Scheme.size_lt_of_isOpenImmersion (𝒜.f i.1) U.left.property
  let a' : B.obj hAsmall ⟶ U.left := B.inclusion.preimage
    (show B.inclusion.obj (B.obj hAsmall) ⟶ B.inclusion.obj U.left from a)
  let V : BigFppfOver B S hS := Over.mk (a' ≫ U.hom)
  let g : V ⟶ U := Over.homMk a'
  have hGg : G.map g = a := B.inclusion.map_preimage _
  -- `a` is étale, being the disjoint union of open immersions.
  have hge : Etale (G.map g) := by
    rw [hGg]
    have : IsZariskiLocalAtSource @Etale :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
  -- The composite atlas is surjective on points, by the choice of the finite subfamily.
  have hpt : Function.Surjective (pointsMap B S hS (yoneda.obj V) (yoneda.map g ≫ f)) := by
    intro y
    obtain ⟨i, hiσ, w, ⟨x, hx⟩, hwq⟩ := hσ y
    obtain ⟨v, hv⟩ := surjective_pointsToScheme B S hS V
      (show G.obj V from (Sigma.ι Y ⟨i, hiσ⟩) x)
    refine ⟨v, ?_⟩
    have hgv : pointsMap B S hS (yoneda.obj V) (yoneda.map g) v = w := by
      refine injective_pointsToScheme B S hS U ?_
      rwa [pointsToScheme_pointsMap_yoneda, hv, hGg, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    rwa [pointsMap_comp_apply, hgv]
  have _ : ∀ i, IsAffine (Y i) := fun i => isAffine_Spec _
  have _ : IsAffine A := inferInstance
  exact ⟨V, yoneda.map g ≫ f, inferInstanceAs (CompactSpace A),
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF V (yoneda.map g ≫ f)).2 hpt,
    isEtale_yoneda_map_comp_of_presheafEtale B S hS g hge hetale⟩

/-- **Stacks 03E4.** An algebraic space over `S` is quasi-compact if and only if its space of
points is quasi-compact. -/
@[stacks 03E4]
theorem isQuasiCompactSpace_iff_compactSpace_points
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    IsQuasiCompactSpace B S hS F ↔ CompactSpace (points B S hS F) :=
  ⟨compactSpace_points_of_isQuasiCompactSpace B S hS hF,
    isQuasiCompactSpace_of_compactSpace_points B S hS hF⟩

end AlgebraicGeometry.Space

end
