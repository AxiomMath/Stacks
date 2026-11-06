module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas

/-!
# Zariski local quasi-separatedness and quasi-compact affine étale charts

For an algebraic space `F` over a scheme `S`, Zariski local quasi-separatedness over `S`,
absolute Zariski local quasi-separatedness, and the existence of a Zariski covering of `F` by
open subspaces each of which carries a quasi-compact surjective étale atlas from an affine
scheme are all equivalent; and the affine schemes may in addition be chosen to map into
affine opens of `S`. This is Stacks 03W7.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineQuasiCompactEtaleAtlas` and
  `AlgebraicGeometry.Space.HasAffineQuasiCompactEtaleAtlasIntoAffineBase` are the atlas data
  of conditions (3) and (4) for a single presheaf, and
  `AlgebraicGeometry.Space.HasAffineQuasiCompactEtaleCover`,
  `AlgebraicGeometry.Space.HasAffineQuasiCompactEtaleCoverIntoAffineBase` the two conditions
  themselves.

## Main results

* `AlgebraicGeometry.Space.isZariskiLocallyQuasiSeparatedOver_tfae`: **Stacks 03W7**, the four
  equivalent conditions.
* `AlgebraicGeometry.Space.isOpenSubspace_range_of_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.isOpenSubspace_range_ι_comp`: the range of an open immersion with
  algebraic source is an open subspace, and so is the image in `F` of an open subspace of an
  open subspace of `F`.
* `AlgebraicGeometry.Space.isZariskiCover_range_ι_comp`: refining each member of a Zariski
  covering by a Zariski covering of it gives a Zariski covering.
* `AlgebraicGeometry.Space.isQuasiSeparatedOver_relocalizeRestrict` and
  `AlgebraicGeometry.Space.isLocallySurjective_relocalizeRestrict_map`: restriction of the
  base scheme preserves quasi-separatedness over the base and local surjectivity.
* `CategoryTheory.OverShriek.mono_relocalizeAdjunction_unit_app`: the unit of the
  relocalization adjunction is a monomorphism.
* `CategoryTheory.Subfunctor.whiskerLeft`: the restriction of a subfunctor along
  precomposition with a functor.

## Implementation notes

The implications among (1), (3) and (4) are the source's, with Stacks 03FY
(`AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas`) producing the covering
and `StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleAtlasQuasiSeparated.lean` comparing
quasi-separatedness over `S` with quasi-compactness of an affine étale atlas.

The source deduces (2) from the observation that condition (3) does not mention the base
scheme. Over a fixed big fppf site the two readings live on different slices, so each
direction is proved separately. From (3) to (2) the atlas of a member of the covering is fed
to Stacks 07S4
(`AlgebraicGeometry.Space.isQuasiSeparated_of_etaleAtlas_quasiCompact_projection`), which
already crosses to the terminal scheme, and the covering is reassembled by Stacks 03KE
(`AlgebraicGeometry.Space.isAbsolutelyZariskiLocallyQuasiSeparated_of_isZariskiCover`). From
(2) to (1) the covering is transported back along the unit `F ⟶ j^{-1} j_! F` of the
relocalization adjunction: the preimage of a member of the covering is an open subspace of
`F` because it is a base change of one, quasi-separated over `S` because it is a subobject of
the restriction of a quasi-separated presheaf, and the preimages still cover because the unit
is compatible with the covering sieves.

## References

* [Stacks Project, Tag 03W7](https://stacks.math.columbia.edu/tag/03W7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Subfunctor

/-- The restriction of a subfunctor of `F` along precomposition with a functor `H`: its
sections over an object `U` are the sections of the subfunctor over `H.obj U`. -/
def whiskerLeft {C : Type*} [Category* C] {D : Type*} [Category* D] (H : D ⥤ C)
    {F : C ⥤ Type*} (G : Subfunctor F) : Subfunctor (H ⋙ F) where
  obj U := G.obj (H.obj U)
  map i := G.map (H.map i)

/-- The sections of `whiskerLeft H G` over `U` are the sections of `G` over `H.obj U`. -/
@[simp]
theorem whiskerLeft_obj {C : Type*} [Category* C] {D : Type*} [Category* D] (H : D ⥤ C)
    {F : C ⥤ Type*} (G : Subfunctor F) (U : D) :
    (whiskerLeft H G).obj U = G.obj (H.obj U) := rfl

/-- The inclusion of `whiskerLeft H G` into `H ⋙ F` is the whiskering of the inclusion of `G`
along `H`. -/
theorem whiskerLeft_ι {C : Type*} [Category* C] {D : Type*} [Category* D] (H : D ⥤ C)
    {F : C ⥤ Type*} (G : Subfunctor F) :
    (whiskerLeft H G).ι = Functor.whiskerLeft H G.ι := rfl

end CategoryTheory.Subfunctor

namespace CategoryTheory.OverShriek

/-- **The unit of the relocalization adjunction is a monomorphism.** A section of
`j^{-1} j_! G` over `W` is a pair consisting of a factorization of the structure morphism of
`W` and a section of `G` over it, and the unit sends a section to the pair with the
tautological factorization, so it is injective on sections. -/
@[sga "4 I 5.14" "special case"]
theorem mono_relocalizeAdjunction_unit_app {C : Type u} [Category* C] {X Y : C} (g : Y ⟶ X)
    (G : (Over Y)ᵒᵖ ⥤ Type _) : Mono ((relocalizeAdjunction g).unit.app G) := by
  have hunit : (relocalizeAdjunction g).unit.app G =
      relocalizeToRestricted g (𝟙 ((relocalizePresheafFunctor g).obj G)) := by
    simp [relocalizeAdjunction]
  rw [NatTrans.mono_iff_mono_app]
  intro A
  rw [mono_iff_injective]
  intro x y h
  rw [hunit] at h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Images of open subspaces -/

/-- The range of an open immersion whose source is an algebraic space over `S` is an open
subspace: the source is isomorphic to the range, and the inclusion of the range is the open
immersion read through that isomorphism. -/
theorem isOpenSubspace_range_of_isAlgebraicSpace
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ G) (hf : IsOpenImmersion B S hS f) :
    IsOpenSubspace B S hS (Subfunctor.range f) := by
  have _ : Mono f := mono_of_presheaf_isOpenImmersion hf
  have hfac : (asIso (Subfunctor.toRange f)).inv ≫ f = (Subfunctor.range f).ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι f).symm
  refine ⟨hF.of_iso (asIso (Subfunctor.toRange f)), ?_⟩
  rw [← hfac]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hf

/-- The image in `F` of an open subspace of an open subspace of `F` is an open subspace of
`F`: the composite of the two inclusions is an open immersion with algebraic source. -/
theorem isOpenSubspace_range_ι_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U)
    (V : Subfunctor U.toFunctor) (hV : IsOpenSubspace B S hS V) :
    IsOpenSubspace B S hS (Subfunctor.range (V.ι ≫ U.ι)) :=
  isOpenSubspace_range_of_isAlgebraicSpace B S hS hV.1 _
    (isOpenImmersion_comp B S hS V.ι U.ι hV.2 hU.2)

/-- **Refining a Zariski covering.** If the open subspaces `U i` cover `F` and for each `i`
the open subspaces `V i j` cover `U i`, then the images of the `V i j` in `F` cover `F`: a
point of `F` comes from some `U i`, and that point of `U i` comes from some `V i j`. -/
theorem isZariskiCover_range_ι_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (I : Type u) (U : I → Subfunctor F)
    (hU : IsZariskiCover B S hS I U) (J : I → Type u)
    (V : ∀ i, J i → Subfunctor (U i).toFunctor)
    (hV : ∀ i, IsZariskiCover B S hS (J i) (V i)) :
    IsZariskiCover B S hS (Σ i, J i)
      (fun ij ↦ Subfunctor.range ((V ij.1 ij.2).ι ≫ (U ij.1).ι)) := by
  classical
  set W : (Σ i, J i) → Subfunctor F := fun ij ↦
    Subfunctor.range ((V ij.1 ij.2).ι ≫ (U ij.1).ι)
  have hWopen : ∀ ij, IsOpenSubspace B S hS (W ij) := fun ij ↦
    isOpenSubspace_range_ι_comp B S hS (U ij.1) (hU.1 ij.1) (V ij.1 ij.2) ((hV ij.1).1 ij.2)
  refine (isZariskiCover_iff_iUnion_points B S hS F hF (Σ i, J i) W hWopen).2 ?_
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hUpts := (isZariskiCover_iff_iUnion_points B S hS F hF I U hU.1).mp hU
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (hUpts ▸ Set.mem_univ x)
  have hVpts := (isZariskiCover_iff_iUnion_points B S hS (U i).toFunctor (hU.1 i).1
    (J i) (V i) (hV i).1).mp (hV i)
  obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp (hVpts ▸ Set.mem_univ y)
  refine Set.mem_iUnion.mpr ⟨⟨i, j⟩,
    pointsMap B S hS (V i j).toFunctor (Subfunctor.toRange ((V i j).ι ≫ (U i).ι)) z, ?_⟩
  calc pointsMap B S hS (W ⟨i, j⟩).toFunctor (W ⟨i, j⟩).ι
        (pointsMap B S hS (V i j).toFunctor (Subfunctor.toRange ((V i j).ι ≫ (U i).ι)) z)
      = pointsMap B S hS (V i j).toFunctor
          (Subfunctor.toRange ((V i j).ι ≫ (U i).ι) ≫ (W ⟨i, j⟩).ι) z := by
        rw [pointsMap_comp]; rfl
    _ = pointsMap B S hS (V i j).toFunctor ((V i j).ι ≫ (U i).ι) z := by
        rw [Subfunctor.toRange_ι]
    _ = pointsMap B S hS (U i).toFunctor (U i).ι
          (pointsMap B S hS (V i j).toFunctor (V i j).ι z) := by
        rw [pointsMap_comp]; rfl
    _ = x := by rw [hz, hy]

/-! ### Restriction of the base scheme -/

section Restrict

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **Restriction of the base scheme preserves quasi-separatedness over the base.**
Restriction preserves fibre products, so it carries the absolute diagonal of a presheaf over
`S'` to the absolute diagonal of its restriction, up to the product comparison. -/
theorem isQuasiSeparatedOver_relocalizeRestrict
    (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) (hF : IsQuasiSeparatedOver B S' hS' F) :
    IsQuasiSeparatedOver B S hS ((OverShriek.relocalizeRestrict g).obj F) := by
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hrestrict := OverShriek.relative_relocalizeRestrict_map g
    (inverseImage_restrictReindexSnd B S S' hS hS' g
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})) hF
  have heq : (OverShriek.relocalizeRestrict g).map (diag F) ≫
      prodComparison (OverShriek.relocalizeRestrict g) F F =
        diag ((OverShriek.relocalizeRestrict g).obj F) := by
    refine prod.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, prodComparison_fst, prodComparison_snd, ← Functor.map_comp,
        prod.lift_fst, prod.lift_snd] <;>
      exact (OverShriek.relocalizeRestrict g).map_id F
  have hdiag := MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (prodComparison (OverShriek.relocalizeRestrict g) F F) _ hrestrict
  rwa [heq] at hdiag

/-- **Restriction of the base scheme preserves local surjectivity.** The image sieve of the
restricted morphism is the pullback of the image sieve along the localization functor, and
the covering sieves of the two slices correspond under `CategoryTheory.Sieve.overEquiv`. -/
theorem isLocallySurjective_relocalizeRestrict_map
    {F G : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S' hS') f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((OverShriek.relocalizeRestrict g).map f) := by
  constructor
  intro A x
  change (Presheaf.imageSieve f x).functorPullback (Over.map g) ∈
    B.topology.over (B.obj hS) A
  rw [B.topology.mem_over_iff, Sieve.overEquiv_functorPullback_map]
  exact (B.topology.mem_over_iff _).mp (hf.imageSieve_mem x)

end Restrict

/-! ### The four conditions of Stacks 03W7 -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03W7, the atlas data of condition (3).** A presheaf on the big fppf site of `S`
admits a quasi-compact surjective étale atlas by an affine scheme. -/
abbrev HasAffineQuasiCompactEtaleAtlas (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ G),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
    IsQuasiCompact B S hS f ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f

/-- **Stacks 03W7, the atlas data of condition (4).** A presheaf on the big fppf site of `S`
admits a quasi-compact surjective étale atlas by an affine scheme which maps into an affine
open of `S`. -/
abbrev HasAffineQuasiCompactEtaleAtlasIntoAffineBase
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ G) (V : S.Opens),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
    IsAffineOpen V ∧
    (∀ t : (BigFppfOver.toScheme B S hS).obj U, (B.inclusion.map U.hom) t ∈ V) ∧
    IsQuasiCompact B S hS f ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f

/-- **Stacks 03W7, condition (3).** There is a Zariski covering of `F` by open subspaces each
of which admits a quasi-compact surjective étale atlas by an affine scheme. -/
abbrev HasAffineQuasiCompactEtaleCover (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (I : Type u) (X : I → Subfunctor F), IsZariskiCover B S hS I X ∧
    ∀ i, HasAffineQuasiCompactEtaleAtlas B S hS (X i).toFunctor

/-- **Stacks 03W7, condition (4).** There is a Zariski covering of `F` by open subspaces each
of which admits a quasi-compact surjective étale atlas by an affine scheme mapping into an
affine open of `S`. -/
abbrev HasAffineQuasiCompactEtaleCoverIntoAffineBase
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (I : Type u) (X : I → Subfunctor F), IsZariskiCover B S hS I X ∧
    ∀ i, HasAffineQuasiCompactEtaleAtlasIntoAffineBase B S hS (X i).toFunctor

/-- Condition (4) implies condition (3): forget the affine open of the base. -/
theorem hasAffineQuasiCompactEtaleCover_of_hasAffineQuasiCompactEtaleCoverIntoAffineBase
    (h : HasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS F) :
    HasAffineQuasiCompactEtaleCover B S hS F := by
  obtain ⟨I, X, hcover, hdata⟩ := h
  refine ⟨I, X, hcover, fun i ↦ ?_⟩
  obtain ⟨U, f, _, hU, _, _, hqc, hsurj, hetale⟩ := hdata i
  exact ⟨U, f, hU, hqc, hsurj, hetale⟩

/-- **Assembling a condition-(4) covering.** Refine a covering `X` of `F` by the covering of
Stacks 03FY of each member. If the atlas of every member of the refinement is quasi-compact,
the images of the refined members in `F` form a condition-(4) covering of `F`. -/
private theorem hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_isQuasiCompact
    (hF : IsAlgebraicSpace B S hS F) (I : Type u) (X : I → Subfunctor F)
    (hX : IsZariskiCover B S hS I X)
    (hqc : ∀ i (Y : Subfunctor (X i).toFunctor), IsAlgebraicSpace B S hS Y.toFunctor →
      ∀ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ Y.toFunctor) (V : S.Opens),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) f →
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) f →
        IsAffineOpen V → (∀ t : (BigFppfOver.toScheme B S hS).obj U,
          (B.inclusion.map U.hom) t ∈ V) → IsQuasiCompact B S hS f) :
    HasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS F := by
  classical
  choose J Y hYcover hYdata using fun i ↦
    exists_zariski_cover_affine_etale_atlas B S hS (X i).toFunctor (hX.1 i).1
  refine ⟨Σ i, J i, fun ij ↦ Subfunctor.range ((Y ij.1 ij.2).ι ≫ (X ij.1).ι),
    isZariskiCover_range_ι_comp B S hS hF I X hX J Y hYcover, fun ij ↦ ?_⟩
  obtain ⟨U, f, V, hU, hsurj, hetale, hV, hbase⟩ := hYdata ij.1 ij.2
  have _ : Mono ((Y ij.1 ij.2).ι ≫ (X ij.1).ι) := inferInstance
  set e : (Y ij.1 ij.2).toFunctor ≅
      (Subfunctor.range ((Y ij.1 ij.2).ι ≫ (X ij.1).ι)).toFunctor :=
    asIso (Subfunctor.toRange ((Y ij.1 ij.2).ι ≫ (X ij.1).ι))
  have hmapsTo := hbase U (f.app (Opposite.op U) (𝟙 U))
  exact ⟨U, f ≫ e.hom, V, hU, hV, hmapsTo,
    IsQuasiCompact.postcomp_iso B S hS f e
      (hqc ij.1 (Y ij.1 ij.2) ((hYcover ij.1).1 ij.2).1 U f V hU hsurj hetale hV hmapsTo),
    MorphismProperty.RespectsIso.postcomp _ e.hom f hsurj,
    MorphismProperty.RespectsIso.postcomp _ e.hom f hetale⟩

/-- **Stacks 03W7, (1) implies (4).** An algebraic space which is Zariski locally
quasi-separated over `S` has a Zariski covering by open subspaces with quasi-compact
surjective étale atlases by affine schemes mapping into affine opens of `S`.

Refine the covering by quasi-separated open subspaces given by condition (1) with the
covering of Stacks 03FY: each member of the refinement is quasi-separated over `S`, being a
subfunctor of a quasi-separated one, and its affine étale atlas is therefore quasi-compact. -/
theorem hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_isZariskiLocallyQuasiSeparatedOver
    (hF : IsAlgebraicSpace B S hS F)
    (h : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    HasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS F := by
  obtain ⟨I, X, hXcover, hXqs⟩ := h
  exact hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_isQuasiCompact B S hS hF I X hXcover
    fun i Y hY U f V hU hsurj hetale hV hbase ↦
      isQuasiCompact_of_isQuasiSeparatedOver_affineEtaleAtlas B S hS hY U f hU
        (isAffine_prod_of_mapsTo_isAffineOpen B S hS U hU V hV hbase)
        (isQuasiSeparatedOver_subfunctor B S hS (hXqs i) Y) hsurj hetale

/-- **Stacks 03W7, (3) implies (4).** Refine a condition-(3) covering with the covering of
Stacks 03FY, whose members map into affine opens of `S`. The atlas of a member of the
refinement is quasi-compact because its composite with the inclusion of the member of the
original covering is, that inclusion being a monomorphism. -/
theorem hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_hasAffineQuasiCompactEtaleCover
    (hF : IsAlgebraicSpace B S hS F) (h : HasAffineQuasiCompactEtaleCover B S hS F) :
    HasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS F := by
  obtain ⟨I, X, hXcover, hXdata⟩ := h
  refine hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_isQuasiCompact B S hS hF I X hXcover
    fun i Y _ U f _ hU _ _ _ _ ↦ ?_
  obtain ⟨U₀, q₀, hU₀, hq₀, hq₀surj, hq₀etale⟩ := hXdata i
  exact IsQuasiCompact.of_comp_mono B S hS f Y.ι
    (isQuasiCompact_of_isAffine_of_isQuasiCompact_atlas B S hS (hXcover.1 i).1
      U₀ q₀ hU₀ hq₀ hq₀surj hq₀etale U (f ≫ Y.ι) hU)

/-- **Stacks 03W7, (4) implies (1).** Each member of a condition-(4) covering is
quasi-separated over `S`, its affine étale atlas being quasi-compact and its self-product
affine; so the covering witnesses Zariski local quasi-separatedness over `S`. -/
theorem isZariskiLocallyQuasiSeparatedOver_of_hasAffineQuasiCompactEtaleCoverIntoAffineBase
    (h : HasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS F) :
    IsZariskiLocallyQuasiSeparatedOver B S hS F := by
  obtain ⟨I, X, hcover, hdata⟩ := h
  refine ⟨I, X, hcover, fun i ↦ ?_⟩
  obtain ⟨U, f, V, hU, hV, hbase, hqc, hsurj, hetale⟩ := hdata i
  exact isQuasiSeparatedOver_of_isQuasiCompact_affineEtaleAtlas B S hS (hcover.1 i).1 U f hU
    (isAffine_prod_of_mapsTo_isAffineOpen B S hS U hU V hV hbase) hqc hsurj hetale

set_option synthInstance.maxHeartbeats 200000 in
/-- **Stacks 03W7, (3) implies (2).** Each member of a condition-(3) covering is
quasi-separated by Stacks 07S4: its atlas has affine, hence quasi-separated, source, and the
kernel-pair projection is quasi-compact because the atlas is. A quasi-separated algebraic
space is Zariski locally quasi-separated by Stacks 03JX, and Zariski local quasi-separatedness
is inherited from a Zariski covering by Stacks 03KE. -/
theorem isAbsolutelyZariskiLocallyQuasiSeparated_of_hasAffineQuasiCompactEtaleCover
    (hZ : B.Contains (⊤_ Scheme.{u})) (h : HasAffineQuasiCompactEtaleCover B S hS F) :
    IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ F := by
  obtain ⟨I, X, hcover, hdata⟩ := h
  refine isAbsolutelyZariskiLocallyQuasiSeparated_of_isZariskiCover B S hS F hZ I X hcover
    fun i ↦ ?_
  obtain ⟨U, f, hU, hqc, hsurj, hetale⟩ := hdata i
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  refine isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS
    (X i).toFunctor hZ (hcover.1 i).1 ?_
  refine isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ (X i).toFunctor
    (hcover.1 i).1 ⟨U, f, inferInstance, hsurj, hetale, Or.inr ?_⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f f)
    (presheafQuasiCompact_of_isQuasiCompact_affineEtaleAtlas B S hS (hcover.1 i).1 U f hU
      hqc hsurj hetale)

/-- **Stacks 03W7, (2) implies (1).** Transport a Zariski covering of the view of `F` over
the terminal scheme by quasi-separated open subspaces back along the unit
`η : F ⟶ j^{-1} j_! F` of the relocalization adjunction. The preimage along `η` of a member
of the covering is an open subspace of `F`, being a base change of the restriction of that
member; it is quasi-separated over `S` because it is a subobject of that restriction, which
is quasi-separated over `S`; and the preimages still cover `F` because the covering sieves of
the two slices correspond. -/
theorem isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyZariskiLocallyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (hF : IsAlgebraicSpace B S hS F)
    (h : IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ F) :
    IsZariskiLocallyQuasiSeparatedOver B S hS F := by
  classical
  set b : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  set L := OverShriek.relocalizePresheafFunctor b
  set R := OverShriek.relocalizeRestrict b
  obtain ⟨I, U, hcover, hqs⟩ := h
  set η := (OverShriek.relocalizeAdjunction b).unit.app F
  have _ : Mono η := OverShriek.mono_relocalizeAdjunction_unit_app b F
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- the restrictions of the members of the covering, and their preimages in `F`
  set W : I → Subfunctor (R.obj (L.obj F)) := fun i ↦
    Subfunctor.whiskerLeft (Over.map b).op (U i)
  set V : I → Subfunctor F := fun i ↦ (W i).preimage η
  have hLalg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (L.obj F) :=
    isAlgebraicSpace_relocalize B ⟨S, hS⟩ ⟨⊤_ Scheme.{u}, hZ⟩ b F hF
  have hRalg : IsAlgebraicSpace B S hS (R.obj (L.obj F)) :=
    isAlgebraicSpace_relocalizeRestrict B S (⊤_ Scheme.{u}) hS hZ b (L.obj F) hLalg
  have hWalg : ∀ i, IsAlgebraicSpace B S hS (W i).toFunctor := fun i ↦
    isAlgebraicSpace_relocalizeRestrict B S (⊤_ Scheme.{u}) hS hZ b (U i).toFunctor
      (hcover.1 i).1
  have hWopen : ∀ i, IsOpenImmersion B S hS (W i).ι := fun i ↦
    OverShriek.relative_relocalizeRestrict_map b
      (inverseImage_restrictReindexSnd B S (⊤_ Scheme.{u}) hS hZ b
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      (hcover.1 i).2
  have hpb : ∀ i, IsPullback ((W i).fromPreimage η) (V i).ι (W i).ι η := fun i ↦
    Subfunctor.isPullback_fromPreimage (W i) η
  have hVopen : ∀ i, IsOpenSubspace B S hS (V i) := fun i ↦
    ⟨(isAlgebraicSpace_pullback B S hS (W i).ι η (hWalg i) hF hRalg).of_iso
        (hpb i).isoPullback.symm,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb i) (hWopen i)⟩
  refine ⟨I, V, ⟨hVopen, ?_⟩, fun i ↦ ?_⟩
  · -- the preimages still cover
    have hd := isLocallySurjective_relocalizeRestrict_map B S hS (⊤_ Scheme.{u}) hZ b
      (Sigma.desc fun i ↦ (U i).ι) hcover.2
    refine ⟨fun {A} x => (BigFppfOver.topology B S hS).superset_covering ?_
      (hd.imageSieve_mem (η.app (Opposite.op A) x))⟩
    rintro T k ⟨y, hy⟩
    obtain ⟨⟨i⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves
        ((evaluation (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ (Type u)).obj
          (Opposite.op ((Over.map b).obj T)))
        (colimit.isColimit (Discrete.functor fun i ↦ (U i).toFunctor))) y
    have hnat : η.app (Opposite.op T) (F.map k.op x) =
        ((R.obj (L.obj F)).map k.op) (η.app (Opposite.op A) x) :=
      η.naturality_apply k.op x
    have hz : (U i).ι.app (Opposite.op ((Over.map b).obj T)) z =
        η.app (Opposite.op T) (F.map k.op x) := by
      rw [hnat]
      exact (congrArg (fun m ↦ m.app (Opposite.op ((Over.map b).obj T)) z)
        (Sigma.ι_desc (fun i ↦ (U i).ι) i)).symm.trans hy
    let z' : (V i).toFunctor.obj (Opposite.op T) :=
      ⟨F.map k.op x, by
        change η.app (Opposite.op T) (F.map k.op x) ∈ (U i).obj _
        rw [← hz]
        exact z.property⟩
    exact ⟨(Sigma.ι (fun i ↦ (V i).toFunctor) i).app (Opposite.op T) z',
      congrArg (fun m ↦ m.app (Opposite.op T) z') (Sigma.ι_desc (fun i ↦ (V i).ι) i)⟩
  · -- each preimage is quasi-separated over `S`
    have _ : Mono ((W i).fromPreimage η) := (hpb i).mono_fst_of_mono
    exact isQuasiSeparatedOver_of_mono B S hS ((W i).fromPreimage η)
      (isQuasiSeparatedOver_relocalizeRestrict B S hS (⊤_ Scheme.{u}) hZ b
        (U i).toFunctor (hqs i))

/-- **Stacks 03W7.** For an algebraic space over a scheme `S`, Zariski local
quasi-separatedness over `S`, absolute Zariski local quasi-separatedness, and the existence of
a Zariski covering by open subspaces carrying quasi-compact surjective étale atlases by affine
schemes — with or without the requirement that those affine schemes map into affine opens of
`S` — are equivalent. -/
@[stacks 03W7]
theorem isZariskiLocallyQuasiSeparatedOver_tfae
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    List.TFAE
      [IsZariskiLocallyQuasiSeparatedOver B S hS X,
        IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X,
        HasAffineQuasiCompactEtaleCover B S hS X,
        HasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS X] := by
  tfae_have 1 → 4 :=
    hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_isZariskiLocallyQuasiSeparatedOver
      B S hS hX
  tfae_have 4 → 1 :=
    isZariskiLocallyQuasiSeparatedOver_of_hasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS
  tfae_have 3 → 4 :=
    hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_hasAffineQuasiCompactEtaleCover B S hS hX
  tfae_have 4 → 3 :=
    hasAffineQuasiCompactEtaleCover_of_hasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS
  tfae_have 3 → 2 :=
    isAbsolutelyZariskiLocallyQuasiSeparated_of_hasAffineQuasiCompactEtaleCover B S hS hZ
  tfae_have 2 → 1 :=
    isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyZariskiLocallyQuasiSeparated
      B S hS hZ hX
  tfae_finish

end AlgebraicGeometry.Space

end
