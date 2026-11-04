module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ResidueFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Morphisms of algebraic spaces whose fibres are affine spaces

In Situation 0EDT let `f : X → Y` be a morphism of algebraic spaces over the base with `Y/B`
good. The hypothesis of Stacks 0ERG on `f` is that for every `y ∈ |Y|` the fibre `X_y` of `f`
over `Spec κ(y) → Y` is isomorphic to `𝐀^r_{κ(y)}`, where `Spec κ(y) → Y` is the monomorphism
from the spectrum of the residue field of Stacks 0ENW
(`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueFieldMorphism`). This file
formulates that hypothesis and shows that it is inherited by the base change of `f` along a
monomorphism `g : Y' → Y` of good spaces, in particular along the inclusion of a closed
subspace: the residue field of `Y'` at `y'` is the residue field of `Y` at `g(y')`, by the
uniqueness clause of Stacks 0ENW, so the fibres of the base change are fibres of `f`.

It also records the other properties of the base change of `f` along a closed subspace
`Z ⊆ Y` used in Stacks 0ERG: the inverse image `f^{-1}(Z)` is a closed subspace of `X`, so it is
good, and `f^{-1}(Z) → Z` is flat of relative dimension `r` (Stacks 0EPD) and quasi-compact
(Stacks 03HF) when `f` is.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineSpaceFibres`: every fibre of `f` over the spectrum of a
  residue field `κ(y)` is affine `r`-space over `κ(y)`.

## Main results

* `AlgebraicGeometry.Space.HasAffineSpaceFibres.of_isPullback`: the fibre hypothesis is
  inherited by base change along a monomorphism.
* `AlgebraicGeometry.Space.HasAffineSpaceFibres.fromPreimage`: in particular by the base
  change `f^{-1}(Z) → Z` along a closed subspace.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_fromPreimage_of_closed` and
  `AlgebraicGeometry.Space.isQuasiCompact_fromPreimage`: flatness, relative dimension and
  quasi-compactness of `f^{-1}(Z) → Z`.

## Implementation notes

The fibre is recorded as a cartesian square of presheaves whose corner over `Spec κ(y)` is the
presheaf represented by an object `T` of the site, together with an isomorphism over `Spec κ(y)`
of the scheme underlying `T` with `𝐀^r_{κ(y)}`, the index type of affine space being
`ULift (Fin r)` as in Stacks 02TT. This is the form in which
`BaseSpaceDimensionSituation.exists_isPullback_vectorBundleProjection_residueFieldMorphism`
supplies the hypothesis for the projection of a vector bundle.

## References

* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0ENW](https://stacks.math.columbia.edu/tag/0ENW)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Fibres

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The fibre hypothesis of Stacks 0ERG.** A morphism `f : X → Y` to a good algebraic space
`Y/B` *has affine `r`-space fibres* when for every `y ∈ |Y|` the fibre of `f` over the
monomorphism `Spec κ(y) → Y` of Stacks 0ENW is represented by a scheme `T` of the site, and `T`
is isomorphic over `Spec κ(y)` to `𝐀^r_{κ(y)}`: `X_y ≅ 𝐀^r_{κ(y)}`. -/
def HasAffineSpaceFibres (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ y : points D.site D.base D.base_mem Y,
    ∃ (T : BigFppfOver D.site D.base D.base_mem) (a : yoneda.obj T ⟶ X)
      (b : T ⟶ (D.residueFieldRepresentative sY hY y).1.siteObject D.site D.base D.base_mem Y),
      IsPullback a (yoneda.map b) f (D.residueFieldMorphism sY hY y) ∧
        ∃ e : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T ≅
            𝔸(ULift.{u} (Fin r); Spec (.of (D.residueField sY hY y))),
          e.hom ≫ 𝔸(ULift.{u} (Fin r); Spec (.of (D.residueField sY hY y))) ↘
              Spec (.of (D.residueField sY hY y)) =
            (BigFppfOver.toScheme D.site D.base D.base_mem).map b

/-- An isomorphism of the bases of two affine spaces, lifted to an isomorphism of the affine
spaces over it. -/
def affineSpaceIsoOfIso {S₁ S₂ : Scheme.{u}} (n : Type u) (φ : S₁ ≅ S₂) :
    𝔸(n; S₁) ≅ 𝔸(n; S₂) where
  hom := AffineSpace.map n φ.hom
  inv := AffineSpace.map n φ.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id]

/-- The isomorphism of affine spaces over an isomorphism of bases lies over it. -/
theorem affineSpaceIsoOfIso_hom_over {S₁ S₂ : Scheme.{u}} (n : Type u) (φ : S₁ ≅ S₂) :
    (affineSpaceIsoOfIso n φ).hom ≫ 𝔸(n; S₂) ↘ S₂ = 𝔸(n; S₁) ↘ S₁ ≫ φ.hom :=
  AffineSpace.map_over (n := n) φ.hom

/-- **The fibre hypothesis is inherited by base change along a monomorphism.** Let
`g : Y' → Y` be a monomorphism of good algebraic spaces over the base and let `f' : X' → Y'` be
the base change of `f`. If the fibres of `f` over the spectra of the residue fields of `Y` are
affine `r`-spaces, so are those of `f'`: the monomorphism `Spec κ(y') → Y' → Y` represents
`g(y')`, so by Stacks 0ENW it is isomorphic over `Y` to `Spec κ(g(y')) → Y`, and the fibre of `f'`
over `Spec κ(y')` is the fibre of `f` over it. -/
theorem HasAffineSpaceFibres.of_isPullback
    {X' Y' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sY : Y ⟶ D.space} {hY : D.IsGood sY} {f : X ⟶ Y} {r : ℕ}
    (h : HasAffineSpaceFibres D sY hY f r) (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY')
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} [Mono g] (sq : IsPullback g' f' f g) :
    HasAffineSpaceFibres D sY' hY' f' r := by
  intro y'
  set y := pointsMap D.site D.base D.base_mem Y' g y'
  obtain ⟨T, a, b, hpb, e, he⟩ := h y
  set q := FieldValuedPoint.map D.site D.base D.base_mem Y' g
    (D.residueFieldRepresentative sY' hY' y').1
  have hq : q.class D.site D.base D.base_mem Y = y := by
    rw [← pointsMap_class, (D.residueFieldMorphism_spec sY' hY' y').1]
  have hqmor : fieldMorphism D.site D.base D.base_mem Y q =
      D.residueFieldMorphism sY' hY' y' ≫ g :=
    fieldMorphism_map D.site D.base D.base_mem Y' g _
  have hmono : Mono (fieldMorphism D.site D.base D.base_mem Y q) := by
    rw [hqmor]
    exact mono_comp' (D.residueFieldMorphism_spec sY' hY' y').2 inferInstance
  obtain ⟨E, hE, -⟩ := D.residueFieldRepresentative_unique sY hY y q hq hmono
  -- the isomorphism of the two field spectra, in the site
  set G : (D.residueFieldRepresentative sY' hY' y').1.siteObject D.site D.base D.base_mem Y' ≅
      (D.residueFieldRepresentative sY hY y).1.siteObject D.site D.base D.base_mem Y :=
    (Functor.FullyFaithful.ofFullyFaithful yoneda).preimageIso E.symm
  have hG : yoneda.map G.hom = E.inv :=
    (Functor.FullyFaithful.ofFullyFaithful yoneda).map_preimage _
  have hGsq : yoneda.map G.hom ≫ D.residueFieldMorphism sY hY y =
      D.residueFieldMorphism sY' hY' y' ≫ g :=
    (congrArg (· ≫ D.residueFieldMorphism sY hY y) hG).trans
      ((congrArg (E.inv ≫ ·) hE.symm).trans ((Iso.inv_hom_id_assoc _ _).trans hqmor))
  have hGsq' : D.residueFieldMorphism sY hY y =
      yoneda.map G.inv ≫ D.residueFieldMorphism sY' hY' y' ≫ g := by
    rw [← hGsq, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  -- the big square, over `Spec κ(y') → Y' → Y`
  have hbig : IsPullback a (yoneda.map (b ≫ G.inv)) f (D.residueFieldMorphism sY' hY' y' ≫ g) :=
    hpb.of_iso (Iso.refl _) (Iso.refl _) (yoneda.mapIso G.symm) (Iso.refl _)
      (by simp) (by simp [Functor.map_comp]) (by simp) (by
        simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom]
        exact hGsq')
  have hcomm : a ≫ f = (yoneda.map (b ≫ G.inv) ≫ D.residueFieldMorphism sY' hY' y') ≫ g := by
    rw [hbig.w, Category.assoc]
  set a' := sq.lift a (yoneda.map (b ≫ G.inv) ≫ D.residueFieldMorphism sY' hY' y') hcomm
  have ha' : a' ≫ g' = a := sq.lift_fst _ _ _
  have ha'' : a' ≫ f' = yoneda.map (b ≫ G.inv) ≫ D.residueFieldMorphism sY' hY' y' :=
    sq.lift_snd _ _ _
  refine ⟨T, a', b ≫ G.inv, ?_, ?_⟩
  · refine IsPullback.of_right ?_ ha'' sq
    rw [ha']
    exact hbig
  · refine ⟨e ≪≫ affineSpaceIsoOfIso _
      ((BigFppfOver.toScheme D.site D.base D.base_mem).mapIso G.symm), ?_⟩
    rw [Iso.trans_hom, Category.assoc, affineSpaceIsoOfIso_hom_over, ← Category.assoc, he,
      Functor.map_comp]
    rfl

end Fibres

section Preimage

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (Z : Subfunctor Y) (hZ : IsClosedSubspace D.site D.base D.base_mem Z)

include hX hY hZ in
/-- The inverse image of a closed subspace is a closed subspace. -/
theorem isClosedSubspace_preimage_of_isClosedSubspace :
    IsClosedSubspace D.site D.base D.base_mem (Z.preimage f) :=
  isClosedSubspace_preimage D.site D.base D.base_mem f Z hY.1 hX.1 hZ

include hbase in
/-- The structure morphisms of `f^{-1}(Z)` and of `Z` are compatible with `f^{-1}(Z) → Z`. -/
theorem fromPreimage_comp_structureMorphism :
    Z.fromPreimage f ≫ Z.ι ≫ sY = (Z.preimage f).ι ≫ sX := by
  rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, hbase]

include hX hY hZ hbase in
/-- **Stacks 0EPD, second assertion, along a closed subspace.** If `f` is flat of relative
dimension `r` then so is `f^{-1}(Z) → Z`. -/
theorem isFlat_and_hasRelativeDimension_fromPreimage_of_closed (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) :
    IsFlat D.site D.base D.base_mem (Z.fromPreimage f) ∧
      HasRelativeDimension r D.site D.base D.base_mem (Z.fromPreimage f) :=
  (isFlat_and_hasRelativeDimension_of_isPullback D ((Z.preimage f).ι ≫ sX)
    (isGood_ι_of_isClosedSubspace D sX hX _
      (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ))
    (Z.ι ≫ sY) (isGood_ι_of_isClosedSubspace D sY hY Z hZ) sX hX sY hY
    (fromPreimage_comp_structureMorphism D sX sY f hbase Z) hbase
    (Subfunctor.isPullback_preimage f Z) r hflat hr).2

/-- **Stacks 03HF along a closed subspace.** If `f` is quasi-compact then so is
`f^{-1}(Z) → Z`. -/
theorem isQuasiCompact_fromPreimage (hqc : IsQuasiCompact D.site D.base D.base_mem f) :
    IsQuasiCompact D.site D.base D.base_mem (Z.fromPreimage f) :=
  isQuasiCompact_of_isPullback D.site D.base D.base_mem
    (Subfunctor.isPullback_preimage f Z).flip hqc

/-- **The fibre hypothesis along a closed subspace.** If the fibres of `f` over the spectra of
the residue fields of `Y` are affine `r`-spaces, so are those of `f^{-1}(Z) → Z`. -/
theorem HasAffineSpaceFibres.fromPreimage {r : ℕ} (h : HasAffineSpaceFibres D sY hY f r) :
    HasAffineSpaceFibres D (Z.ι ≫ sY) (isGood_ι_of_isClosedSubspace D sY hY Z hZ)
      (Z.fromPreimage f) r :=
  h.of_isPullback D _ _ (Subfunctor.isPullback_preimage f Z).flip

end Preimage

end AlgebraicGeometry.Space

end
