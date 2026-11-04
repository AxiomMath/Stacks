module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedFieldBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedQuasiCompactReduction

/-!
# A universally closed morphism of algebraic spaces is quasi-compact

This file supplies the affine-base case used in closing Stacks 04XW: a universally closed
morphism of algebraic spaces over a scheme `S` whose target is represented by an affine scheme
of the site has quasi-compact source.

Two steps are already available. The base of the quantifier defining quasi-compactness of a
morphism is replaced by an affine scheme of the site in
`AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed_of_affine_base`, and the case of a
base with a one-point point space is
`AlgebraicGeometry.Space.compactSpace_points_of_universallyClosed_of_subsingleton_base`. What
remains, and is proved here, is the passage from a one-point base to an affine base.

Stacks 04XW itself is `AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed`, the module that owns the
universally-closed vocabulary.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_universallyClosed_of_isAffine`: a
  universally closed morphism of algebraic spaces over `S` whose target is represented by an
  affine scheme of the site has quasi-compact source.

## Implementation notes

The passage from a one-point base to an affine base is topological properness. The map on
points of a universally closed morphism is closed, by
`AlgebraicGeometry.Space.isClosed_of_universallyClosed`, and each of its fibres is
quasi-compact: the fibre over a point represented by a field-valued point `p` of the target is
the image of the point space of the field fibre `W ×_{h_V} h_{Spec κ}` by Tag 03H4, in the
form `AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`, and the field fibre is
universally closed over `h_{Spec κ}` by Stacks 03IS, so the one-point case applies to it.
`isProperMap_iff_isClosedMap_and_compact_fibers` then makes the map on points proper, and the
point space of an affine scheme of the site is quasi-compact, so the preimage of everything is
quasi-compact. Quasi-compactness of the point space is quasi-compactness of the algebraic
space by Tag 03E4.

`AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre` is stated for the fibre product
`W ×_{h_V} h_{Spec κ}` with first projection to `W`, whereas
`AlgebraicGeometry.Space.universallyClosed_pullback` produces universal closedness of the
first projection of `h_{Spec κ} ×_{h_V} W`. The two fibre products are exchanged by
`CategoryTheory.Limits.pullbackSymmetry`, whose map on points is surjective by
`AlgebraicGeometry.Space.pointsMap_surjective_of_isIso`, so quasi-compactness of the point
space transfers from one to the other.

`AlgebraicGeometry.Space.pointTopology` is installed as a local instance.

## References

* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03IS](https://stacks.math.columbia.edu/tag/03IS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universally closed morphism of algebraic spaces with affine representable target has
quasi-compact source.** This is the affine case of Stacks 04XW.

The map `|W| → |V|` is closed because `h` is universally closed, and its fibre over the point
represented by a field-valued point `p` of `h_V` is the image of the point space of the field
fibre of `h` at `p`, by Tag 03H4. That field fibre is a base change of `h`, hence universally
closed over a base with a one-point point space, so its point space is quasi-compact by
`AlgebraicGeometry.Space.compactSpace_points_of_universallyClosed_of_subsingleton_base`; hence
every fibre of `|W| → |V|` is quasi-compact. A closed map with quasi-compact fibres is proper,
and `|V|` is quasi-compact because the scheme underlying `V` is affine, so `|W|` is
quasi-compact; Tag 03E4 turns that back into quasi-compactness of `W`. -/
theorem isQuasiCompactSpace_of_universallyClosed_of_isAffine
    (V : BigFppfOver B S hS) (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hV : IsAlgebraicSpace B S hS (yoneda.obj V)) (h : W ⟶ yoneda.obj V)
    (hh : UniversallyClosed B S hS h) :
    IsQuasiCompactSpace B S hS W := by
  refine isQuasiCompactSpace_of_compactSpace_points B S hS hW ?_
  have hVc : CompactSpace (points B S hS (yoneda.obj V)) :=
    @compactSpace_points_yoneda B S hS V inferInstance
  have hfib : ∀ v, IsCompact (pointsMap B S hS W h ⁻¹' {v}) := by
    intro v
    obtain ⟨p, rfl⟩ := Quot.exists_rep v
    let V' : BigFppfOver B S hS := p.siteObject
    let g' : yoneda.obj V' ⟶ yoneda.obj V := yonedaEquiv.symm p.value
    have hV' : IsAlgebraicSpace B S hS (yoneda.obj V') := isAlgebraicSpace_yoneda B S hS V'
    have hsub : Subsingleton (points B S hS (yoneda.obj V')) :=
      ⟨fun x y => injective_pointsToScheme B S hS V'
        (@Subsingleton.elim _ (inferInstanceAs
          (Subsingleton (Spec (CommRingCat.of p.carrier)))) _ _)⟩
    have hPsym : CompactSpace (points B S hS (pullback g' h)) :=
      compactSpace_points_of_universallyClosed_of_subsingleton_base B S hS V' p.carrier
        p.contained (𝟙 _) hsub (isAlgebraicSpace_pullback B S hS g' h hV' hW hV) hV'
        (pullback.fst g' h) (universallyClosed_pullback B S hS h g' hh)
    have hPc : CompactSpace (points B S hS (pullback h g')) :=
      @Function.Surjective.compactSpace _ _ _ _ _
        (continuous_pointsMap B S hS (pullbackSymmetry g' h).hom) hPsym
        (pointsMap_surjective_of_isIso B S hS (pullbackSymmetry g' h).hom)
    rw [show (pointsMap B S hS W h ⁻¹' {p.class B S hS (yoneda.obj V)}) =
        setFibre B S hS h p from rfl, ← range_pointsMap_fst_fieldFibre B S hS h p]
    exact @isCompact_range _ _ _ _ hPc _ (continuous_pointsMap B S hS _)
  have hproper : IsProperMap (pointsMap B S hS W h) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2
      ⟨continuous_pointsMap B S hS h, isClosed_of_universallyClosed B S hS hV h hh, hfib⟩
  exact ⟨by simpa using hproper.isCompact_preimage (K := Set.univ) isCompact_univ⟩

end AlgebraicGeometry.Space

end
