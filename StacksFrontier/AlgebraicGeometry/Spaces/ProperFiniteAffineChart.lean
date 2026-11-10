module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedPointInfiniteFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus

/-!
# A finite affine chart diagram at a point with finite fibre

Let `g : Z ⟶ Y` be a proper morphism of decent algebraic spaces over `S` and let `η` be a point
of `|Y|` whose fibre in `|Z|` is finite. This file produces a commuting square of étale scheme
charts of `g` which is cartesian, has affine schemes on both sides and a finite morphism of
schemes between them, and whose target chart has exactly one point `e` above `η`, with
`Spec κ(e) ⟶ Y` a monomorphism.

## Main results

* `AlgebraicGeometry.Space.exists_finite_affine_chartDiagram`: the chart diagram above.
* `AlgebraicGeometry.Space.exists_iso_siteHom_canonicalSiteFieldPoint`: the canonical
  field-valued point of a scheme of the site at a point is its residue-field point, up to an
  isomorphism of field spectra over `S`.

## Implementation notes

The proof follows three steps. A finite fibre of a proper morphism of decent spaces consists of
points where `g` is quasi-finite
(`AlgebraicGeometry.Space.finite_fibre_iff_forall_isQuasiFiniteAt`, Stacks 0ACK), so `g` is
finite over an open subspace `V` of `Y` containing `η`
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_isProper`). The open
subspace `V` is decent, so Stacks 0BBP
(`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`) gives an affine
elementary étale neighbourhood `E` of the point of `V` over `η`; its composite with the
inclusion of `V` is the target chart. Finiteness of `Z ×_Y V ⟶ V` represents the base change to
`E` by an affine scheme finite over `E`, and pasting with the square of `Z ×_Y V` gives the
source chart and the cartesian square. The monomorphism comes from the one carried by the
elementary étale neighbourhood, transported along
`AlgebraicGeometry.Space.exists_iso_siteHom_canonicalSiteFieldPoint`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The site morphism of the canonical field-valued point at a point `u` of a scheme `U` of the
site is the canonical morphism from the residue-field point of `U` at `u`, up to an isomorphism
of the two field spectra over `S`: they are the same field spectrum, with structure morphisms to
`S` that agree. -/
theorem exists_iso_siteHom_canonicalSiteFieldPoint (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    ∃ k : (canonicalSiteFieldPoint B S hS U u).siteObject ≅ residueFieldObject B S hS U u hu,
      (canonicalSiteFieldPoint B S hS U u).siteHom = k.hom ≫ residueFieldMap B S hS U u hu := by
  have hρ := map_siteMapOfSchemeMap B S hS U
    (B.residueField_spec_contains U.left.property u)
    (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u)
  have h₁ : U.left.1.fromSpecResidueField u ≫ U.hom.1 =
      B.inclusion.map (siteMapOfSchemeMap B S hS U
        (B.residueField_spec_contains U.left.property u)
        (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u) ≫ U.hom) := by
    rw [Functor.map_comp, hρ]
    rfl
  refine ⟨Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ h₁), ?_⟩
  exact Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <| hρ.trans (Category.id_comp _).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_ProperFiniteAffineChart :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProperFiniteAffineChart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A finite affine chart diagram at a point with finite fibre.** Let `g : Z ⟶ Y` be a proper
morphism of decent algebraic spaces and `η` a point of `|Y|` with finite fibre. Then there is a
cartesian square of étale scheme charts of `g` with affine schemes, whose morphism of schemes is
finite, and a point `e` of the target chart which is the only one above `η` and whose
residue-field point `Spec κ(e) ⟶ Y` is a monomorphism. -/
theorem exists_finite_affine_chartDiagram {Z Y : AlgebraicSpaces B S hS}
    (hZdec : IsDecentSpace B S hS Z.1) (hYdec : IsDecentSpace B S hS Y.1)
    (g : Z ⟶ Y) (hg : IsProper B S hS g.hom) (η : points B S hS Y.1)
    (hfin : {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η}.Finite) :
    ∃ (d : ChartDiagram B S hS Z.1 Y.1 g.hom) (e : chartScheme d.V),
      IsPullback d.U.1.hom (yoneda.map d.g) g.hom d.V.1.hom ∧
      IsAffine (chartScheme d.V) ∧ IsAffine (chartScheme d.U) ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map d.g) ∧
      chartSchemeToPoints B S hS Y.1 d.V e = η ∧
      (∀ e' : chartScheme d.V, chartSchemeToPoints B S hS Y.1 d.V e' = η → e' = e) ∧
      Mono (fieldMorphism B S hS Y.1 (chartSchemeFieldValuedPoint B S hS Y.1 d.V e)) := by
  -- Step 1: `g` is finite over an open neighbourhood `V` of `η`.
  have hqf := (finite_fibre_iff_forall_isQuasiFiniteAt B S hS Z.2 Y.2 g.hom hg.2.1.1 hg.2.2
    hZdec hYdec η).1 hfin
  obtain ⟨V, hVopen, ⟨v, hv⟩, hVfin⟩ :=
    exists_isOpenSubspace_isFinite_pullback_snd_of_isProper B S hS Z.2 Y.2 g.hom hg η hqf
  -- Step 2: an affine elementary étale neighbourhood of `v` in `V`.
  have hVdec : IsDecentSpace B S hS V.toFunctor :=
    isDecentSpace_of_isOpenSubspace B S hS Y.2 hYdec hVopen
  obtain ⟨E, hEaff, hEuniq, -⟩ :=
    exists_affine_elementaryEtaleNeighborhood' B S hS hVopen.1 hVdec v
  -- Step 3: the base change of `g` to `E`.
  obtain ⟨U', p, i, hU'aff, hpfin, hpb⟩ := hVfin E.scheme hEaff E.toSpace
  have hsq : IsPullback (pullback.fst g.hom V.ι) (pullback.snd g.hom V.ι) g.hom V.ι :=
    IsPullback.of_hasPullback g.hom V.ι
  have hpb' : IsPullback (i ≫ pullback.fst g.hom V.ι) (yoneda.map p) g.hom (E.toSpace ≫ V.ι) :=
    hpb.paste_horiz hsq
  have hVet : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (E.toSpace ≫ V.ι)) :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS E.etale_toSpace (isEtale_ι_of_isOpenSubspace hVopen))
  have hUet : IsEtaleChart B S hS Z.1 (CostructuredArrow.mk (i ≫ pullback.fst g.hom V.ι)) :=
    presheaf_of_isPullback B S hS hpb'.flip hVet
  let d : ChartDiagram B S hS Z.1 Y.1 g.hom :=
    { U := ⟨CostructuredArrow.mk (i ≫ pullback.fst g.hom V.ι), hUet⟩
      V := ⟨CostructuredArrow.mk (E.toSpace ≫ V.ι), hVet⟩
      g := p
      comm := hpb'.w }
  have hsymm : (pointsEquivScheme B S hS E.scheme).symm E.point =
      presheafPoint B S hS E.scheme E.point E.residueField_contained :=
    (Equiv.symm_apply_eq _).2 (pointsToScheme_presheafPoint B S hS _ _ _).symm
  have hpt : ∀ e' : chartScheme d.V, chartSchemeToPoints B S hS Y.1 d.V e' =
      pointsMap B S hS V.toFunctor V.ι (pointsMap B S hS (yoneda.obj E.scheme) E.toSpace
        ((pointsEquivScheme B S hS E.scheme).symm e')) := fun e' ↦
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS Y.1 d.V e').trans
      (pointsMap_comp_apply B S hS E.toSpace V.ι _)
  refine ⟨d, E.point, hpb', hEaff, hU'aff, hpfin, ?_, fun e' he' ↦ ?_, ?_⟩
  · rw [hpt, hsymm, E.map_point, hv]
  · rw [hpt, ← hv] at he'
    have h₁ := hEuniq _ (pointsMap_injective_of_mono B S hS V.ι he')
    rw [← hsymm] at h₁
    exact (pointsEquivScheme B S hS E.scheme).symm.injective h₁
  · change Mono (fieldMorphism B S hS Y.1 (FieldValuedPoint.map B S hS (yoneda.obj E.scheme)
      (E.toSpace ≫ V.ι) (canonicalSiteFieldPoint B S hS E.scheme E.point)))
    rw [fieldMorphism_map_yoneda]
    obtain ⟨k, hk⟩ := exists_iso_siteHom_canonicalSiteFieldPoint B S hS E.scheme E.point
      E.residueField_contained
    have := E.mono_residueField
    rw [hk, Functor.map_comp, Category.assoc, ← Category.assoc _ E.toSpace]
    exact mono_comp (yoneda.map k.hom) _

end AlgebraicGeometry.Space

end
