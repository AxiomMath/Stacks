module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descent of local Noetherianity along a surjective affine flat morphism of spaces

Local Noetherianity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.IsLocallyNoetherian` in the sense of
`AlgebraicGeometry.Space.HasEtaleLocalProperty`. It descends along a surjective, affine, flat
morphism of algebraic spaces: an affine open of a chart of the target is pulled back to an
affine scheme over the source, the induced ring map is faithfully flat because the morphism is
affine, flat and surjective, and Noetherianity of a ring descends along a faithfully flat ring
map.

## Main results

* `AlgebraicGeometry.Space.isLocallyNoetherian_of_surjective_affine_flat`: a surjective,
  affine, flat morphism of algebraic spaces with locally Noetherian source has locally
  Noetherian target.

## Implementation notes

Turning local Noetherianity of the source from the *some-chart* condition of Stacks 03E6 into
the *every-étale-scheme* condition needs `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`
(Stacks 03E8), which in turn needs local Noetherianity to be a local object property for the
étale precoverage, Stacks 034E; that is taken here as an instance argument.

Affineness of the morphism supplies, for each affine open of the chart of the target, an affine
scheme over the source together with a cartesian square. Surjectivity of the resulting morphism
of schemes is read off from surjectivity on points through
`AlgebraicGeometry.Space.surjective_iff_surjective_pointsMap`, flatness from the chart
condition defining `AlgebraicGeometry.Space.IsFlat`, and the two together give faithful flatness
of the map on global sections because both schemes are affine.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A flat surjective morphism of affine schemes with locally Noetherian source has Noetherian
ring of global sections on the target. -/
private theorem isNoetherianRing_of_flat_surjective_of_isAffine {W Y : Scheme.{u}} (f : W ⟶ Y)
    [IsAffine W] [IsAffine Y] [Flat f] [Surjective f] [IsLocallyNoetherian W] :
    IsNoetherianRing Γ(Y, ⊤) :=
  descent_noetherian f.appTop.hom
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹_›, ‹_›⟩)
    (IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top W⟩)

/-- The base change of a surjective morphism of algebraic spaces along a morphism from a
representable presheaf, when representable, is a surjective morphism of schemes. -/
private theorem surjective_toScheme_map_of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : Z ⟶ T}
    (hZSpace : IsAlgebraicSpace B S hS Z) (hTSpace : IsAlgebraicSpace B S hS T)
    (hp : IsSurjective B S hS p) {W V : BigFppfOver B S hS} {w : yoneda.obj W ⟶ Z}
    {q : W ⟶ V} {g : yoneda.obj V ⟶ T} (sq : IsPullback w (yoneda.map q) p g) :
    Surjective ((BigFppfOver.toScheme B S hS).map q) := by
  let Wsp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj W, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W⟩
  let Vsp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩
  let Zsp : AlgebraicSpaces B S hS := ⟨Z, hZSpace⟩
  let Tsp : AlgebraicSpaces B S hS := ⟨T, hTSpace⟩
  have hfull : IsPullback (ObjectProperty.homMk w : Wsp ⟶ Zsp)
      (ObjectProperty.homMk (yoneda.map q) : Wsp ⟶ Vsp)
      (ObjectProperty.homMk p : Zsp ⟶ Tsp) (ObjectProperty.homMk g : Vsp ⟶ Tsp) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hqSurjPoints : IsSurjective B S hS (X := yoneda.obj W) (Y := yoneda.obj V)
      (yoneda.map q) := by
    simpa [Wsp, Vsp] using isSurjective_of_isPullback B S hS hfull hp
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).1
    ((surjective_iff_surjective_pointsMap B S hS (yoneda.obj V) Vsp.property W
      (yoneda.map q)).2 hqSurjPoints)

/-- **Descent of local Noetherianity.** A surjective, affine, flat morphism of algebraic
spaces over `S` whose source is locally Noetherian has locally Noetherian target. -/
theorem isLocallyNoetherian_of_surjective_affine_flat
    [ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      Scheme.etalePrecoverage]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Z ⟶ T)
    (hZSpace : IsAlgebraicSpace B S hS Z) (hTSpace : IsAlgebraicSpace B S hS T)
    (hpSurjective : IsSurjective B S hS p) (hpAffine : IsAffineHom B S hS p)
    (hpFlat : IsFlat B S hS p)
    (hZLocallyNoetherian :
      HasEtaleLocalProperty B S hS Z (fun X : Scheme.{u} => IsLocallyNoetherian X)) :
    HasEtaleLocalProperty B S hS T (fun X : Scheme.{u} => IsLocallyNoetherian X) := by
  obtain ⟨U, u, huSurjective, huEtale⟩ := hTSpace.exists_atlas
  refine ⟨U, u, huSurjective, huEtale, ?_⟩
  let X := (BigFppfOver.toScheme B S hS).obj U
  change IsLocallyNoetherian X
  rw [isLocallyNoetherian_iff_of_iSup_eq_top (S := fun i : X.affineOpens => i)
    (iSup_affineOpens_eq_top X)]
  intro i
  let Y : Scheme.{u} := (i.1 : X.Opens).toScheme
  have hYcut : Y.size < B.cutoff := (Scheme.size_coe_opens_le _ i.1).trans_lt U.left.2
  let ab : (⟨Y, hYcut⟩ : B.Schemes) ⟶ U.left :=
    B.inclusion.preimage (show B.inclusion.obj ⟨Y, hYcut⟩ ⟶ B.inclusion.obj U.left from
      (i.1 : X.Opens).ι)
  let V : BigFppfOver B S hS := Over.mk (ab ≫ U.hom)
  let vU : V ⟶ U := Over.homMk ab rfl
  let Va : BigAffineFppf B S hS := ⟨V, show IsAffine (↑(i.1 : X.Opens)) from i.2⟩
  obtain ⟨W, wZ, q, sq⟩ := hpAffine Va (yoneda.map vU ≫ u)
  let QEtale := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have : QEtale.IsStableUnderBaseChange := inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : QEtale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have : QEtale.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange QEtale
  have : QEtale.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QEtale
  have hvUEtale : QEtale.presheaf (yoneda.map vU) := by
    apply MorphismProperty.relative_map
    change Etale (B.inclusion.map ab)
    rw [B.inclusion.map_preimage]
    infer_instance
  have hgEtale : QEtale.presheaf (yoneda.map vU ≫ u) :=
    MorphismProperty.comp_mem QEtale.presheaf _ _ hvUEtale huEtale
  have hwZEtale : QEtale.presheaf wZ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hgEtale
  let Wsite := (BigAffineFppf.inclusion B S hS).obj W
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Wsite) :=
    (exists_atlas_iff_forall_etale B S hS Z (fun X : Scheme.{u} => IsLocallyNoetherian X)
      hZSpace).1 hZLocallyNoetherian Wsite wZ hwZEtale
  have : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    surjective_toScheme_map_of_isPullback B S hS hZSpace hTSpace hpSurjective sq
  have : Flat ((BigFppfOver.toScheme B S hS).map q) :=
    hpFlat Wsite V wZ (yoneda.map vU ≫ u) q hwZEtale hgEtale sq.w.symm
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Wsite) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS W
  have := BigAffineFppf.isAffine_toScheme_obj B S hS Va
  have : IsNoetherianRing Γ(Y, ⊤) :=
    isNoetherianRing_of_flat_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map q)
  exact isNoetherianRing_of_ringEquiv _
    (asIso ((i.1 : X.Opens).ι.appLE i.1 ⊤ (fun x _ ↦ x.2))).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Space

end
