module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descent of local Noetherianity along a surjective affine flat morphism

Local Noetherianity of an algebraic space over `S` descends along a surjective, affine, flat
morphism: if `p : Z ⟶ T` is such a morphism and `Z` is locally Noetherian, then so is `T`.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_surjective_affine_flat`
  is the descent.

## Implementation notes

Local Noetherianity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.IsLocallyNoetherian` in the sense of
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of Tag 03E6, the same reading used by
`AlgebraicGeometry.Space.IsNoetherian`.

The argument is affine-local on a chart. Choose a scheme atlas `u : h_U ⟶ T` and an affine
open `i` of the scheme `X` underlying `U`. The open immersion `i ⟶ X` is an étale morphism
of the site, so composing it with `u` gives an étale chart of `T` with affine source; being
affine, it is one of the test objects of `AlgebraicGeometry.Space.IsAffineHom`, which
therefore presents the base change of `p` along it by a morphism `q` of the big affine site.
That `q` is surjective because `p` is, by Tag 03MH together with the comparison
`AlgebraicGeometry.Space.surjective_yonedaMap_iff_surjective_pointsMap` of the two readings
of surjectivity, and it is flat because `q` sits in a commuting square of étale charts of
`p`. Both source and target of `q` are affine, so `q` is faithfully flat on global sections
and Stacks 033E descends Noetherianity of `Γ(W, ⊤)` to `Γ(X, i)`. Noetherianity of
`Γ(W, ⊤)` comes from local Noetherianity of `Z` through Tag 03E8, since the projection
`h_W ⟶ Z` of the presenting square is an étale chart of `Z`.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 033E](https://stacks.math.columbia.edu/tag/033E)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Local Noetherianity of algebraic spaces over `S` descends along a surjective, affine, flat
morphism. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_surjective_affine_flat
    {Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Z ⟶ T)
    (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T)
    (hpSurjective : IsSurjective B S hS p) (hpAffine : IsAffineHom B S hS p)
    (hpFlat : IsFlat B S hS p)
    (hZNoetherian : HasEtaleLocalProperty B S hS Z
      (fun W : Scheme.{u} => IsLocallyNoetherian W)) :
    HasEtaleLocalProperty B S hS T (fun W : Scheme.{u} => IsLocallyNoetherian W) := by
  obtain ⟨U, u, huSurjective, huEtale⟩ := hT.exists_atlas
  refine ⟨U, u, huSurjective, huEtale, ?_⟩
  change IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)
  set X := (BigFppfOver.toScheme B S hS).obj U
  rw [isLocallyNoetherian_iff_of_iSup_eq_top (S := fun i : X.affineOpens => i)
    (iSup_affineOpens_eq_top X)]
  intro i
  -- The affine open `i` of `X`, viewed as an object `V` of the big fppf site over `S`.
  have hVcut : B.Contains ((i : X.Opens) : Scheme.{u}) :=
    (Scheme.size_coe_opens_le X (i : X.Opens)).trans_lt U.left.2
  set ab : B.obj hVcut ⟶ U.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj hVcut) ⟶ B.inclusion.obj U.left from (i : X.Opens).ι)
  have hab : B.inclusion.map ab = (i : X.Opens).ι := B.inclusion.map_preimage _
  set V : BigFppfOver B S hS := Over.mk (ab ≫ U.hom)
  set vU : V ⟶ U := Over.homMk ab rfl
  have hvUscheme : (BigFppfOver.toScheme B S hS).map vU = (i : X.Opens).ι := hab
  have hvUEtale : Etale ((BigFppfOver.toScheme B S hS).map vU) := by
    rw [hvUscheme]; infer_instance
  -- The resulting étale chart of `T` with affine source.
  set g : yoneda.obj V ⟶ T := yoneda.map vU ≫ u
  have hgEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g :=
    etale_comp_of_scheme B S hS vU u hvUEtale huEtale
  have hVaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := i.2
  -- Affineness of `p` presents its base change along that chart.
  obtain ⟨W, wZ, q, sq⟩ := hpAffine ⟨V, hVaffine⟩ g
  have hWaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj W)) := W.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (⟨V, hVaffine⟩ : BigAffineFppf B S hS))) := hVaffine
  -- The projection to `Z` is an étale chart of `Z`, so its source is locally Noetherian.
  have _ := inverseImage_isStableUnderBaseChange B S hS
    (Etale.etale_isStableUnderBaseChange.{u})
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hwZEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf wZ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hgEtale
  have hWnoetherian : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj W)) :=
    (exists_atlas_iff_forall_etale B S hS Z
      (fun W : Scheme.{u} => IsLocallyNoetherian W) hZ).1 hZNoetherian _ wZ hwZEtale
  -- The presenting morphism `q` is surjective, by Tag 03MH on the square of algebraic spaces.
  have hsquare : IsPullback
      (ObjectProperty.homMk wZ :
        (⟨yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk (yoneda.map q) :
        (⟨yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (ObjectProperty.homMk p : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨T, hT⟩)
      (ObjectProperty.homMk g :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨T, hT⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hqSurjective : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    (presheaf_yoneda_map_iff B S hS inferInstance q).1
      ((surjective_yonedaMap_iff_surjective_pointsMap B S hS q).mpr
        (isSurjective_of_isPullback B S hS hsquare hpSurjective))
  -- It is flat, being the morphism of charts in a commuting square of étale charts of `p`.
  have hqFlat : Flat ((BigFppfOver.toScheme B S hS).map q) :=
    hpFlat _ _ wZ g q hwZEtale hgEtale sq.w.symm
  -- Faithfully flat descent of Noetherianity on global sections.
  have hff : ((BigFppfOver.toScheme B S hS).map q).appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
      ((BigFppfOver.toScheme B S hS).map q)).mp ⟨hqFlat, hqSurjective⟩
  have hWring : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj W), ⊤) :=
    hWnoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hVring : IsNoetherianRing Γ(((i : X.Opens) : Scheme.{u}), ⊤) :=
    descent_noetherian ((BigFppfOver.toScheme B S hS).map q).appTop.hom hff hWring
  exact isNoetherianRing_of_ringEquiv _
    (Scheme.Opens.topIso (i : X.Opens)).commRingCatIsoToRingEquiv

end AlgebraicGeometry.Space

end
