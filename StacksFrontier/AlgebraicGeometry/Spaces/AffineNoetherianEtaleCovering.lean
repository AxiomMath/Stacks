module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Spectra of Noetherian rings as étale charts of a locally Noetherian algebraic space

A locally Noetherian algebraic space over `S` is covered by étale charts whose underlying
schemes are literally spectra of Noetherian rings. This refines the defining property of an
algebraic space, which provides a single surjective étale chart by some scheme of the site, to a
family of charts each of which is a spectrum: what a consumer needs when it has to feed an affine
scheme, or a ring, into a construction.

## Main definitions

* `AlgebraicGeometry.Space.affineOpenSpecSiteHom`: the morphism of the big fppf site over `S`
  attached to an affine open of the scheme underlying an object of the site, with the canonical
  open immersion `Spec Γ(X, W) ⟶ X` as its underlying morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_spec_isLocallyNoetherian_etale_covering_family`: a locally
  Noetherian algebraic space admits a family of étale charts out of spectra of Noetherian rings,
  indexed by a type of the working universe, which is jointly surjective on points.

## Implementation notes

The family is obtained from one surjective étale atlas `h_V ⟶ Y` by shrinking `V` to the affine
opens of its underlying scheme `X`. For `W` an affine open of `X` the ring is `Γ(X, W)`; it is
Noetherian because `X` is locally Noetherian, which holds because local Noetherianity is an
étale-local property of schemes (**Stacks 03E8**) and so may be tested on any étale scheme over
`Y`.

The chart itself is the composite of the atlas with the morphism of the site whose underlying
morphism of schemes is `AlgebraicGeometry.IsAffineOpen.fromSpec`, the canonical open immersion
`Spec Γ(X, W) ⟶ X`. Using `fromSpec` rather than the open inclusion of `W` is what makes the
scheme representing the chart *definitionally* a spectrum, which is the point of the statement;
the price is that the identification of `Spec Γ(X, W)` with `W` is no longer the identity, and it
is paid in the covering clause, where the range of `fromSpec` is recovered from
`AlgebraicGeometry.IsAffineOpen.range_fromSpec`.

Joint surjectivity is checked on the points of the representing schemes, through the bijection
`AlgebraicGeometry.Space.pointsToScheme` between the points of a represented presheaf and the
points of the representing scheme: a point of `Y` comes from a point `x` of `X` because the atlas
is surjective, the affine opens of `X` cover `X`, and `fromSpec` of an affine open containing `x`
hits `x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).affineOpens)

/-- The spectrum of the ring of sections of an affine open of the scheme underlying an object of
the big fppf site over `S` again belongs to the site: it is the source of an open immersion into
that scheme. -/
theorem contains_spec_affineOpen :
    B.Contains (Spec Γ((BigFppfOver.toScheme B S hS).obj V, W.1)) :=
  have := W.2.isOpenImmersion_fromSpec
  Scheme.size_lt_of_isOpenImmersion W.2.fromSpec V.left.2

/-- The morphism of the big fppf site over `S` attached to an affine open `W` of the scheme
underlying an object `V`: its source is the spectrum of `Γ(X, W)`, viewed as an object of the
site over `S` through the canonical open immersion into the scheme underlying `V`, and its
underlying morphism of schemes is that open immersion. -/
def affineOpenSpecSiteHom :
    siteObject B S hS (contains_spec_affineOpen B S hS V W)
      (W.2.fromSpec ≫ B.inclusion.map V.hom) ⟶ V :=
  Over.homMk (ObjectProperty.homMk W.2.fromSpec :
    B.obj (contains_spec_affineOpen B S hS V W) ⟶ V.left) (by rfl)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.affineOpenSpecSiteHom` is the
canonical open immersion `AlgebraicGeometry.IsAffineOpen.fromSpec`. -/
theorem map_affineOpenSpecSiteHom :
    (BigFppfOver.toScheme B S hS).map (affineOpenSpecSiteHom B S hS V W) = W.2.fromSpec :=
  rfl

/-- A locally Noetherian algebraic space over `S` is covered by étale charts whose underlying
schemes are spectra of Noetherian rings.

The charts are indexed by a type of the working universe; each one is a morphism
`yoneda.obj (siteObject B S hS _ _) ⟶ Y` out of the presheaf represented by an object of the site
whose underlying scheme is literally `Spec A`; the ring `A` is Noetherian, so that `Spec A` is
locally Noetherian; each chart is étale; and together they hit every point of `Y`. -/
theorem exists_spec_isLocallyNoetherian_etale_covering_family
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    ∃ (I : Type u) (A : I → CommRingCat.{u}) (hA : ∀ i, B.Contains (Spec (A i)))
      (a : ∀ i, Spec (A i) ⟶ S)
      (φ : ∀ i, yoneda.obj (siteObject B S hS (hA i) (a i)) ⟶ Y),
      (∀ i, IsNoetherianRing (A i)) ∧
      (∀ i, IsLocallyNoetherian (Spec (A i))) ∧
      (∀ i, IsEtale B S hS (φ i)) ∧
      (∀ y : points B S hS Y, ∃ i,
        y ∈ Set.range (pointsMap B S hS
          (yoneda.obj (siteObject B S hS (hA i) (a i))) (φ i))) := by
  classical
  -- One surjective étale atlas of `Y`.
  obtain ⟨V, φV, hsurj, hetale⟩ := hY.exists_atlas
  -- Its underlying scheme is locally Noetherian: local Noetherianity is étale-local, so it is
  -- tested on every étale scheme over `Y`.
  have hVNoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) hY).mp hNoeth V φV hetale
  refine ⟨((BigFppfOver.toScheme B S hS).obj V).affineOpens,
    fun W ↦ Γ((BigFppfOver.toScheme B S hS).obj V, W.1),
    contains_spec_affineOpen B S hS V,
    fun W ↦ W.2.fromSpec ≫ B.inclusion.map V.hom,
    fun W ↦ yoneda.map (affineOpenSpecSiteHom B S hS V W) ≫ φV,
    hVNoeth.component_noetherian, fun W ↦ ?_, fun W ↦ ?_, fun y ↦ ?_⟩
  · have := hVNoeth.component_noetherian W
    infer_instance
  · -- `fromSpec` is an open immersion, hence étale, and an étale morphism of the site followed
    -- by an étale chart is an étale chart.
    have := W.2.isOpenImmersion_fromSpec
    refine isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS ?_)
      (isEtale_of_presheaf_etale B S hS hetale)
    refine (presheaf_yoneda_map_etale_iff B S hS (affineOpenSpecSiteHom B S hS V W)).2 ?_
    rw [map_affineOpenSpecSiteHom]
    exact inferInstance
  · -- A point of `Y` comes from a point of the atlas, and the affine opens of its scheme cover
    -- that point.
    obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY V φV).mp hsurj y
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      ((BigFppfOver.toScheme B S hS).obj V).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (pointsToScheme B S hS V z)) isOpen_univ
    obtain ⟨s, hs⟩ : pointsToScheme B S hS V z ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hxW
    obtain ⟨r, hr⟩ := surjective_pointsToScheme B S hS
      (siteObject B S hS (contains_spec_affineOpen B S hS V ⟨W, hW⟩)
        (hW.fromSpec ≫ B.inclusion.map V.hom)) s
    refine ⟨⟨W, hW⟩, r, ?_⟩
    have hrz : pointsMap B S hS _ (yoneda.map (affineOpenSpecSiteHom B S hS V ⟨W, hW⟩)) r = z := by
      refine injective_pointsToScheme B S hS V ?_
      rw [pointsToScheme_pointsMap_yoneda, map_affineOpenSpecSiteHom, hr]
      exact hs
    rw [pointsMap_comp, Function.comp_apply, hrz, hz]

end AlgebraicGeometry.Space

end
