module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen

/-!
# An affine étale chart over a quasi-compact set of points

A quasi-compact subset of the point space of an algebraic space over `S` lies in the image of
an étale morphism from an object of the big fppf site whose underlying scheme is affine.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact`: a compact set of points of
  an algebraic space over `S` is contained in the image on points of an étale morphism from an
  object of the big fppf site with affine underlying scheme.

## Implementation notes

This is the quasi-compact strengthening of
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_finite_points`, and it is proved the same
way. Tag 03FX presents one surjective étale chart `f : h_U ⟶ F` whose underlying scheme is a
disjoint union of affine objects `W i` of the site along open immersions `j i : W i ⟶ U`. Each
composite `h_{W i} ⟶ F` is étale, hence open on points by clause (3) of Tag 03BX, so its image
is open; the images cover the point space because `f` is surjective on points and the summands
cover `|U|`. Quasi-compactness selects finitely many of them, their disjoint union is again an
object of the site with affine — a finite disjoint union of affines — underlying scheme, and
the universal property of that coproduct in the site supplies the chart. Étaleness of the
resulting morphism of the site is Zariski-local on its source, and étaleness of the chart is
then Tag 03EC.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale chart over a quasi-compact set of points.** A compact subset of the point
space of an algebraic space over `S` lies in the image on points of an étale morphism from an
object of the big fppf site whose underlying scheme is affine.

No surjectivity is asserted and none is available: the chart is a disjoint union of finitely
many affine summands of a surjective chart, chosen to cover the prescribed set. -/
theorem exists_affine_etale_chart_of_isCompact
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {T : Set (points B S hS F)} (hT : IsCompact T) :
    ∃ (Z : BigFppfOver B S hS) (c : yoneda.obj Z ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
      T ⊆ Set.range (pointsMap B S hS (yoneda.obj Z) c) := by
  classical
  obtain ⟨U, f, I, W, j, e, hfSurj, hfE, hWaffine, hιe, hjOI, hjcE, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  -- The image of each summand is open, and the images cover the point space.
  have hRopen : ∀ i : I, IsOpen
      (Set.range (pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i) ≫ f))) := by
    intro i
    have h := isOpenMap_pointsMap_of_presheafEtale B S hS
      (yoneda.map (j i) ≫ f) (hjcE i) Set.univ isOpen_univ
    rwa [Set.image_univ] at h
  have hRcover : T ⊆ ⋃ i : I,
      Set.range (pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i) ≫ f)) := by
    intro x _
    obtain ⟨w, hw⟩ := isSurjective_of_presheafSurjective B S hS f hfSurj x
    obtain ⟨i, z, hz⟩ := (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1
      (pointsToScheme B S hS U w)
    obtain ⟨z', hz'⟩ := surjective_pointsToScheme B S hS (W i) z
    have hzw : pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i)) z' = w := by
      refine injective_pointsToScheme B S hS U ?_
      rw [pointsToScheme_pointsMap_yoneda, hz', hz]
    exact Set.mem_iUnion.2 ⟨i, ⟨z', by rw [pointsMap_comp_apply, hzw, hw]⟩⟩
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover _ hRopen hRcover
  -- The disjoint union of the finitely many summands met is again an object of the site.
  obtain ⟨Z, cι, e', hce, huniv⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (B := B) (S := S) (hS := hS)
      (σ := {i : I // i ∈ t}) Cardinal.mk_le_aleph0 fun a => W a.1
  obtain ⟨d, hd⟩ := huniv fun a : {i : I // i ∈ t} => j a.1
  -- Its underlying scheme is a finite disjoint union of affine schemes, hence affine.
  have hWa : ∀ a : {i : I // i ∈ t},
      IsAffine ((BigFppfOver.toScheme B S hS).obj (W a.1)) := fun a => hWaffine _
  have hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := IsAffine.of_isIso e'.inv
  -- The morphism to the chart is a coproduct of open immersions, hence étale.
  have hdesc : e'.hom ≫ (BigFppfOver.toScheme B S hS).map d =
      Sigma.desc fun a : {i : I // i ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (j a.1) := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [← Category.assoc, hce a, Sigma.ι_comp_desc, ← Functor.map_comp, hd a]
  have hEt : ∀ a : {i : I // i ∈ t},
      Etale ((BigFppfOver.toScheme B S hS).map (j a.1)) := by
    intro a
    have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j a.1)) := hjOI _
    infer_instance
  have _ : HasRingHomProperty @Etale RingHom.Etale := inferInstance
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  have hdEtale : Etale ((BigFppfOver.toScheme B S hS).map d) := by
    have hdescEtale : Etale (Sigma.desc fun a : {i : I // i ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (j a.1)) :=
      IsZariskiLocalAtSource.sigmaDesc fun a => hEt a
    have hrw : (BigFppfOver.toScheme B S hS).map d =
        e'.inv ≫ Sigma.desc fun a : {i : I // i ∈ t} =>
          (BigFppfOver.toScheme B S hS).map (j a.1) := by
      rw [← hdesc, Iso.inv_hom_id_assoc]
    rw [hrw]
    infer_instance
  refine ⟨Z, yoneda.map d ≫ f, hZaff,
    etale_comp_of_scheme B S hS d f hdEtale hfE, fun x hx => ?_⟩
  -- A point of the prescribed set lies in the image of one of the chosen summands.
  obtain ⟨i, hit, z, hz⟩ := Set.mem_iUnion₂.1 (ht hx)
  have hcomp : yoneda.map (cι ⟨i, hit⟩) ≫ yoneda.map d ≫ f = yoneda.map (j i) ≫ f := by
    rw [← Category.assoc, ← Functor.map_comp, hd ⟨i, hit⟩]
  exact ⟨pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (cι ⟨i, hit⟩)) z, by
    rw [← pointsMap_comp_apply, hcomp]; exact hz⟩

end AlgebraicGeometry.Space

end
