module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# An affine étale chart through finitely many prescribed points

`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartAtPoint.lean` produces an affine étale chart
of an algebraic space over `S` through *one* prescribed point. The proof of Stacks 082H needs
one through *finitely many*: "choose an affine scheme `Z` and an étale morphism `Z ⟶ X` such
that the `xᵢ` are in the image". This file produces it.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_chart_at_finite_points`: an algebraic space
  over `S` and finitely many of its points admit an étale morphism from an object of the big
  fppf site with affine underlying scheme whose image on points contains all of them.

## Implementation notes

The one-point statement cannot simply be applied once per point and the results added up: the
charts it returns are morphisms of *presheaves* out of distinct representables, and assembling
them into a single morphism out of a disjoint union would need the sheaf condition on the
target. Instead a single chart is used throughout. Tag 03FX
(`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`) presents one surjective
étale chart `f : h_U ⟶ F` whose underlying scheme is the disjoint union of affine objects
`W i` of the site along morphisms `j i : W i ⟶ U`; each prescribed point lifts to `|U|` by
surjectivity and then lies in exactly one summand. The disjoint union `T` of the finitely many
summands named this way is again an object of the site
(`AlgebraicGeometry.BigFppfOver.exists_coproduct_of_mk_le_aleph0`), its underlying scheme is a
finite disjoint union of affine schemes and hence affine, and the universal property of that
coproduct in the site supplies a *site* morphism `d : T ⟶ U` restricting to the `j (k i)`.
The chart is then `yoneda.map d ≫ f`, which needs no gluing at all.

Étaleness of the underlying scheme morphism of `d` is Zariski-local on its source, so it
follows from étaleness of the open immersions `j (k i)`; étaleness of the chart is then Tag
03EC (`AlgebraicGeometry.Space.etale_comp_of_scheme`). The index type of the coproduct is
`ULift (Fin n)` rather than `Fin n` because the family taken by
`AlgebraicGeometry.BigFppfOver.exists_coproduct_of_mk_le_aleph0` is indexed by a type in the
universe of the site.

Nothing here carries a Stacks tag. Stacks 082H asserts the existence of such a chart as one
step of a longer proof and does not state it as a result of its own, and Tag 03FX, which does
the work, is already carried by
`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`.

## References

* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale chart through finitely many prescribed points.** Any finite family of
points of an algebraic space over `S` lies in the image on points of an étale morphism from an
object of the big fppf site whose underlying scheme is affine.

No surjectivity is asserted and none is available: the chart is a disjoint union of finitely
many affine summands of a surjective chart, chosen to cover the prescribed points. This is the
step "choose an affine scheme `Z` and an étale morphism `Z ⟶ X` such that the `xᵢ` are in the
image" of the proof of Stacks 082H. -/
theorem exists_affine_etale_chart_at_finite_points
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {n : ℕ} (x : Fin n → points B S hS F) :
    ∃ (Z : BigFppfOver B S hS) (b : yoneda.obj Z ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      ∀ i, ∃ z : points B S hS (yoneda.obj Z),
        pointsMap B S hS (yoneda.obj Z) b z = x i := by
  classical
  obtain ⟨U, f, I, W, j, e, hfSurj, hfE, hWaffine, hιe, hjOI, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  -- The chart is surjective on points, so each prescribed point comes from one of the chart.
  have hsurj := isSurjective_of_presheafSurjective B S hS f hfSurj
  choose y hy using fun i : Fin n => hsurj (x i)
  -- The corresponding point of the chart's underlying scheme lies in a single summand.
  have hcov := (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1
  choose k w hw using fun i : Fin n => hcov (pointsToScheme B S hS U (y i))
  -- The disjoint union of the finitely many summands met is again an object of the site.
  obtain ⟨T, c, e', hce, huniv⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (B := B) (S := S) (hS := hS)
      (σ := ULift.{u} (Fin n)) Cardinal.mk_le_aleph0 fun a => W (k a.down)
  obtain ⟨d, hd⟩ := huniv fun a : ULift.{u} (Fin n) => j (k a.down)
  -- Its underlying scheme is a finite disjoint union of affine schemes, hence affine.
  have hWa : ∀ a : ULift.{u} (Fin n),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (W (k a.down))) := fun a => hWaffine _
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e'.inv
  -- The morphism to the chart is a coproduct of open immersions, hence étale.
  have hdesc : e'.hom ≫ (BigFppfOver.toScheme B S hS).map d =
      Sigma.desc fun a : ULift.{u} (Fin n) =>
        (BigFppfOver.toScheme B S hS).map (j (k a.down)) := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [← Category.assoc, hce a, Sigma.ι_comp_desc, ← Functor.map_comp, hd a]
  have hEt : ∀ a : ULift.{u} (Fin n),
      Etale ((BigFppfOver.toScheme B S hS).map (j (k a.down))) := by
    intro a
    have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j (k a.down))) := hjOI _
    infer_instance
  have _ : HasRingHomProperty @Etale RingHom.Etale := inferInstance
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  have hdEtale : Etale ((BigFppfOver.toScheme B S hS).map d) := by
    have hdescEtale : Etale (Sigma.desc fun a : ULift.{u} (Fin n) =>
        (BigFppfOver.toScheme B S hS).map (j (k a.down))) :=
      IsZariskiLocalAtSource.sigmaDesc fun a => hEt a
    have hrw : (BigFppfOver.toScheme B S hS).map d =
        e'.inv ≫ Sigma.desc fun a : ULift.{u} (Fin n) =>
          (BigFppfOver.toScheme B S hS).map (j (k a.down)) := by
      rw [← hdesc, Iso.inv_hom_id_assoc]
    rw [hrw]
    infer_instance
  refine ⟨T, yoneda.map d ≫ f, hTaff,
    etale_comp_of_scheme B S hS d f hdEtale hfE, fun i => ?_⟩
  -- The prescribed point is the image of the point of the summand that met it.
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS T
    ((BigFppfOver.toScheme B S hS).map (c ⟨i⟩) (w i))
  refine ⟨z, ?_⟩
  have hdz : pointsMap B S hS (yoneda.obj T) (yoneda.map d) z = y i := by
    refine injective_pointsToScheme B S hS U ?_
    rw [pointsToScheme_pointsMap_yoneda, hz, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
      hd ⟨i⟩, hw i]
  rw [pointsMap_comp_apply, hdz, hy i]

end AlgebraicGeometry.Space

end
