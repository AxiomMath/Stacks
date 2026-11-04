module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartNeighborhood

/-!
# A fibre chart neighbourhood compatible with a morphism of charts

Let `X ⟶ Y` be a morphism of algebraic spaces over `S`, let `V ⟶ Y` be a surjective étale
scheme chart of the target, let `Spec k' ⟶ Y` be a point of the target factoring through `V`
as `ρ : Spec k' ⟶ V`, and let `F = X ×_Y Spec k'` be the fibre.
`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange` produces, for a
geometric point `z` of `F`, a surjective étale scheme chart `U ⟶ X` lying over `V` and a small
étale neighbourhood of `z` whose chart scheme is isomorphic to `U_v ×_{Spec κ(v)} Spec k'`.

This file proves the same statement together with the compatibility of the neighbourhood with
the chart `U`: a morphism of the site `cU` from the chart of the neighbourhood to `U`, over
`U ⟶ X`, which the identification of the chart scheme carries to the composite
`U_v ×_{κ(v)} Spec k' ⟶ U_v ⟶ U`.

## Main results

* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange_compatible`: the small
  étale neighbourhood of a point of a fibre whose chart is a base-changed fibre, together with
  the morphism of charts `cU` and the identification carrying it to `U_v ×_{κ(v)} Spec k' ⟶ U`.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` and `Y` algebraic
spaces, let `q : V ⟶ Y` be a scheme chart of the target which is surjective and étale after every
represented base change, let `k'` be a field in the site and let `ρ : Spec k' ⟶ V` be a morphism of
the site. Let `F` be the fibre `X ×_Y Spec k'`, presented by a cartesian square, and let `z` be any
geometric point of `F`.

Then there is a surjective étale scheme chart `U ⟶ X` lying over `V`, with `v` the image of the
closed point of `Spec k'` under `ρ` and `φ : κ(v) ⟶ k'` the induced extension of residue
fields, together with a small étale neighbourhood of `z` whose chart scheme is the base change
`U_v ×_{Spec κ(v)} Spec k'` of the scheme-theoretic fibre of `U ⟶ V` at `v`, and a morphism of
the site `cU` from the chart of the neighbourhood to `U`: the chart of the neighbourhood lies
over `U ⟶ X` through `cU`, and the identification of its chart scheme carries `cU` to the
composite `U_v ×_{κ(v)} Spec k' ⟶ U_v ⟶ U`. -/
theorem exists_smallEtaleNeighborhood_fiberBaseChange_compatible
    {X Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hF : IsAlgebraicSpace B S hS F) (gXY : X ⟶ Y)
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    {k' : Type u} [Field k'] (hk' : B.Contains (Spec (.of k'))) (b' : Spec (.of k') ⟶ S)
    (ρ : (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V)
    {ξ : F ⟶ X} {π : F ⟶ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS))}
    (sq : IsPullback ξ π gXY (yoneda.map ρ ≫ q))
    (z : GeometricPoint B S hS F) :
    ∃ (U : BigFppfOver B S hS) (gUV : U ⟶ V) (aX : yoneda.obj U ⟶ X)
      (N : SmallEtaleNeighborhood z) (cU : N.chart.obj.left ⟶ U)
      (v : (BigFppfOver.toScheme B S hS).obj V)
      (φ : ((BigFppfOver.toScheme B S hS).obj V).residueField v ⟶ CommRingCat.of k'),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) aX ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) aX ∧
      yoneda.map gUV ≫ q = aX ≫ gXY ∧
      v = (BigFppfOver.toScheme B S hS).map ρ (IsLocalRing.closedPoint k') ∧
      N.chart.obj.hom ≫ ξ = yoneda.map cU ≫ aX ∧
      ∃ e : chartScheme N.chart ≅
          pullback (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v)
            (Spec.map φ),
        (BigFppfOver.toScheme B S hS).map cU =
          e.hom ≫ pullback.fst
              (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ) ≫
            ((BigFppfOver.toScheme B S hS).map gUV).fiberι v := by
  obtain ⟨U, a, haSurj, haEtale⟩ :=
    (isAlgebraicSpace_pullback B S hS gXY q hX (isAlgebraicSpace_yoneda B S hS V) hY).exists_atlas
  let gUV : U ⟶ V := yoneda.preimage (a ≫ pullback.snd gXY q)
  have hgUV : yoneda.map gUV = a ≫ pullback.snd gXY q := yoneda.map_preimage _
  have sqP : IsPullback (pullback.fst gXY q) (pullback.snd gXY q) gXY q :=
    IsPullback.of_hasPullback gXY q
  let α : F ⟶ pullback gXY q :=
    pullback.lift ξ (π ≫ yoneda.map ρ) (by rw [Category.assoc]; exact sq.w)
  have hαfst : α ≫ pullback.fst gXY q = ξ := pullback.lift_fst _ _ _
  have hαsnd : α ≫ pullback.snd gXY q = π ≫ yoneda.map ρ := pullback.lift_snd _ _ _
  have sqα : IsPullback α π (pullback.snd gXY q) (yoneda.map ρ) :=
    IsPullback.of_right (by rw [hαfst]; exact sq) hαsnd sqP
  have hW : IsPullback (yoneda.map (pullback.fst gUV ρ)) (yoneda.map (pullback.snd gUV ρ))
      (a ≫ pullback.snd gXY q) (yoneda.map ρ) := by
    rw [← hgUV]
    exact (IsPullback.of_hasPullback gUV ρ).map yoneda
  let chartMor : yoneda.obj (pullback gUV ρ) ⟶ F :=
    sqα.flip.lift (yoneda.map (pullback.snd gUV ρ)) (yoneda.map (pullback.fst gUV ρ) ≫ a)
      (by rw [Category.assoc, ← hgUV, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition])
  have hchartπ : chartMor ≫ π = yoneda.map (pullback.snd gUV ρ) := sqα.flip.lift_fst _ _ _
  have hchartα : chartMor ≫ α = yoneda.map (pullback.fst gUV ρ) ≫ a := sqα.flip.lift_snd _ _ _
  have sqchart : IsPullback chartMor (yoneda.map (pullback.fst gUV ρ)) α a :=
    IsPullback.of_right (by rw [hchartπ]; exact hW.flip) hchartα sqα.flip
  have bc (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      {A₁ A₂ A₃ A₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : A₁ ⟶ A₂} {g : A₁ ⟶ A₃} {h : A₂ ⟶ A₄}
      {i : A₃ ⟶ A₄} (sq : IsPullback f g h i)
      (hh : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B S hS))) h) :
      (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B S hS))) g :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq hh
  have hchartEtale := bc (@Etale.{u}) sqchart.flip haEtale
  have hchartSurj := bc (@Surjective.{u}) sqchart.flip haSurj
  obtain ⟨pt, hpt⟩ := exists_point_lift B S hS F hF z chartMor hchartSurj hchartEtale
  let N : SmallEtaleNeighborhood z :=
    { chart := ⟨CostructuredArrow.mk chartMor, hchartEtale⟩, point := pt, point_comp := hpt }
  have hfstSurj := bc (@Surjective.{u}) sqP.flip hqS
  have hfstEtale := bc (@Etale.{u}) sqP.flip hqE
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let s : Spec (.of k') ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    (BigFppfOver.toScheme B S hS).map ρ
  obtain ⟨v, φ, hs, hv⟩ := exists_specResidueField_factorization s
  have hfib := isPullback_fiberBaseChange ((BigFppfOver.toScheme B S hS).map gUV) v φ s hs
  refine ⟨U, gUV, a ≫ pullback.fst gXY q, N, pullback.fst gUV ρ, v, φ,
    MorphismProperty.comp_mem _ _ _ haSurj hfstSurj,
    MorphismProperty.comp_mem _ _ _ haEtale hfstEtale,
    by rw [hgUV]; simp only [Category.assoc, ← pullback.condition], hv, ?_,
    PreservesPullback.iso (BigFppfOver.toScheme B S hS) gUV ρ ≪≫ hfib.isoPullback.symm, ?_⟩
  · calc chartMor ≫ ξ = (chartMor ≫ α) ≫ pullback.fst gXY q := by rw [Category.assoc, hαfst]
      _ = yoneda.map (pullback.fst gUV ρ) ≫ a ≫ pullback.fst gXY q := by
        rw [hchartα, Category.assoc]
  · calc (BigFppfOver.toScheme B S hS).map (pullback.fst gUV ρ)
        = (PreservesPullback.iso (BigFppfOver.toScheme B S hS) gUV ρ).hom ≫
            pullback.fst ((BigFppfOver.toScheme B S hS).map gUV) s :=
          (PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) gUV ρ).symm
      _ = (PreservesPullback.iso (BigFppfOver.toScheme B S hS) gUV ρ).hom ≫
            hfib.isoPullback.inv ≫ pullback.fst
                (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v)
                (Spec.map φ) ≫
              ((BigFppfOver.toScheme B S hS).map gUV).fiberι v := by
          rw [hfib.isoPullback_inv_fst]
      _ = _ := by rw [Iso.trans_hom, Category.assoc]; rfl

end AlgebraicGeometry.Space

end
