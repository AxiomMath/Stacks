module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartNeighborhood

/-!
# The small étale neighbourhood of a point of a fibre, with its morphism of charts

Let `X ⟶ Y` be a morphism of algebraic spaces over `S`, let `V ⟶ Y` be a surjective étale
scheme chart of the target and let `Spec k' ⟶ Y` be a point of the target which factors through
`V`, with `F = X ×_Y Spec k'` the fibre. For a geometric point `z` of `F`,
`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange` produces a surjective
étale scheme chart `U` of `X` over `V` and a small étale neighbourhood of `z` whose chart scheme
is the base change `U_v ×_{Spec κ(v)} Spec k'` of the scheme-theoretic fibre of `U ⟶ V`. This
file records, in addition, the morphism of the site from the chart of that neighbourhood to `U`,
its commuting square over `F ⟶ X`, and the compatibility of the isomorphism of chart schemes
with the two projections of the base change.

## Main results

* `AlgebraicGeometry.Space.exists_pointed_smallEtaleNeighborhood_chart_eq`: a surjective étale
  atlas is, as a chart, the chart of a small étale neighbourhood of a prescribed geometric point.
* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange_chartMap`: the small
  étale neighbourhood of a point of the fibre, together with the morphism of charts.

## Implementation notes

The morphism of the site out of the chart of the neighbourhood is the first projection of the
fibre product `U ×_V Spec k'` read through the equality of charts that
`AlgebraicGeometry.Space.exists_pointed_smallEtaleNeighborhood` returns; its commuting square
over `F ⟶ X` is the commutativity of the cartesian square the chart comes from, and the
compatibility with the isomorphism is the identification of the first projection of that fibre
product with the composite of the two projections of the base-changed fibre.

## References

* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A surjective étale scheme atlas is, as a chart, the chart of a small étale neighbourhood of
any prescribed geometric point.** This is
`AlgebraicGeometry.Space.exists_pointed_smallEtaleNeighborhood` with the equality returned one of
objects of `CostructuredArrow` rather than of their sources, so
`CategoryTheory.CostructuredArrow.w` recovers the chart morphism of the neighbourhood as the atlas
precomposed with the induced identification. -/
theorem exists_pointed_smallEtaleNeighborhood_chart_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    Nonempty { V : SmallEtaleNeighborhood x // V.chart.obj = CostructuredArrow.mk f } := by
  obtain ⟨p, hp⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U f).mp hSurj x.image
  obtain ⟨xU, -, hxU⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hF f
    ((isEtale_iff_presheaf_of_yoneda B S hS f).mpr hEtale) x p hp
  have hsite : Opposite.op xU.val.siteObject = Opposite.op x.val.siteObject :=
    congrArg Opposite.op
      (congrArg (fun z : FieldValuedPoint B S hS F ↦ z.siteObject) hxU)
  have hmapval : ∀ (p : FieldValuedPoint B S hS (yoneda.obj U)) (q : FieldValuedPoint B S hS F)
      (hsite : Opposite.op p.siteObject = Opposite.op q.siteObject)
      (_ : FieldValuedPoint.map B S hS (yoneda.obj U) f p = q),
      hsite ▸ f.app (Opposite.op p.siteObject) p.value = q.value := by
    intro p q hsite h
    have hv : HEq (f.app (Opposite.op p.siteObject) p.value) q.value := by
      cases h
      rfl
    exact eq_of_heq ((eqRec_heq hsite _).trans hv)
  have hcast : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ} (h : X = Y) (a : F.obj X),
      F.map (eqToHom h) a = h ▸ a := by
    intro X Y h a
    rw [eqToHom_map]
    cases h
    rfl
  refine ⟨⟨⟨⟨CostructuredArrow.mk f, hEtale⟩,
    (yoneda.obj U).map (eqToHom hsite) xU.val.value, ?_⟩, rfl⟩⟩
  calc
    f.app (Opposite.op x.val.siteObject)
          ((yoneda.obj U).map (eqToHom hsite) xU.val.value) =
        F.map (eqToHom hsite) (f.app (Opposite.op xU.val.siteObject) xU.val.value) := by
      simpa only [types_comp_apply] using
        congrArg (fun k ↦ k xU.val.value) (f.naturality (eqToHom hsite))
    _ = x.val.value := (hcast hsite _).trans (hmapval xU.val x.val hsite hxU)

/-- A base change of a morphism in `P.inverseImage toScheme`-relative form is again in that form. -/
private theorem presheaf_inverseImage_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {T₁ T₂ T₃ T₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : T₁ ⟶ T₂} {g : T₁ ⟶ T₃} {h : T₂ ⟶ T₄} {i : T₃ ⟶ T₄} (sq : IsPullback f g h i)
    (hi : (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) h) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) g :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (P.inverseImage (BigFppfOver.toScheme B S hS))).of_isPullback sq hi

/-- Composing a relative `P`-morphism with the base change of a relative `P`-morphism is again
relative `P`. -/
private theorem presheaf_inverseImage_comp_fst (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hP : P.IsStableUnderComposition)
    {T X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : T ⟶ Z} {fst : Z ⟶ X} {snd : Z ⟶ W}
    {g : X ⟶ Y} {q : W ⟶ Y}
    (ha : (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) a)
    (sq : IsPullback fst snd g q)
    (hq : (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) q) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) (a ≫ fst) :=
  haveI := hP
  MorphismProperty.comp_mem _ _ _ ha (presheaf_inverseImage_of_isPullback B S hS P sq.flip hq)

/-- **The small étale neighbourhood of a point of a fibre over a field factoring through a chart,
with its morphism of charts.** Let `X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`
with `X` and `Y` algebraic spaces, let `q : V ⟶ Y` be a scheme chart of the target which is
surjective and étale after every represented base change, let `k'` be a field in the site and let
`ρ : Spec k' ⟶ V` be a morphism of the site, so that `Spec k' ⟶ Y` factors through the chart.
Let `F` be the fibre `X ×_Y Spec k'`, presented by a cartesian square, and let `z` be any
geometric point of `F`.

Then there is a surjective étale scheme chart `U ⟶ X` lying over `V`, with `v` the image of the
closed point of `Spec k'` under `ρ` and `φ : κ(v) ⟶ k'` the induced extension of residue
fields, together with a small étale neighbourhood of `z` and a morphism `U' ⟶ U` of the site
from its chart, commuting with `ξ` over the two charts, whose morphism of schemes is the
composite of an isomorphism `U' ≅ U_v ×_{Spec κ(v)} Spec k'` with the two projections of the
base change `U_v ×_{Spec κ(v)} Spec k'` of the scheme-theoretic fibre of `U ⟶ V` at `v` to
`U_v` and then to `U`. -/
theorem exists_smallEtaleNeighborhood_fiberBaseChange_chartMap
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
      (N : SmallEtaleNeighborhood z) (gNU : N.chart.obj.left ⟶ U)
      (v : (BigFppfOver.toScheme B S hS).obj V)
      (φ : ((BigFppfOver.toScheme B S hS).obj V).residueField v ⟶ CommRingCat.of k'),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) aX ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) aX ∧
      yoneda.map gUV ≫ q = aX ≫ gXY ∧
      N.chart.obj.hom ≫ ξ = yoneda.map gNU ≫ aX ∧
      v = (BigFppfOver.toScheme B S hS).map ρ (IsLocalRing.closedPoint k') ∧
      ∃ e : chartScheme N.chart ≅
          pullback (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v)
            (Spec.map φ),
        e.hom ≫ pullback.fst
              (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ) ≫
            ((BigFppfOver.toScheme B S hS).map gUV).fiberι v =
          (BigFppfOver.toScheme B S hS).map gNU := by
  have hP : IsAlgebraicSpace B S hS (pullback gXY q) :=
    isAlgebraicSpace_pullback B S hS gXY q hX (isAlgebraicSpace_yoneda B S hS V) hY
  obtain ⟨U, a, haSurj, haEtale⟩ := hP.exists_atlas
  let gUV : U ⟶ V := yoneda.preimage (a ≫ pullback.snd gXY q)
  have hgUV : yoneda.map gUV = a ≫ pullback.snd gXY q := yoneda.map_preimage _
  have sqP : IsPullback (pullback.fst gXY q) (pullback.snd gXY q) gXY q :=
    IsPullback.of_hasPullback gXY q
  let L : F ⟶ pullback gXY q :=
    pullback.lift ξ (π ≫ yoneda.map ρ) (by rw [sq.w, Category.assoc])
  have hLfst : L ≫ pullback.fst gXY q = ξ := pullback.lift_fst _ _ _
  have hLsnd : L ≫ pullback.snd gXY q = π ≫ yoneda.map ρ := pullback.lift_snd _ _ _
  have sq' : IsPullback L π (pullback.snd gXY q) (yoneda.map ρ) :=
    IsPullback.of_right (by rwa [hLfst]) hLsnd sqP
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hW : IsPullback (yoneda.map (pullback.fst gUV ρ)) (yoneda.map (pullback.snd gUV ρ))
      (a ≫ pullback.snd gXY q) (yoneda.map ρ) := by
    rw [← hgUV]
    exact (IsPullback.of_hasPullback gUV ρ).map yoneda
  let M : yoneda.obj (pullback gUV ρ) ⟶ F :=
    sq'.flip.lift (yoneda.map (pullback.snd gUV ρ))
      (yoneda.map (pullback.fst gUV ρ) ≫ a) (by rw [Category.assoc, hW.w])
  have hMπ : M ≫ π = yoneda.map (pullback.snd gUV ρ) := sq'.flip.lift_fst _ _ _
  have hML : M ≫ L = yoneda.map (pullback.fst gUV ρ) ≫ a := sq'.flip.lift_snd _ _ _
  have hMξ : M ≫ ξ = yoneda.map (pullback.fst gUV ρ) ≫ a ≫ pullback.fst gXY q := by
    rw [← hLfst, ← Category.assoc, hML, Category.assoc]
  have sqchart : IsPullback (yoneda.map (pullback.fst gUV ρ)) M a L :=
    (IsPullback.of_right (by rw [hMπ]; exact hW.flip) hML sq'.flip).flip
  obtain ⟨⟨N, hN⟩⟩ := exists_pointed_smallEtaleNeighborhood_chart_eq B S hS F hF z M
    (presheaf_inverseImage_of_isPullback B S hS (@Surjective.{u}) sqchart haSurj)
    (presheaf_inverseImage_of_isPullback B S hS (@Etale.{u}) sqchart haEtale)
  have hNleft : N.chart.obj.left = pullback gUV ρ := congrArg (fun A => A.left) hN
  have hNhom : yoneda.map (eqToHom hNleft) ≫ M = N.chart.obj.hom := by
    have h := CostructuredArrow.w (eqToHom hN)
    rwa [CostructuredArrow.eqToHom_left] at h
  obtain ⟨v, φ, hs, hv⟩ := exists_specResidueField_factorization (K := k')
    ((BigFppfOver.toScheme B S hS).map ρ)
  refine ⟨U, gUV, a ≫ pullback.fst gXY q, N, eqToHom hNleft ≫ pullback.fst gUV ρ, v, φ,
    presheaf_inverseImage_comp_fst B S hS (@Surjective.{u})
      surjective_isStableUnderComposition.{u} haSurj sqP hqS,
    presheaf_inverseImage_comp_fst B S hS (@Etale.{u})
      etale_isStableUnderComposition.{u} haEtale sqP hqE,
    by simp only [hgUV, Category.assoc, ← pullback.condition], ?_, hv,
    eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hNleft) ≪≫
      PreservesPullback.iso (BigFppfOver.toScheme B S hS) gUV ρ ≪≫
      (isPullback_fiberBaseChange ((BigFppfOver.toScheme B S hS).map gUV) v φ _
        hs).isoPullback.symm,
    ?_⟩
  · rw [← hNhom, Category.assoc, hMξ, Functor.map_comp, Category.assoc]
  · rw [Functor.map_comp, eqToHom_map]
    simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_fst, PreservesPullback.iso_hom_fst]

end AlgebraicGeometry.Space

end
