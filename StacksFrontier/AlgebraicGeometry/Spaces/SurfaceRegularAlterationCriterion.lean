module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationBirationalIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalSurfaceSingularPointsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationNormalizationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkBaseChangeNormalCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceResolutionCriterion

/-!
# A regular alteration of a two-dimensional space gives condition (4) of Stacks 0BHY

Let `Y` be a two-dimensional integral Noetherian algebraic space over a scheme `S` admitting an
alteration `f : X ⟶ Y` with `X` regular. Then every normalization `D : Y^ν ⟶ Y` satisfies
condition (4) of [Stacks, Tag 0BHY]: `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular
points, and the completion of the henselian local ring of `Y^ν` at each of them is normal.

This is the implication (1) `⇒` (4) of [Stacks, Tag 0BHY].

## The argument

* Finiteness of `Y^ν ⟶ Y` is [Stacks, Tag 0BHT], in the namespace `AlgebraicGeometry.Space`,
  `NormalizationData.isFinite_hom_of_regular_alteration_of_isQuasiCompactSpace`.
* The alteration factors through the normalization by a proper morphism `g : X ⟶ Y^ν`
  ([Stacks, Tag 0BB4]), which is dominant: the generic point of `X` maps to a point of
  codimension zero of `Y`, hence its image under `g` is a point of codimension zero of the
  integral space `Y^ν`, its generic point. `Y^ν` is integral, normal, quasi-compact (it is
  finite over the quasi-compact `Y`), its étale charts are locally Noetherian (it is locally of
  finite type over `Y`), and its dimension is at most two (it is integral over `Y`,
  [Stacks, Tag 0EDB]).
* Finiteness of the singular locus is
  `AlgebraicGeometry.Space.finite_setOf_not_isRegularAt_of_isProper`, which replaces the
  flatness step of the source by the openness of the flat locus; see that module for why the
  source's step "`f` is flat over `V` by [Stacks, Tag 00R4]" needs repair.
* Normality of the completed henselian local rings is
  `AlgebraicGeometry.Space.isNormalRing_adicCompletion_henselianLocalRing_of_isProper`, which
  makes precise the step "`X ×_Y Spec(𝒪^h_{Y^ν, y_i})` is a regular alteration of
  `Spec(𝒪^h_{Y^ν, y_i})` (some details omitted)" and applies [Stacks, Tag 0BHU]; it holds at
  every point of `Y^ν`, singular or not.

## Main results

* `NormalizationData.isSurfaceResolutionCriterion_of_exists_regular_alteration`, in the
  namespace `AlgebraicGeometry.Space`: the implication (1) `⇒` (4) of [Stacks, Tag 0BHY].

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BHT](https://stacks.math.columbia.edu/tag/0BHT)
* [Stacks Project, Tag 0BHU](https://stacks.math.columbia.edu/tag/0BHU)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0EDB](https://stacks.math.columbia.edu/tag/0EDB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace NormalizationData

/-- A lift through the normalization of a dominant morphism from an integral space is dominant. -/
theorem isDominant_of_comp_hom_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS Y) (hY : IsAlgebraicSpace B S hS Y)
    (hYint : IsIntegralSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXint : IsIntegralSpace B S hS X) {f : X ⟶ Y} (hf : IsDominant B S hS f)
    {g : X ⟶ D.space} (hg : g ≫ D.hom = f) : IsDominant B S hS g := by
  have hNint : IsIntegralSpace B S hS D.space := D.isIntegralSpace hY hYint
  have _ : IrreducibleSpace (points B S hS X) := hXint.2.2
  have _ : IrreducibleSpace (points B S hS D.space) := hNint.2.2
  have hsX := stacksSober_points_of_isDecentSpace B S hS hX hXint.2.1
  have _ : T0Space (points B S hS X) := (stacksSober_iff_t0_and_quasiSober.mp hsX).1
  have _ : QuasiSober (points B S hS X) := (stacksSober_iff_t0_and_quasiSober.mp hsX).2
  let ξ := genericPoint (points B S hS X)
  have hξ : localRingDimension B S hS ξ = 0 :=
    (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hXint.2.1 ξ).1
      (by rw [genericPoints_eq_singleton]; rfl)
  have hfξ := localRingDimension_eq_zero_of_isDominant_of_isIntegralSpace B S hS hX hY hXint
    hYint f hf ξ hξ
  have hgξ : localRingDimension B S hS (pointsMap B S hS X g ξ) = 0 := by
    refine D.localRingDimension_eq_zero_of_hom hY _ ?_
    rwa [← Function.comp_apply (f := pointsMap B S hS D.space D.hom), ← pointsMap_comp, hg]
  have hgen := (mem_genericPoints_iff_localRingDimension_eq_zero B S hS D.isAlgebraicSpace
    hNint.2.1 _).2 hgξ
  rw [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
    Set.mem_singleton_iff] at hgen
  rw [IsDominant, DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : z ∈ closure {pointsMap B S hS X g ξ} := by rw [hgen]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self ξ)) hz

/-- **Stacks 0BHY, (1) `⇒` (4).** Let `Y` be a two-dimensional integral Noetherian algebraic
space over `S` admitting an alteration `X ⟶ Y` with `X` regular. Then every normalization
`D : Y^ν ⟶ Y` satisfies condition (4) of Stacks 0BHY: the normalization morphism is finite, `Y^ν`
has finitely many singular points, and at each of them the completion of the henselian local
ring of `Y^ν` is normal. -/
theorem isSurfaceResolutionCriterion_of_exists_regular_alteration
    (hZ : B.Contains (⊤_ Scheme.{u})) (Y : AlgebraicSpaces B S hS)
    (hYdim : dimension B S hS Y.obj Y.property = 2)
    (hYnoeth : IsNoetherian B S hS hZ Y.obj) (hYint : IsIntegralSpace B S hS Y.obj)
    (h : ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X ⟶ Y.obj), IsAlteration B S hS f ∧
      HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (D : NormalizationData B S hS Y.obj) :
    D.IsSurfaceResolutionCriterion Y.property (hYint.isDecentSpace B S hS Y.obj) := by
  obtain ⟨X, f, hf, hXreg⟩ := h
  have hY : IsAlgebraicSpace B S hS Y.obj := Y.property
  have hX : IsAlgebraicSpace B S hS X := hf.2.2.1
  have hXint : IsIntegralSpace B S hS X := hf.2.2.2.1
  have hN : IsAlgebraicSpace B S hS D.space := D.isAlgebraicSpace
  have hfin : IsFinite B S hS D.hom :=
    NormalizationData.isFinite_hom_of_regular_alteration_of_isQuasiCompactSpace B S hS f hf hXreg
      hYnoeth.1 hYnoeth.2.2 D
  have hNdec : IsDecentSpace B S hS D.space := D.isDecentSpace hY (hYint.isDecentSpace B S hS Y.obj)
  have hNnorm : IsNormal B S hS D.space := D.isNormal hY
  have hNnoeth : HasEtaleLocalProperty B S hS D.space
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hN hY D.hom
      (isLocallyOfFiniteType_of_isFinite B S hS hN hY hfin) hYnoeth.2.2
  have hNqc : IsQuasiCompactSpace B S hS D.space := by
    obtain ⟨U, a, hUaff, haSurjP, haet⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.obj hY).mp
        hYnoeth.1
    obtain ⟨V, p, i, hVaff, -, hpb⟩ := hfin U hUaff a
    have hV := isAlgebraicSpace_yoneda B S hS V
    have hU := isAlgebraicSpace_yoneda B S hS U
    have hiet : IsEtale B S hS i := isEtale_of_isPullback_yoneda B S hS hpb.flip haet
    have hasurj : IsSurjective B S hS a :=
      (presheafSurjective_iff_isSurjective_yoneda B S hS Y.obj hY U a).mp haSurjP
    have hisurj : IsSurjective B S hS i :=
      isSurjective_of_isPullback B S hS
        (W := ⟨yoneda.obj V, hV⟩) (Z := ⟨yoneda.obj U, hU⟩) (X := ⟨D.space, hN⟩) (Y := Y)
        (p := ObjectProperty.homMk (yoneda.map p)) (q := ObjectProperty.homMk i)
        (g := ObjectProperty.homMk a) (f := ObjectProperty.homMk D.hom)
        (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hpb.flip) hasurj
    exact (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.space hN).mpr
      ⟨V, i, hVaff, (presheafSurjective_iff_isSurjective_yoneda B S hS D.space hN V i).mpr hisurj,
        hiet⟩
  have hNdim : dimension B S hS D.space hN ≤ 2 :=
    hYdim ▸ dimension_le_of_isIntegralHom B S hS hN hY D.hom (D.isIntegralHom_hom hY)
  obtain ⟨g, hg, -⟩ := D.existsUnique_lift_of_isAlteration f hf hXreg
  have hgp : IsProper B S hS g := D.isProper_lift hY hX hf.2.2.2.2.1 g hg
  have hgdom : IsDominant B S hS g := D.isDominant_of_comp_hom_eq hY hYint hX hXint hf.isDominant hg
  exact ⟨hfin, finite_setOf_not_isRegularAt_of_isProper B S hS hX hN hXint
      (D.isIntegralSpace hY hYint) hXreg hNnorm hNnoeth hNqc hNdim g hgp hgdom, fun y _ =>
    isNormalRing_adicCompletion_henselianLocalRing_of_isProper B S hS hN hNdec hX hNnorm
      hNnoeth g hgp (isSurjective_of_isProper_of_isDominant B S hS hN g hgp hgdom) hXreg y⟩

end NormalizationData

end AlgebraicGeometry.Space

end
