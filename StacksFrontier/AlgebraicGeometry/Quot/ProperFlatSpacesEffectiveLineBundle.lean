module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfScheme
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatVersalPowerSeries
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesEffectiveLevels
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeInvertiblePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmoothNontrivialInvertibleRegularLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleAdicFibreDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleAdicFibreSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartArrowIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsNonempty
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafFirstCohomologyTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionLocal
public import StacksFrontier.RingTheory.MvPowerSeries.RegularRing

/-!
# An effective versal deformation of a surface carries a nontrivial line bundle

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism, smooth of relative dimension `2`,
from an integral scheme with `H¹(X, 𝒪_X) = 0` (a K3 surface, say). Let `η` be a versal formal
object over `R ≅ k[[x_1, …, x_n]]` of the predeformation category of the point `x₀ = [X]` of
`p'_{fp, flat, proper}`, and `ξ` its image, a formal object of `p'_{fp, flat, proper}`.

If `ξ` were effective, it would come from a flat proper algebraic space `Y` over `Spec R`
(`AlgebraicGeometry.exists_relocalizeSpace_adicFibreSpaceOf_iso_of_isEffective`). Following the
discussion before Stacks 0D1R: `Y` is smooth over the regular `R`, so it carries an effective
Cartier divisor `D` with `𝒪_Y(D)` nontrivial; as `H¹(X, 𝒪_X) = 0`, its restriction `L₀` to the
closed fibre `Y₀ ≅ X` is nontrivial; the canonical section of `𝒪_Y(D)` gives a nonzero section of
`L₀`; and by versality every infinitesimal deformation of `X` maps to `Y` compatibly with
`X ≅ Y₀ ⟶ Y`. This file records that output, which the proof of Stacks 0D1R contradicts.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.exists_invertibleModule_of_isEffective`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

/-- On a proper flat algebraic space `Y` over a complete Noetherian local ring `A` with a point,
the invertible module `𝒪_Y(D)` of an effective Cartier divisor restricts to the closed fibre
`Y₀ = Y ×_{Spec A} Spec(A / 𝔪)` with a nonzero section: the restriction of the canonical section
need not be nonzero, but some graded piece of it is
(`AlgebraicGeometry.exists_unit_hom_adicFibre_zero_ne_zero`). -/
theorem exists_unit_hom_adicFibre_zero_associatedInvertibleSheaf_ne_zero
    (B : BigFppfSite.{u}) {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] {hA : B.Contains (Spec (.of A))}
    (Y : AlgebraicSpaces B (Spec (.of A)) hA) (fY : Y ⟶ schemeSpace (baseObject A B hA))
    (hprop : IsProper B (Spec (.of A)) hA fY.hom)
    (hflat : IsFlat B (Spec (.of A)) hA fY.hom)
    (D : ClosedSubspaces B (Spec (.of A)) hA Y.1)
    (hD : IsEffectiveCartierDivisor B (Spec (.of A)) hA Y D)
    (hne : Nonempty (points B (Spec (.of A)) hA Y.1)) :
    ∃ t : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B
        (Spec (.of A)) hA (adicFibreSpaceOf A (maximalIdeal A) B hA Y fY 0).1
          (adicFibreSpaceOf A (maximalIdeal A) B hA Y fY 0).2).O)) ⟶
        (modulePullback B (Spec (.of A)) hA
          (adicFibreInclusion A (maximalIdeal A) B hA Y fY 0)).obj
            (associatedInvertibleSheaf B _ hA Y D hD), t ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_unit_hom_associatedInvertibleSheaf_ne_zero B _ hA Y D hD hne
  exact exists_unit_hom_adicFibre_zero_ne_zero (maximalIdeal A) Y fY hprop hflat _
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (associatedInvertibleSheaf_isInvertible B _ hA Y D hD)) s hs

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **An effective versal deformation of a surface with `H¹(𝒪) = 0` carries a nontrivial line
bundle extending to every infinitesimal deformation** (the input of the contradiction in the
proof of Stacks 0D1R). Let `f : X ⟶ Spec k` be proper and smooth of relative dimension `2`
with `X` integral and `H¹(X, 𝒪_X) = 0`, and let `η` be a versal formal object over a power
series ring `k[[x_1, …, x_n]]` of the predeformation category of the point `x₀ = [X]` of
`p'_{fp, flat, proper}`. If the formal object `ξ` of `p'_{fp, flat, proper}` defined by `η` is
effective, there are an algebraic space `𝒴` over `Spec k`, an invertible `𝒪_𝒴`-module `L` and
a morphism `g₀ : X ⟶ 𝒴` such that `g₀^* L` is not trivial and has a nonzero section, and such
that for every deformation `x₀ ⟶ x` over an Artinian base, `g₀` factors through the total space
of `x`. -/
theorem exists_invertibleModule_of_isEffective [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 2 f] [IsIntegral X]
    (hH1 : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      (SheafOfModules.unit _)))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
        𝟙 (Spec (.of k))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))))
    (η : Deformation.FormalObject (ProperFlatSpaceDeformation.predeformationCat B (Spec (.of k)) hk
      (𝟙 _) (point B k hk f) (projection_point B k hk f)).projection)
    (hR : ∃ n : ℕ, Nonempty (η.base ≃ₐ[k] MvPowerSeries (Fin n) k))
    (hη : IsVersal (ProperFlatSpaceDeformation.isDeformationCategory_predeformationCat B
      (Spec (.of k)) hk (𝟙 _) (point B k hk f) (projection_point B k hk f)
        hfinite).predeformation.cofibered η)
    (hξ : Deformation.Artin.FormalObject.IsEffective B (Spec (.of k)) hk
      (cartesianProperFlatProjection B (Spec (.of k)) hk)
      (cartesianProperFlatProjection_isFiberedInGroupoids B (Spec (.of k)) hk)
      (FormalObject.ofPredeformation B (Spec (.of k)) hk (𝟙 _)
        (cartesianProperFlatProjection B (Spec (.of k)) hk) (point B k hk f)
        (projection_point B k hk f) hfinite η)) :
    ∃ (𝒴 : AlgebraicSpaces B (Spec (.of k)) hk)
      (L : Space.Modules.{u, u} B (Spec (.of k)) hk 𝒴.1 𝒴.2)
      (_ : Space.IsInvertibleModule 𝒴 L) (g₀ : schemeSpace (siteObj B k hk f) ⟶ 𝒴),
      ¬ Nonempty ((Space.modulePullback B (Spec (.of k)) hk g₀).obj L ≅
        SheafOfModules.unit _) ∧
      (∃ s : SheafOfModules.unit _ ⟶ (Space.modulePullback B (Spec (.of k)) hk g₀).obj L,
        s ≠ 0) ∧
      ∀ a : DeformationObject (𝟙 (Spec (.of k)))
          (cartesianProperFlatProjection B (Spec (.of k)) hk ⋙ Over.post B.inclusion)
          (point B k hk f) (projection_point B k hk f),
        ∃ g : a.point.obj.obj.left ⟶ 𝒴, a.arrow.hom.hom.left ≫ g = g₀ := by
  -- The effective algebraization `Y` over `Spec R`.
  set ξ := FormalObject.ofPredeformation B (Spec (.of k)) hk (𝟙 _)
    (cartesianProperFlatProjection B (Spec (.of k)) hk) (point B k hk f)
    (projection_point B k hk f) hfinite η
  have hA : B.Contains (Spec (.of ξ.base.R)) := ξ.contains_spec_base
  obtain ⟨Y, fY, hfp, hflat, hprop, e, he1, he2⟩ :=
    exists_relocalizeSpace_adicFibreSpaceOf_iso_of_isEffective ξ hξ hA
  have := ξ.base.noetherian
  have := ξ.base.complete
  obtain ⟨n, ⟨φ⟩⟩ := hR
  have := MvPowerSeries.isRegularRing_fin k n
  have : IsRegularRing ξ.base.R := IsRegularRing.of_ringEquiv φ.symm.toRingEquiv
  let h := formalBaseHom hk ξ.base hA
  let ι₀ := Space.adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY 0
  have hι₀ : yoneda.relativelyRepresentable ι₀.hom :=
    (Space.isClosedImmersion_adicFibreFstHom ξ.base.R (maximalIdeal ξ.base.R) B hA Y.2
      fY.hom 0).rep
  -- The isomorphism `X ≅ Λ(Y₀)`.
  let a₀ := (predeformationCategory (𝟙 (Spec (.of k)))
    (cartesianProperFlatProjection B (Spec (.of k)) hk ⋙ Over.post B.inclusion)
      (point B k hk f) (projection_point B k hk f)).objects (η.level 0)
  have hr : IsIso a₀.arrow.hom.hom.right := isIso_arrow_hom_right_level_zero (𝟙 (Spec (.of k)))
    (point B k hk f) (projection_point B k hk f) η
  have hl : IsIso a₀.arrow.hom.hom.left :=
    @isIso_hom_left_of_isIso_hom_right _ _ _ _ _ a₀.arrow hr
  have hl' : IsIso ((ObjectProperty.ι _).map a₀.arrow.hom.hom.left) :=
    Functor.map_isIso (ObjectProperty.ι _) a₀.arrow.hom.hom.left
  let ψ : schemeSpace (siteObj B k hk f) ≅ Space.relocalizeSpace B hA hk h
      (Space.adicFibreSpaceOf ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY 0) :=
    @asIso _ _ _ _ a₀.arrow.hom.hom.left hl ≪≫ (e 0).symm
  -- `Y` has a point.
  have hne : Nonempty (Space.points B (Spec (.of ξ.base.R)) hA Y.1) := by
    have h0 : Nonempty (Space.points B (Spec (.of k)) hk (yoneda.obj (siteObj B k hk f))) :=
      Space.nonempty_points_yoneda_of_nonempty B hk _
        (inferInstanceAs (Nonempty X))
    have h1 := Space.nonempty_points_of_hom B hk ψ.hom.hom h0
    exact Space.nonempty_points_of_hom B hA ι₀.hom
      ((Space.nonempty_points_relocalizeSpace_iff B hA hk h _).2 h1)
  -- The closed fibre `Y₀` is smooth of relative dimension `2` on every étale chart.
  have hP := isEtaleLocalOnSourceAndTarget_smoothOfRelativeDimension.{u} 2
  have hfib : Space.HoldsOnEveryEtaleChart B (Spec (.of ξ.base.R)) hA
      (@SmoothOfRelativeDimension 2)
      (Space.adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY 0).hom := by
    have hx : Space.HoldsOnEveryEtaleChart B (Spec (.of k)) hk (@SmoothOfRelativeDimension 2)
        (point B k hk f).toBase :=
      Space.holdsOnEveryEtaleChart_yoneda_map B (Spec (.of k)) hk hP (toBaseObj B k hk f)
        (inferInstanceAs (SmoothOfRelativeDimension 2 f))
    have hsq := CartesianProperFlatSpaces.isPullback_hom a₀.arrow
    have hl : Space.HoldsOnEveryEtaleChart B (Spec (.of k)) hk (@SmoothOfRelativeDimension 2)
        a₀.point.toBase :=
      (Space.holdsOnEveryEtaleChart_iff_of_comm_iso B (Spec (.of k)) hk _ _ _
        (@asIso _ _ _ _ ((ObjectProperty.ι _).map a₀.arrow.hom.hom.left) hl')
        (yoneda.mapIso (@asIso _ _ _ _ a₀.arrow.hom.hom.right hr)) hsq.w).1 hx
    have hs : Space.HoldsOnEveryEtaleChart B (Spec (.of k)) hk (@SmoothOfRelativeDimension 2)
        (properFlatLevelStructure ξ 0).hom :=
      (Space.holdsOnEveryEtaleChart_iff_of_comm_iso B (Spec (.of k)) hk _ _ _ (Iso.refl _)
        (yoneda.mapIso (eqToIso (properFlatLevel_right_eq ξ 0)))
        (Category.id_comp _)).1 hl
    have hr : Space.HoldsOnEveryEtaleChart B (Spec (.of k)) hk (@SmoothOfRelativeDimension 2)
        (Space.relocalizeHom B hA hk h
          (Space.adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY 0)).hom :=
      (Space.holdsOnEveryEtaleChart_hom_iff_of_comm_iso B (Spec (.of k)) hk _ _ _ (e 0)
        (relocalizeAdicThickeningIso ξ.base hA ξ.contains 0) (he1 0)).2 hs
    exact (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B _ _ hA hk h _
      (Space.adicFibreProjection ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY 0).hom).1 hr
  -- The nontrivial invertible module `𝒪_Y(D)`.
  obtain ⟨D, hD, hnt⟩ := Space.exists_isEffectiveCartierDivisor_not_isTrivial_of_isRegularRing B
    ξ.base.R hA Y fY.hom hfp hflat hprop 2 two_ne_zero hfib hne
  let L := Space.associatedInvertibleSheaf B _ hA Y D hD
  have hL : Space.IsInvertibleModule Y L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Space.associatedInvertibleSheaf_isInvertible B _ hA Y D hD)
  refine ⟨Space.relocalizeSpace B hA hk h Y,
    (Space.moduleRelocalizeEquivalence B _ _ hA hk h Y).inverse.obj L,
    Space.isInvertibleModule_relocalize h L hL, ψ.hom ≫ Space.relocalizeHom B hA hk h ι₀,
    ?_, ?_, fun a => ?_⟩
  · rw [Space.nonempty_modulePullback_relocalize_iso_unit_iff h ι₀ hι₀ L ψ]
    intro h0
    exact hnt (Space.nonempty_iso_unit_of_adicFibre_zero_iso_unit (maximalIdeal ξ.base.R) Y fY
      hprop hflat (Space.isZero_rightDerived_one_unit_of_iso_relocalizeSpace h
        (siteObj B k hk f) _ ψ hH1) L hL h0)
  · exact (Space.exists_unit_hom_modulePullback_relocalize_ne_zero_iff h ι₀ hι₀ L ψ).2
      (Space.exists_unit_hom_adicFibre_zero_associatedInvertibleSheaf_ne_zero B Y fY hprop hflat
        D hD hne)
  · obtain ⟨g, hg⟩ := exists_comp_eq_of_isVersal (𝟙 (Spec (.of k))) (point B k hk f)
      (projection_point B k hk f) hfinite η
      (ProperFlatSpaceDeformation.isDeformationCategory_predeformationCat B (Spec (.of k)) hk
        (𝟙 _) (point B k hk f) (projection_point B k hk f) hfinite).predeformation hη
      (levelToAlgebraization e) (transition_comp_levelToAlgebraization e he2) a
    exact ⟨g, hg.trans (Category.assoc _ _ _).symm⟩

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end
