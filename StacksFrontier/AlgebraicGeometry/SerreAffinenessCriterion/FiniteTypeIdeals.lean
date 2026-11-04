module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.CohomologyOverAQuasiCompactOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's criterion for affineness from finite type ideal sheaves

A quasi-compact and quasi-separated scheme on which the first cohomology of every quasi-coherent
sheaf of ideals *of finite type* vanishes is affine.

Only the finite type ideals are needed because every quasi-coherent module on a scheme is the
filtered colimit of its quasi-coherent finite type submodules, and on a quasi-separated
quasi-compact scheme cohomology commutes with filtered colimits. So the vanishing on finite type
ideals propagates to all quasi-coherent ideals, and
`Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal` applies.

## Main results

* `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_finiteType_ideal`: the finite type form of
  Serre's criterion for affineness.

## Implementation notes

The commutation of cohomology with filtered colimits is stated for a diagram indexed by a small
category, whereas the category of finite type quasi-coherent subobjects is only essentially
small, so the diagram is transported to `CategoryTheory.SmallModel` along
`CategoryTheory.equivSmallModel`.

The two topological hypotheses the commutation needs — a basis of quasi-compact opens and
quasi-compactness of pairwise intersections of quasi-compact opens — are the affine opens and
quasi-separatedness.

## References

* [Stacks Project, Tag 01XG](https://stacks.math.columbia.edu/tag/01XG)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreCriterion

/-- **Cohomology of a quasi-coherent module is detected on its finite type submodules.** On a
quasi-compact quasi-separated scheme, `H¹(X, ℱ) = 0` as soon as `H¹` vanishes on every
quasi-coherent finite type submodule of `ℱ`: the module is the filtered colimit of those
submodules, and `H¹(X, -)` commutes with filtered colimits. -/
theorem isZero_hgroup_one_of_isZero_on_finiteType (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent]
    (hH : ∀ G : AlgebraicGeometry.FiniteTypeQuasicoherentSubobject F,
      IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj G.obj))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 F) := by
  have hBasis : PrespectralSpace (X : Type u) := by
    refine PrespectralSpace.of_isTopologicalBasis
      (B := ((↑) : X.Opens → Set X) '' X.affineOpens) X.isBasis_affineOpens ?_
    rintro _ ⟨U, hU, rfl⟩
    exact hU.isCompact
  let K : Type (u + 1) := AlgebraicGeometry.FiniteTypeQuasicoherentSubobject F
  let eK : K ≌ SmallModel.{u} K := equivSmallModel.{u} K
  have hsmallFiltered : IsFiltered (SmallModel.{u} K) := IsFiltered.of_equivalence eK
  let D : SmallModel.{u} K ⥤ SheafOfModules.{u} X.ringCatSheaf :=
    eK.inverse ⋙ AlgebraicGeometry.finiteTypeQuasicoherentSubobjectFunctor F
  let c : Cocone D :=
    (AlgebraicGeometry.finiteTypeQuasicoherentSubobjectCocone F).whisker eK.inverse
  have hc : IsColimit c :=
    (AlgebraicGeometry.isColimit_finiteTypeQuasicoherentSubobjectCocone F).whiskerEquivalence
      eK.symm
  have hcolim : HasColimit D := ⟨⟨c, hc⟩⟩
  have hcmp : IsIso (colimit.post D (Hfunctor X.ringCatSheaf ⊤ 1)) :=
    Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact X.ringCatSheaf
      hBasis inferInstance D ⊤
      (by simpa using isCompact_univ) 1
  have hpres : PreservesColimit D (Hfunctor X.ringCatSheaf ⊤ 1) :=
    preservesColimit_of_isIso_post (Hfunctor X.ringCatSheaf ⊤ 1) D
  rw [IsZero.iff_id_eq_zero]
  exact (isColimitOfPreserves (Hfunctor X.ringCatSheaf ⊤ 1) hc).hom_ext fun k =>
    (hH (eK.inverse.obj k)).eq_of_src _ _

/-- **Serre's criterion for affineness, finite type form.** Vanishing of the first cohomology on
the finite type quasi-coherent sheaves of ideals suffices for affineness of a quasi-compact,
quasi-separated scheme. -/
@[stacks 01XG, ega "II 5.2.1" "(d')⇒(a), quasi-sep", ega "III 1.4.7" "(ii), special case"]
theorem isAffine_of_forall_isZero_H1_finiteType_ideal (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hH₁ : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        (Subobject.underlying.obj I).IsFiniteType →
          IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).obj
            (Subobject.underlying.obj I))) :
    IsAffine X := by
  refine isAffine_of_forall_isZero_H1_ideal X fun I hI => ?_
  refine (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    X.ringCatSheaf ⊤ 1 _).2 ?_
  refine @isZero_hgroup_one_of_isZero_on_finiteType X _ _ (Subobject.underlying.obj I) hI
    fun G => ?_
  have : Mono (G.obj.arrow ≫ I.arrow) :=
    mono_comp' (Subobject.arrow_mono G.obj) (Subobject.arrow_mono I)
  have heq : Subobject.underlying.obj (Subobject.mk (G.obj.arrow ≫ I.arrow)) ≅
      Subobject.underlying.obj G.obj :=
    Subobject.underlyingIso (G.obj.arrow ≫ I.arrow)
  exact ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    X.ringCatSheaf ⊤ 1 _).1 (hH₁ _
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso heq.symm G.property.1)
      (@Stacks.AlgebraicGeometry.DerivedPushforward.isFiniteType_of_iso.{u, u, u}
        _ _ _ _ _ _ _ _ heq.symm G.property.2))).of_iso
    ((Hfunctor X.ringCatSheaf ⊤ 1).mapIso heq.symm)

end Stacks.SerreCriterion

end
