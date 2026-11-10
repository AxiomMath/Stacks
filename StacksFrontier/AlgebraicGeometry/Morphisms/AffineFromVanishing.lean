module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism with vanishing first higher direct image on ideals is affine

Let `f : X ⟶ Y` be a quasi-compact morphism of quasi-separated schemes. If `R¹f_*𝓘 = 0` for
every quasi-coherent sheaf of ideals `𝓘` on `X`, then `f` is affine.

Affineness is local on the target, so it suffices to show that the preimage of an affine open
`V ⊆ Y` is affine, and that is Serre's criterion
(`Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`) applied to `U = f⁻¹(V)`. Its
hypothesis is supplied in three steps: a quasi-coherent ideal sheaf on `U` extends to one on `X`
(Stacks 01PE), the vanishing of `R¹f_*` of the extension localizes to `R¹(f|_U)_*` of the ideal
(Stacks 01E5), and the low-degree Leray sequence for `f|_U` sandwiches `H¹(U, 𝓘)` between
`H¹(V, (f|_U)_*𝓘)` — zero because `V` is affine and the direct image is quasi-coherent — and
`Γ(V, R¹(f|_U)_*𝓘)`, zero by the previous step.

## Main results

* `Stacks.AffineFromVanishing.isZero_rightDerived_evaluation_of_isZero_pushforward`: the
  low-degree Leray sandwich over an affine base.
* `Stacks.AffineFromVanishing.isAffineOpen_preimage_of_isZero_rightDerived_ideal`: the preimage
  of an affine open is affine.
* `Stacks.AffineFromVanishing.isAffineHom_of_forall_isZero_rightDerived_ideal`: the criterion.

## Implementation notes

A quasi-coherent sheaf of ideals on `X` is a subobject of `SheafOfModules.unit X.ringCatSheaf`
with quasi-coherent underlying module, and `R¹f_*` is the first right derived functor of
`Scheme.Modules.pushforward f`; vanishing is `CategoryTheory.Limits.IsZero`.

The localization isomorphism of Stacks 01E5 is stated for ringed spaces; its scheme-level form
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso` is what is used
here.

## References

* [Stacks Project, Tag 0F83](https://stacks.math.columbia.edu/tag/0F83)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AffineFromVanishing

/-- `H¹(U, M)` vanishes iff the cohomology of the underlying abelian sheaf does. -/
private theorem isZero_hgroup_iff_isZero_abelianCohomology (X : Scheme.{u}) (M : X.Modules) :
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 M) ↔
      IsZero ((Stacks.Cohomology.LerayLowDegree.abelianCohomology.{u, u} X.toTopCat ⊤ 1).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) :=
  let e :=
    (((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf ⊤ 1).app M).symm ≪≫
      (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso X.ringCatSheaf ⊤ 1).app M)
  ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

/-- **The low-degree Leray sandwich over an affine base.** If `g : U ⟶ V` has affine target, the
direct image of `M` is quasi-coherent and `R¹g_*M = 0`, then `H¹(U, M) = 0`: the low-degree Leray
sequence puts `H¹(U, M)` between `H¹(V, g_*M)`, which vanishes because `V` is affine and `g_*M`
is quasi-coherent, and `Γ(V, R¹g_*M)`, which vanishes by hypothesis. -/
theorem isZero_rightDerived_evaluation_of_isZero_pushforward
    {U V : Scheme.{u}} (g : U ⟶ V) [IsAffine V] (M : U.Modules)
    (hQ : ((Scheme.Modules.pushforward g).obj M).IsQuasicoherent)
    (hR : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj M)) :
    IsZero (((SheafOfModules.evaluation U.ringCatSheaf (op ⊤)).rightDerived 1).obj M) := by
  let gR := g.toLRSHom.toShHom
  let FAb := (SheafOfModules.toSheaf U.ringCatSheaf).obj M
  have hH₁Ab : IsZero (Hgroup V.ringCatSheaf ⊤ 1 ((Scheme.Modules.pushforward g).obj M)) :=
    @Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen V _ hQ ⊤
      (isAffineOpen_top V) 1 one_pos
  have hSource : IsZero ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} gR.hom.base ⋙
      Stacks.Cohomology.LerayLowDegree.abelianCohomology.{u, u} V.toTopCat ⊤ 1).obj FAb) :=
    (isZero_hgroup_iff_isZero_abelianCohomology V ((Scheme.Modules.pushforward g).obj M)).1 hH₁Ab
  have hTarget : IsZero ((Stacks.Cohomology.LerayLowDegree.abelianSections.{u, u}
      V.toTopCat ⊤).obj
        (((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
          gR.hom.base).rightDerived 1).obj FAb)) :=
    Functor.map_isZero (Stacks.Cohomology.LerayLowDegree.abelianSections.{u, u} V.toTopCat ⊤)
      ((Functor.map_isZero (SheafOfModules.toSheaf V.ringCatSheaf) hR).of_iso
        ((Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso
          gR 1).app M).symm)
  have hAbH₁ : IsZero ((Stacks.Cohomology.LerayLowDegree.abelianCohomology.{u, u}
      U.toTopCat ⊤ 1).obj FAb) :=
    ((Stacks.Cohomology.LerayLowDegree.abelianLerayLowDegreeData.{u, u} gR.hom.base).exact
      FAb).isZero_of_both_zeros (hSource.eq_zero_of_src _) (hTarget.eq_zero_of_tgt _)
  exact (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    U.ringCatSheaf ⊤ 1 _).2 ((isZero_hgroup_iff_isZero_abelianCohomology U M).2 hAbH₁)

/-- **The preimage of an affine open is affine.** For a quasi-compact morphism of quasi-separated
schemes whose first higher direct image vanishes on quasi-coherent ideal sheaves, the preimage of
an affine open of the target is affine. -/
theorem isAffineOpen_preimage_of_isZero_rightDerived_ideal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (hR₁ : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (V : Y.Opens) (hV : IsAffineOpen V) : IsAffineOpen (f ⁻¹ᵁ V) := by
  have hqsU : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    (f ⁻¹ᵁ V).isOpenEmbedding'.quasiSeparatedSpace
  have hcs : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    isCompact_iff_compactSpace.mp ((quasiCompact_iff_forall_isAffineOpen.mp inferInstance) V hV)
  have hVaff : IsAffine V.toScheme := hV
  change IsAffine (f ⁻¹ᵁ V).toScheme
  refine Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal (f ⁻¹ᵁ V).toScheme
    fun I hI => ?_
  have hfac : (I.arrow ≫ (Scheme.Modules.restrictUnitIso ((f ⁻¹ᵁ V).ι)).inv) ≫
      (Scheme.Modules.restrictUnitIso ((f ⁻¹ᵁ V).ι)).hom = I.arrow :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => I.arrow ≫ k)
        (Scheme.Modules.restrictUnitIso ((f ⁻¹ᵁ V).ι)).inv_hom_id).trans (Category.comp_id _))
  have hcomp : Mono (I.arrow ≫ (Scheme.Modules.restrictUnitIso ((f ⁻¹ᵁ V).ι)).inv) :=
    mono_of_mono_fac hfac
  let G : Subobject (Scheme.Modules.restrict
      (SheafOfModules.unit X.ringCatSheaf) ((f ⁻¹ᵁ V).ι)) :=
    @Subobject.mk _ _ _ _ (I.arrow ≫ (Scheme.Modules.restrictUnitIso ((f ⁻¹ᵁ V).ι)).inv) hcomp
  have eGI : Subobject.underlying.obj G ≅ Subobject.underlying.obj I :=
    @Subobject.underlyingIso _ _ _ _
      (I.arrow ≫ (Scheme.Modules.restrictUnitIso ((f ⁻¹ᵁ V).ι)).inv) hcomp
  have hG : (Subobject.underlying.obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (f ⁻¹ᵁ V).toScheme.ringCatSheaf).prop_of_iso eGI.symm hI
  have hJqc : QuasiCompact ((f ⁻¹ᵁ V).ι) :=
    quasiCompact_isStableUnderBaseChange.of_isPullback (isPullback_morphismRestrict f V)
      inferInstance
  obtain ⟨H, hH, eH, -⟩ := AlgebraicGeometry.exists_quasicoherentSubobject_restrict
    ((f ⁻¹ᵁ V).ι) (SheafOfModules.unit X.ringCatSheaf) G hG
  have hLocalI : IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived 1).obj
      (Subobject.underlying.obj I)) :=
    ((Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι) (hR₁ H hH)).of_iso
      ((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso
        f V 1).app (Subobject.underlying.obj H))).of_iso
      (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived 1).mapIso (eH ≪≫ eGI).symm)
  exact isZero_rightDerived_evaluation_of_isZero_pushforward (f ∣_ V) (Subobject.underlying.obj I)
    (@AlgebraicGeometry.pushforward_isQuasicoherent _ _ (f ∣_ V) inferInstance
      ((quasiSeparated_iff_quasiSeparatedSpace (f ∣_ V)).2 hqsU) (Subobject.underlying.obj I) hI)
    hLocalI

/-- **Stacks Project, Tag 0F83.** A quasi-compact morphism between quasi-separated schemes is
affine as soon as the first higher direct image of every quasi-coherent sheaf of ideals on the
source vanishes. -/
@[stacks 0F83, ega "II 5.2.2" "c ⇒ a, c' ⇒ a"]
theorem isAffineHom_of_forall_isZero_rightDerived_ideal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (hR₁ : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
          (Subobject.underlying.obj I))) :
    IsAffineHom f := by
  refine isAffineHom_of_forall_exists_isAffineOpen f fun y => ?_
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  exact ⟨V, hyV, hV, isAffineOpen_preimage_of_isZero_rightDerived_ideal f hR₁ V hV⟩

end Stacks.AffineFromVanishing

end
