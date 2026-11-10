module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.RegularLocalBlowupTwists
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineModelTwistBridge
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesPullbackFlat
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationTwistComparison
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistBaseChangeGlued
import all StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted first direct image of a blowup at a regular point of dimension two

Let `X` be a locally Noetherian scheme and `w ∈ X` a closed point whose local ring is regular of
dimension two, let `b : X' ⟶ X` be the blowup of `X` at `w` and let `𝒪_{X'}(n)` be the `n`-th
twisting sheaf of that blowup (`AlgebraicGeometry.blowUpTwist`, the `n`-th twisting sheaf of the
relative `Proj` of the Rees algebra of the centre). Then

`R¹b_*𝒪_{X'}(n) = 0` for every `n ≥ -1`.

At `n = -1` this is `R¹b_*𝒪_{X'}(E) = 0` for `E` the exceptional divisor: the ideal sheaf of `E`
is `𝒪_{X'}(1)` (`AlgebraicGeometry.twistOneIsoExceptionalIdealModule`, part (3) of
[Stacks, Tag 02OS]), so `𝒪_{X'}(E)` is the twist by `-1`.

## Implementation notes

`AlgebraicGeometry.blowUp` is the relative `Proj` of `AlgebraicGeometry.reesSituation`, whose
graded algebra is chosen from `Stacks.Blowup.exists_reesAlgebraData`, while the base-change datum
of [Stacks, Tag 01O3] is available for the explicitly built `Stacks.Blowup.reesSituation`. The two
relative `Proj`s are identified over the base by `Stacks.Blowup.reesSituationBlowUpIso`, and the
comparison morphism of the blowups of a flat base change, `AlgebraicGeometry.reesBaseChangeHom`, is
the base-change morphism of the explicit models conjugated by that identification.

## Main definitions

* `AlgebraicGeometry.reesSituationBaseChangeHom` and
  `AlgebraicGeometry.reesSituationBaseChangeTwistIso`: [Stacks, Tag 01O3] at the explicitly built
  Rees algebras — the base-change morphism of their relative `Proj`s and the transport of the
  twisting sheaf along it.
* `AlgebraicGeometry.reesBaseChangeHom`: the comparison morphism of the two blowups of a flat
  base change, the above conjugated by `Stacks.Blowup.reesSituationBlowUpIso`.
* `AlgebraicGeometry.reesBaseChangeTwistIso`: the transport of `𝒪_{X'}(n)` along it.

## Main results

* `AlgebraicGeometry.isPullback_reesSituationBaseChangeHom` and
  `AlgebraicGeometry.isPullback_reesBaseChangeHom`: the base-change square of the explicit models
  is cartesian, and so is the square of the two blowup morphisms and the flat base change.
* `AlgebraicGeometry.reesBaseChangeHom_comp_blowUpToBase`: the comparison morphism lies over the
  base change.
* `AlgebraicGeometry.isZero_Hgroup_one_blowUpTwist_maximalIdeal`: part (2) of
  [Stacks, Tag 0AGS] read on `AlgebraicGeometry.blowUpTwist` over `Spec B`, for `B` a
  two-dimensional regular local ring.
* `AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_blowUpTwist_pointIdeal`:
  **`R¹b_*𝒪_{X'}(n) = 0` for `n ≥ -1`**, for the blowup of a locally Noetherian scheme at a
  closed point with regular two-dimensional local ring.
* `AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_exceptionalTwist_pointIdeal`: the
  case `n = -1`, `R¹b_*𝒪_{X'}(E) = 0`.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeProj

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The blowups of a flat base change, with their twisting sheaves -/

section FlatBaseChange

variable {Z X : Scheme.{u}} (b : Z ⟶ X) [Flat b] (I : X.IdealSheafData)

/-- **The base-change morphism of the relative `Proj`s of the explicitly built Rees algebras** of
a quasi-coherent sheaf of ideals and of its inverse image along a flat morphism: the morphism
[Stacks, Tag 01O3] attaches to the comparison `Φ` of the two Rees algebras,
`Stacks.Blowup.reesSituationGradedPullbackHom`. -/
def reesSituationBaseChangeHom :
    (Stacks.Blowup.reesSituation (I.comap b)).relativeProj ⟶
      (Stacks.Blowup.reesSituation I).relativeProj :=
  Situation.relativeProjBaseChange b (Stacks.Blowup.reesSituationGradedPullbackHom b I)
    (Stacks.Blowup.isIso_reesSituationGradedPullbackHom_app b I)

/-- The base-change square of the relative `Proj`s of the explicit Rees algebras is
cartesian. -/
theorem isPullback_reesSituationBaseChangeHom :
    IsPullback (reesSituationBaseChangeHom b I)
      (Stacks.Blowup.reesSituation (I.comap b)).relativeProjToBase
      (Stacks.Blowup.reesSituation I).relativeProjToBase b :=
  @Situation.isPullback_relativeProjBaseChange (Stacks.Blowup.reesSituation I)
    (Stacks.Blowup.reesSituation (I.comap b)) b
    (Stacks.Blowup.reesSituationGradedPullbackHom b I)
    (Stacks.Blowup.isIso_reesSituationGradedPullbackHom_app b I)

/-- **The twist assertion of [Stacks, Tag 01O3] at the explicit Rees algebras**: the base-change
morphism carries the `n`-th twisting sheaf onto the `n`-th twisting sheaf. -/
def reesSituationBaseChangeTwistIso (n : ℤ) :
    (Scheme.Modules.pullback (reesSituationBaseChangeHom b I)).obj
        (Situation.twistSheaf (Stacks.Blowup.reesSituation I) n) ≅
      Situation.twistSheaf (Stacks.Blowup.reesSituation (I.comap b)) n :=
  Situation.twistSheafPullbackIso (s := Stacks.Blowup.reesSituation I)
    (s' := Stacks.Blowup.reesSituation (I.comap b)) b
    (Stacks.Blowup.reesSituationGradedPullbackHom b I)
    (Stacks.Blowup.isIso_reesSituationGradedPullbackHom_app b I) n

/-- **The comparison morphism of the blowups of a flat base change**: for a flat `b : Z ⟶ X` and
a quasi-coherent sheaf of ideals `ℐ` on `X`, the morphism `blowUp (ℐ𝒪_Z) ⟶ blowUp ℐ` obtained by
conjugating `AlgebraicGeometry.reesSituationBaseChangeHom` by the identification
`Stacks.Blowup.reesSituationBlowUpIso` of the explicit model with the blowup. -/
def reesBaseChangeHom : blowUp (I.comap b) ⟶ blowUp I :=
  (Stacks.Blowup.reesSituationBlowUpIso (I.comap b)).inv ≫
    reesSituationBaseChangeHom b I ≫ (Stacks.Blowup.reesSituationBlowUpIso I).hom

/-- **The square of the two blowup morphisms and a flat base change is cartesian**, with
`AlgebraicGeometry.reesBaseChangeHom` as its upper edge. -/
@[sga "6 VII 1.8" "Clause (i), special case"]
theorem isPullback_reesBaseChangeHom :
    IsPullback (reesBaseChangeHom b I) (blowUpToBase (I.comap b)) (blowUpToBase I) b := by
  refine (isPullback_reesSituationBaseChangeHom b I).of_iso
    (Stacks.Blowup.reesSituationBlowUpIso (I.comap b))
    (Stacks.Blowup.reesSituationBlowUpIso I) (Iso.refl Z) (Iso.refl X) ?_ ?_ ?_ ?_
  · simp [reesBaseChangeHom]
  · exact (Category.comp_id _).trans
      (Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase (I.comap b)).symm
  · exact (Category.comp_id _).trans
      (Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase I).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The comparison morphism lies over the base change**: the two blowup morphisms and `b` form
a commuting square with it. -/
theorem reesBaseChangeHom_comp_blowUpToBase :
    reesBaseChangeHom b I ≫ blowUpToBase I = blowUpToBase (I.comap b) ≫ b :=
  (isPullback_reesBaseChangeHom b I).w

/-- **The twisting sheaf of a blowup is carried onto the twisting sheaf of the blowup of the
inverse-image centre by a flat base change**, in every degree: the twist assertion of
[Stacks, Tag 01O3] at the explicitly built Rees algebras, conjugated by the identification of
that model with the blowup (`Stacks.Blowup.reesSituationBlowUpTwistIso`). -/
def reesBaseChangeTwistIso (n : ℤ) :
    (Scheme.Modules.pullback (reesBaseChangeHom b I)).obj (blowUpTwist I n) ≅
      blowUpTwist (I.comap b) n :=
  ((Scheme.Modules.pullbackComp (Stacks.Blowup.reesSituationBlowUpIso (I.comap b)).inv
        (reesSituationBaseChangeHom b I ≫
          (Stacks.Blowup.reesSituationBlowUpIso I).hom)).app (blowUpTwist I n)).symm ≪≫
    (Scheme.Modules.pullback (Stacks.Blowup.reesSituationBlowUpIso (I.comap b)).inv).mapIso
      (((Scheme.Modules.pullbackComp (reesSituationBaseChangeHom b I)
              (Stacks.Blowup.reesSituationBlowUpIso I).hom).app (blowUpTwist I n)).symm ≪≫
        (Scheme.Modules.pullback (reesSituationBaseChangeHom b I)).mapIso
          (Stacks.Blowup.reesSituationBlowUpTwistIso I n) ≪≫
        reesSituationBaseChangeTwistIso b I n ≪≫
        (Stacks.Blowup.reesSituationBlowUpTwistIso (I.comap b) n).symm) ≪≫
    ((Scheme.Modules.pullbackEquivOfIso
        (Stacks.Blowup.reesSituationBlowUpIso (I.comap b))).unitIso.app
      (blowUpTwist (I.comap b) n)).symm

end FlatBaseChange

/-! ### The absolute statement, read on the twisting sheaf of the blowup -/

/-- **`H¹(X, 𝒪_X(n)) = 0` for `n ≥ -1`, for the blowup of a two-dimensional regular local ring
`B` in its maximal ideal**, read on `AlgebraicGeometry.blowUpTwist` of the blowup of `Spec B` in
the sheaf of ideals that the maximal ideal defines. -/
theorem isZero_Hgroup_one_blowUpTwist_maximalIdeal (B : Type u) [CommRing B]
    [IsRegularLocalRing B] (hdim : ringKrullDim B = 2) {n : ℤ} (hn : -1 ≤ n) :
    IsZero (Hgroup (blowUp (Stacks.Blowup.AffineModel.specIdealSheaf
        (IsLocalRing.maximalIdeal B))).ringCatSheaf ⊤ 1
      (blowUpTwist (Stacks.Blowup.AffineModel.specIdealSheaf
        (IsLocalRing.maximalIdeal B)) n)) := by
  obtain ⟨d, -, htw⟩ :=
    Stacks.Blowup.AffineModel.exists_iso_blowUpTwist (IsLocalRing.maximalIdeal B)
  obtain ⟨e⟩ := htw n
  have h := Stacks.Blowup.isZero_hgroup_one_twistingSheaf_maximalIdeal B hdim hn
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff d _ 1).mp (h.of_iso ?_)
  exact (Hfunctor (Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal B)).ringCatSheaf ⊤ 1).mapIso e

/-! ### The relativization -/

/-- **`R¹b_*𝒪_{X'}(n) = 0` for `n ≥ -1`, for the blowup `b` of a locally Noetherian scheme at a
closed point whose local ring is regular of dimension two.** -/
@[sga "6 VII 3.5" "Clause (i), special case", sga "7 X 2.11" "partial"]
theorem isZero_rightDerivedPlus_one_pushforward_blowUpTwist_pointIdeal {X : Scheme.{u}}
    [IsLocallyNoetherian X] (w : X) (hw : IsClosed ({w} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk w)] (hdim : ringKrullDim (X.presheaf.stalk w) = 2)
    {n : ℤ} (hn : -1 ≤ n) :
    IsZero (((Scheme.Modules.pushforward
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus 1).obj
      (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) n)) := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X) with hM
  set g := blowUpToBase M
  have hF : (((Scheme.Modules.pushforward g).rightDerivedPlus 1).obj
      (blowUpTwist M n)).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus g _ inferInstance 1
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ (fun y => ?_)
  by_cases hy : y = w
  · subst hy
    let b := X.fromSpecStalk y
    have : Flat b := flat_fromSpecStalk X y
    set p := blowUpToBase (M.comap b)
    have hsq : IsPullback (reesBaseChangeHom b M) p g b := isPullback_reesBaseChangeHom b M
    have hloc : IsZero (Hgroup (blowUp (M.comap b)).ringCatSheaf ⊤ 1
        (blowUpTwist (M.comap b) n)) := by
      rw [hM, vanishingIdeal_singleton_comap_fromSpecStalk_eq y hw]
      exact isZero_Hgroup_one_blowUpTwist_maximalIdeal _ hdim hn
    have hp : IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus 1).obj
        (blowUpTwist (M.comap b) n)) :=
      open Stacks.AlgebraicGeometry.TopDegreeBaseChange Stacks.Cohomology.AffineBase in
      isZero_rightDerivedPlus_pushforward_of_isZero_cohomology p 1 _
        ((isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup _ _ 1).2 hloc)
    have hpull : IsZero ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward g).rightDerivedPlus 1).obj (blowUpTwist M n))) := by
      have h₁ : IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus 1).obj
          ((Scheme.Modules.pullback (reesBaseChangeHom b M)).obj (blowUpTwist M n))) :=
        hp.of_iso (((Scheme.Modules.pushforward p).rightDerivedPlus 1).mapIso
          (reesBaseChangeTwistIso b M n))
      exact h₁.of_iso (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hsq
        (blowUpTwist M n) 1)
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    obtain ⟨e, -⟩ := exists_fromSpecStalkSectionsStalkLinearEquiv
      (((Scheme.Modules.pushforward g).rightDerivedPlus 1).obj (blowUpTwist M n)) y hU hyU
    have hsub : Subsingleton (Γ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward g).rightDerivedPlus 1).obj (blowUpTwist M n)), ⊤)) := by
      exact ModuleCat.isZero_iff_subsingleton.mp
        ((SheafOfModules.evaluation _ (op ⊤)).map_isZero hpull)
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact e.symm.toEquiv.subsingleton
  · let V : X.Opens := ⟨M.supportᶜ, M.support.isClosed.isOpen_compl⟩
    have hyV : y ∈ V := by
      change y ∉ (M.support : Set X)
      rw [hM, Stacks.GenericFlatness.support_vanishingIdeal]
      exact hy
    have hiso : IsIso (g ∣_ V) := isIso_blowUp_restrict_compl_support M
    have : IsAffineHom (g ∣_ V) := inferInstance
    have : ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ V).ι).obj
        (blowUpTwist M n)).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ _
    open Stacks.AlgebraicGeometry.SchemeHigherDirectImage in
    exact isZero_stalk_of_isZero_rightDerivedPlus_restrict g V y hyV _ (by norm_num)
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom (g ∣_ V) _ 1
        one_pos)

/-- **`R¹b_*𝒪_{X'}(E) = 0`** for the blowup `b : X' ⟶ X` of a locally Noetherian scheme at a
closed point `w` whose local ring is regular of dimension two, with `E` the exceptional divisor
(`𝒪_{X'}(E)` is the twist by `-1`). -/
theorem isZero_rightDerivedPlus_one_pushforward_exceptionalTwist_pointIdeal {X : Scheme.{u}}
    [IsLocallyNoetherian X] (w : X) (hw : IsClosed ({w} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk w)] (hdim : ringKrullDim (X.presheaf.stalk w) = 2) :
    IsZero (((Scheme.Modules.pushforward
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus 1).obj
      (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) (-1))) :=
  isZero_rightDerivedPlus_one_pushforward_blowUpTwist_pointIdeal w hw hdim le_rfl

end AlgebraicGeometry

end
