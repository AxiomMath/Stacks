module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReductionNumberOneFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images along the blowup of a closed point

Let `X` be a locally Noetherian scheme, `w ∈ X` a closed point and `g : X' ⟶ X` the blowup of `X`
at `w`. Away from `w` the morphism `g` is an isomorphism, and at `w` flat base change along
`Spec 𝒪_{X, w} ⟶ X` ([Stacks, Tag 02KH]) identifies the stalk of `R^q g_*𝒪_{X'}` with
`H^q` of the blowup of the local ring `𝒪_{X, w}` in its maximal ideal. So
`R^q g_*𝒪_{X'} = 0` as soon as that cohomology group vanishes.

The local cohomology vanishes in every positive degree when the maximal ideal `𝔪` of
`𝒪_{X, w}` has a reduction `(a, b)` of reduction number one, `𝔪² = (a, b) 𝔪`
(`Stacks.Blowup.isZero_Hgroup_one_proj_reesGrading_of_sq_eq`); this covers the regular points of
dimension two and the singular points of a family of nodal curves over a discrete valuation ring.

## Main results

* `AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUp_pointIdeal_of_isZero_Hgroup`:
  `R^q g_*𝒪_{X'} = 0` if `H^q` of the blowup of `𝒪_{X, w}` in its maximal ideal vanishes.
* `AlgebraicGeometry.isZero_Hgroup_blowUp_maximalIdeal_of_sq_eq`: `H^q` of the blowup of a ring
  in an ideal `I` with `I² = (a, b) I` vanishes for `q > 0`.
* `AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUp_pointIdeal_of_sq_eq`:
  `R^q g_*𝒪_{X'} = 0` for `q > 0` when the maximal ideal of `𝒪_{X, w}` satisfies
  `𝔪² = (a, b) 𝔪`.

## Implementation notes

Higher direct images are the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`, in the
standard model of the derived category, the model in which flat base change
(`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso`) and the quasi-coherence of
higher direct images are stated.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The structure sheaf of a scheme is quasi-coherent. -/
private instance isQuasicoherent_unit_ringCatSheaf (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _

open Stacks.AlgebraicGeometry.TopDegreeBaseChange Stacks.Cohomology.AffineBase
  Stacks.AlgebraicGeometry.SchemeHigherDirectImage in
/-- **`R^q g_*𝒪_{X'} = 0` for the blowup `g` of a locally Noetherian scheme at a closed point `w`,
when `H^q` of the blowup of `𝒪_{X, w}` in its maximal ideal vanishes** (`q > 0`). Away from `w`
the morphism `g` is an isomorphism; at `w` flat base change along `Spec 𝒪_{X, w} ⟶ X`
([Stacks, Tag 02KH]) identifies the question with the local one. -/
theorem isZero_rightDerivedPlus_pushforward_blowUp_pointIdeal_of_isZero_Hgroup {X : Scheme.{u}}
    [IsLocallyNoetherian X] (w : X) (hw : IsClosed ({w} : Set X)) (q : ℕ) (hq : 0 < q)
    (hloc : IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (X.presheaf.stalk w))).inv.hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk w))))).ringCatSheaf ⊤ q
      (SheafOfModules.unit (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (X.presheaf.stalk w))).inv.hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk w))))).ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus
          q).obj (SheafOfModules.unit (blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds X))).ringCatSheaf)) := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X) with hM
  set g := blowUpToBase M
  have hF : (((Scheme.Modules.pushforward g).rightDerivedPlus q).obj
      (SheafOfModules.unit (blowUp M).ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus g _ inferInstance q
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ (fun y => ?_)
  by_cases hy : y = w
  · subst hy
    let b := X.fromSpecStalk y
    have : Flat b := flat_fromSpecStalk X y
    obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap b M
    set p := blowUpToBase (M.comap b)
    have hloc' : IsZero (Hgroup (blowUp (M.comap b)).ringCatSheaf ⊤ q
        (SheafOfModules.unit (blowUp (M.comap b)).ringCatSheaf)) := by
      rw [hM, Stacks.Blowup.vanishingIdeal_comap_fromSpecStalk_eq_specIdealSheaf y hw]
      exact hloc
    have hp : IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus q).obj
        (SheafOfModules.unit (blowUp (M.comap b)).ringCatSheaf)) :=
      isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
        p q _ ((isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
          _ _ q).2 hloc')
    have hpull : IsZero ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward g).rightDerivedPlus q).obj
          (SheafOfModules.unit (blowUp M).ringCatSheaf))) := by
      have h₁ : IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus q).obj
          ((Scheme.Modules.pullback h).obj (SheafOfModules.unit (blowUp M).ringCatSheaf))) :=
        hp.of_iso (((Scheme.Modules.pushforward p).rightDerivedPlus q).mapIso
          (Scheme.Modules.pullbackUnitIso h))
      exact h₁.of_iso (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hpb.flip
        (SheafOfModules.unit (blowUp M).ringCatSheaf) q)
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    obtain ⟨e, -⟩ := exists_fromSpecStalkSectionsStalkLinearEquiv
      (((Scheme.Modules.pushforward g).rightDerivedPlus q).obj
        (SheafOfModules.unit (blowUp M).ringCatSheaf)) y hU hyU
    have hsub : Subsingleton (Γ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward g).rightDerivedPlus q).obj
          (SheafOfModules.unit (blowUp M).ringCatSheaf)), ⊤)) := by
      have := (SheafOfModules.evaluation _ (op ⊤)).map_isZero hpull
      exact (ModuleCat.isZero_iff_subsingleton.mp this)
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
        (SheafOfModules.unit (blowUp M).ringCatSheaf)).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ _
    exact isZero_stalk_of_isZero_rightDerivedPlus_restrict
      g V y hyV _ (by positivity)
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom (g ∣_ V) _ q
        (by exact_mod_cast hq))

/-- **`H^q` of the blowup of `Spec A` in an ideal `I` with `I² = (a, b) I` vanishes for `q > 0`**,
in the ideal-sheaf spelling of the blowup: the blowup is `Proj` of the Rees algebra
(`Stacks.Blowup.nonempty_over_iso_blowUpToBase`), whose cohomology is computed on the two charts
`D₊(a⁽¹⁾)`, `D₊(b⁽¹⁾)`. -/
@[sga "6 VII 3.5" "Clause (i)"]
theorem isZero_Hgroup_blowUp_maximalIdeal_of_sq_eq (A : Type u) [CommRing A] (I : Ideal A)
    {a b : A} (ha : a ∈ I) (hb : b ∈ I) (hI : I ^ 2 = Ideal.span {a, b} * I) (q : ℕ)
    (hq : 0 < q) :
    IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I))).ringCatSheaf ⊤ q
      (SheafOfModules.unit (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I))).ringCatSheaf)) := by
  obtain ⟨e⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase (R := A) (K := I)
  have hei : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let e' : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I) ≅
      blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)) :=
    @asIso _ _ _ _ e.hom.left hei
  have h : IsZero (Hgroup (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)).ringCatSheaf ⊤ q
      (SheafOfModules.unit
        (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)).ringCatSheaf)) := by
    rcases Nat.lt_or_ge q 2 with h | h
    · obtain rfl : q = 1 := by omega
      exact Stacks.Blowup.isZero_Hgroup_one_proj_reesGrading_of_sq_eq I ha hb hI
    · exact Stacks.Blowup.isZero_Hgroup_proj_reesGrading_of_sq_eq_of_two_le I ha hb hI _ q h
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e' _ q).mp (h.of_iso ?_)
  exact (Hfunctor (AlgebraicGeometry.Proj
    (Stacks.Blowup.reesGrading I)).ringCatSheaf ⊤ q).mapIso
      (Scheme.Modules.pullbackUnitIso e'.hom)

/-- **`R^q g_*𝒪_{X'} = 0` for `q > 0` for the blowup `g` of a locally Noetherian scheme at a
closed point `w` whose maximal ideal has a reduction of reduction number one**, i.e.
`𝔪² = (a, b) 𝔪` in `𝒪_{X, w}`. -/
@[sga "6 VII 3.5" "Clause (i)"]
theorem isZero_rightDerivedPlus_pushforward_blowUp_pointIdeal_of_sq_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] (w : X) (hw : IsClosed ({w} : Set X))
    {a b : X.presheaf.stalk w} (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w))
    (hb : b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w))
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk w) ^ 2 =
      Ideal.span {a, b} * IsLocalRing.maximalIdeal (X.presheaf.stalk w)) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus
          q).obj (SheafOfModules.unit (blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds X))).ringCatSheaf)) :=
  isZero_rightDerivedPlus_pushforward_blowUp_pointIdeal_of_isZero_Hgroup w hw q hq
    (isZero_Hgroup_blowUp_maximalIdeal_of_sq_eq _ _ ha hb hm q hq)

end AlgebraicGeometry

end
