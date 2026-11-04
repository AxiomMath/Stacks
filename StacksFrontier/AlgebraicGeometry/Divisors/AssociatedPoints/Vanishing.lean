module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of a quasi-coherent module and its associated points

A quasi-coherent sheaf of modules on a scheme is zero exactly when it has no weakly associated
points, and — on a locally Noetherian scheme — exactly when it has no associated points.

## Main results

* `AlgebraicGeometry.isZero_iff_weaklyAssociatedPoints_eq_empty`: vanishing is the absence of
  weakly associated points.
* `AlgebraicGeometry.isZero_iff_associatedPoints_eq_empty`: on a locally Noetherian scheme,
  vanishing is the absence of associated points.

## References

* [Stacks Project, Tag 05AG](https://stacks.math.columbia.edu/tag/05AG)
* [Stacks Project, Tag 05AP](https://stacks.math.columbia.edu/tag/05AP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The sections of a zero sheaf of modules over any open form a subsingleton. -/
private lemma sections_subsingleton_of_isZero {X : Scheme.{u}} (F : X.Modules) (hF : IsZero F)
    (U : X.Opens) : Subsingleton Γ(F, U) :=
  AddCommGrpCat.subsingleton_of_isZero
    (Functor.map_isZero ((evaluation _ _).obj (Opposite.op U))
      (Functor.map_isZero (PresheafOfModules.toPresheaf.{u} _)
        (Functor.map_isZero (SheafOfModules.forget X.ringCatSheaf) hF)))

/-- A quasi-coherent sheaf of modules is zero if and only if it has no weakly associated points. -/
@[stacks 05AP]
theorem isZero_iff_weaklyAssociatedPoints_eq_empty {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] : IsZero F ↔ Stacks.Divisors.weaklyAssociatedPoints F = ∅ := by
  refine ⟨fun hF ↦ Set.eq_empty_of_forall_notMem fun x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hempty : weaklyAssociatedPrimes Γ(X, U) Γ(F, U) = ∅ :=
      weakAss_empty_iff_zero.mp fun s => (sections_subsingleton_of_isZero F hF U).elim s 0
    have hp : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ weaklyAssociatedPrimes Γ(X, U) Γ(F, U) :=
      (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F U hU x hxU).mpr hx
    simp [hempty] at hp
  · have hstalk : ∀ x : X, IsZero (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) := by
      intro x
      have hzero : ∀ z : F.presheaf.stalk x, z = 0 := by
        intro z
        obtain ⟨V, hxV, hV, a, ha⟩ :=
          TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens F.presheaf x z
        have hpempty : weaklyAssociatedPrimes Γ(X, V) Γ(F, V) = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun p hp ↦ ?_
          let y : V := hV.isoSpec.inv ⟨p, hp.isPrime⟩
          have hpy : (hV.primeIdealOf y).asIdeal = p := by
            have hi : hV.isoSpec.hom (hV.isoSpec.inv ⟨p, hp.isPrime⟩) =
                (⟨p, hp.isPrime⟩ : PrimeSpectrum Γ(X, V)) := by
              show (hV.isoSpec.inv ≫ hV.isoSpec.hom) ⟨p, hp.isPrime⟩ = _
              rw [hV.isoSpec.inv_hom_id]
              rfl
            simpa [IsAffineOpen.primeIdealOf, y] using congrArg (fun q => q.asIdeal) hi
          have hy : y.1 ∈ Stacks.Divisors.weaklyAssociatedPoints F :=
            (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F V hV y y.property).mp
              (hpy ▸ hp)
          simp [h] at hy
        have hz : a = 0 := (weakAss_empty_iff_zero.mpr hpempty) a
        rw [← ha, hz]
        simp
      have hsub : Subsingleton (F.presheaf.stalk x) :=
        ⟨fun s t ↦ (hzero s).trans (hzero t).symm⟩
      exact AddCommGrpCat.isZero_of_subsingleton _
    have hsheaf : IsZero (⟨F.presheaf, Scheme.Modules.isSheaf F⟩ : TopCat.Sheaf Ab X) :=
      (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr hstalk
    have hp : IsZero F.presheaf := Functor.map_isZero (TopCat.Sheaf.forget Ab X) hsheaf
    let f := (isZero_zero _).from_ F
    have hiso : IsIso ((Scheme.Modules.toPresheaf X).map f) := isIso_of_source_target_iso_zero _
      hp.isoZero (Functor.map_isZero (Scheme.Modules.toPresheaf X) (isZero_zero _)).isoZero
    have : IsIso f := isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)
    exact (isZero_zero _).of_iso (asIso f)

/-- A quasi-coherent module on a locally Noetherian scheme is zero if and only if its set of
associated points is empty. -/
@[stacks 05AG]
theorem isZero_iff_associatedPoints_eq_empty (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsZero F ↔ Stacks.Divisors.associatedPoints F = ∅ := by
  simpa only [associatedPoints_eq_weaklyAssociatedPoints] using
    isZero_iff_weaklyAssociatedPoints_eq_empty F

end AlgebraicGeometry
