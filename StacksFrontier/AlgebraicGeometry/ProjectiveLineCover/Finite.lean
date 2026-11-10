module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.Generic
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.ChartAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.Glue

/-!
# The multiplication of binary forms is a finite morphism

The morphism `ℙ¹ × ℙⁿ ⟶ ℙⁿ⁺¹` of `Stacks.ProjectiveLineCover.multiplication` is proper, its
source being proper over the integers and its target separated, and it is locally quasi-finite:
on each piece of `ℙ¹ × ℙⁿ` it is `Proj` of a graded substitution whose maps of degree-zero
localizations are quasi-finite by
`StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.ChartAlgebra`.
A proper locally quasi-finite morphism is finite (Mathlib's
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`).

## Main results

* `Stacks.ProjectiveLineCover.locallyQuasiFinite_projMap_of_awayMap`: `Proj` of a graded ring
  homomorphism of polynomial rings is locally quasi-finite as soon as its maps of degree-zero
  localizations at the variables are quasi-finite.
* `Stacks.ProjectiveLineCover.isFinite_multiplication`: the multiplication morphism is finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveLineCover

/-- Locally quasi-finite morphisms of schemes respect isomorphisms. -/
instance : MorphismProperty.RespectsIso @LocallyQuasiFinite.{u} :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance

/-- Being locally quasi-finite is local on the target. -/
instance : IsZariskiLocalAtTarget @LocallyQuasiFinite :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyQuasiFinite)
    (Q := RingHom.QuasiFinite)

variable (n : ℕ)

/-- **`Proj` of a graded homomorphism out of a polynomial ring is locally quasi-finite** when the
maps of degree-zero localizations at the variables are quasi-finite. -/
theorem locallyQuasiFinite_projMap_of_awayMap {B : Type u} [CommRing B] (m : ℕ)
    (ψ : Stacks.ProjectiveCohomology.polyGrading (ULift.{u} ℤ) m →+*ᵍ
      Stacks.ProjectiveCohomology.polyGrading B n)
    (hψ : HomogeneousIdeal.irrelevant (Stacks.ProjectiveCohomology.polyGrading B n) ≤
      HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant _))
    (h : ∀ k : Fin (m + 1), (Away.map ψ (X k)).QuasiFinite) :
    LocallyQuasiFinite (Proj.map ψ hψ) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ (iSup_basicOpen_X_eq_top (ULift.{u} ℤ) m)
    fun k => ?_
  have hsq := Stacks.AlgebraicGeometry.ProjBaseChange.isPullback_awayι_projMap
    (Stacks.ProjectiveCohomology.polyGrading (ULift.{u} ℤ) m)
    (Stacks.ProjectiveCohomology.polyGrading B n) ψ hψ Nat.one_pos
    (X_mem_one (ULift.{u} ℤ) m k) (ψ.2 (X_mem_one (ULift.{u} ℤ) m k)) rfl (Away.map ψ (X k))
    (fun k a ha ha' => Away.map_mk _ _ _ _ _ _)
  have hSpec : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (Away.map ψ (X k)))) :=
    HasRingHomProperty.Spec_iff.mpr (h k)
  have h1 : LocallyQuasiFinite (hsq.isoPullback.inv ≫
      Spec.map (CommRingCat.ofHom (Away.map ψ (X k)))) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyQuasiFinite) _ _).mpr hSpec
  rw [hsq.isoPullback_inv_snd] at h1
  have h2 := (MorphismProperty.arrow_mk_iso_iff (P := @LocallyQuasiFinite)
    (morphismRestrictOpensRange (Proj.map ψ hψ) (Proj.awayι
      (Stacks.ProjectiveCohomology.polyGrading (ULift.{u} ℤ) m) (X k)
      (X_mem_one (ULift.{u} ℤ) m k) Nat.one_pos))).mpr h1
  rw [Proj.opensRange_awayι] at h2
  exact h2

/-- The coordinate ring of a standard chart of `ℙ¹_ℤ` is generated, as a ring, by its affine
coordinate. -/
theorem mem_closure_chartRing (i : Fin 2) (c : chartRing.{u} i)
    (hc : chartCoord (ULift.{u} ℤ) 1 i ⟨1 - i, by fin_cases i <;> decide⟩ = c)
    (b : chartRing.{u} i) : b ∈ Subring.closure {c} := by
  obtain ⟨p, rfl⟩ := chartHom_surjective (ULift.{u} ℤ) 1 i b
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [chartHom_C, show r = ((r.down : ℤ) : ULift.{u} ℤ) by ext; simp, map_intCast]
    exact intCast_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, chartHom_X]
    refine mul_mem hp (Subring.subset_closure ?_)
    rw [Set.mem_singleton_iff, ← hc]
    congr
    obtain ⟨j, hj⟩ := j
    fin_cases i <;> fin_cases j <;>
      simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue, ne_eq, sub_zero,
        sub_self, Subtype.mk.injEq, zero_ne_one, one_ne_zero] <;>
      exact absurd rfl hj

/-- Multiplication by `T + t`, on the chart of `ℙ¹` with affine coordinate `t`, is locally
quasi-finite. -/
theorem locallyQuasiFinite_mulMapX : LocallyQuasiFinite (mulMapX.{u} n coordT) :=
  locallyQuasiFinite_projMap_of_awayMap n (n + 1) _ _ fun k =>
    quasiFinite_awayMap_mulHom_one_left n coordT (mem_closure_chartRing 0 coordT rfl) k

/-- Multiplication by `σ T + 1`, on the chart of `ℙ¹` with affine coordinate `σ`, is locally
quasi-finite. -/
theorem locallyQuasiFinite_mulMapY : LocallyQuasiFinite (mulMapY.{u} n coordS) :=
  locallyQuasiFinite_projMap_of_awayMap n (n + 1) _ _ fun k =>
    quasiFinite_awayMap_mulHom_one_right n coordS (mem_closure_chartRing 1 coordS rfl) k

/-- Being locally quasi-finite is local on the source. -/
instance : IsZariskiLocalAtSource @LocallyQuasiFinite :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyQuasiFinite)
    (Q := RingHom.QuasiFinite)

/-- **The multiplication of binary forms is locally quasi-finite.** -/
theorem locallyQuasiFinite_multiplication : LocallyQuasiFinite (multiplication.{u} n) := by
  refine IsZariskiLocalAtSource.of_openCover (productCover.{u} n) fun i => ?_
  have := locallyQuasiFinite_mulMapX.{u} n
  have := locallyQuasiFinite_mulMapY.{u} n
  have key : ∀ i : Fin 2, LocallyQuasiFinite (pieceι.{u} n i ≫ multiplication.{u} n) := by
    intro i
    rw [pieceι_multiplication]
    fin_cases i
    · change LocallyQuasiFinite (_ ≫ _ ≫ mulMapX.{u} n coordT); infer_instance
    · change LocallyQuasiFinite (_ ≫ _ ≫ mulMapY.{u} n coordS); infer_instance
  exact key i

/-- `ℙ¹ × ℙⁿ` is proper over `Spec ℤ`. -/
instance : IsProper (terminal.from (Prod.{u} n)) := by
  have h1 : IsProper (pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} 1))) :=
    ProjectiveSpace.instIsProperOver 1 (projectiveSpaceAtUniverse.{u} n)
  have h2 : IsProper (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
    ProjectiveSpace.isProper_terminal_from n
  rw [show terminal.from (Prod.{u} n) = pullback.fst _ _ ≫
    terminal.from (projectiveSpaceAtUniverse.{u} n) from terminal.hom_ext _ _]
  infer_instance

/-- **The multiplication of binary forms is proper.** -/
instance isProper_multiplication : IsProper (multiplication.{u} n) := by
  have h2 : IsProper (terminal.from (projectiveSpaceAtUniverse.{u} (n + 1))) :=
    ProjectiveSpace.isProper_terminal_from (n + 1)
  have : IsProper (multiplication.{u} n ≫ terminal.from _) := by
    rw [show multiplication.{u} n ≫ terminal.from _ = terminal.from (Prod.{u} n) from
      terminal.hom_ext _ _]
    infer_instance
  exact IsProper.of_comp _ (terminal.from _)

/-- **The multiplication of binary forms is finite.** -/
instance isFinite_multiplication : IsFinite (multiplication.{u} n) := by
  have := locallyQuasiFinite_multiplication.{u} n
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Stacks.ProjectiveLineCover
