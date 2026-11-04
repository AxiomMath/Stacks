module

public import StacksFrontier.RingTheory.Flat.CompleteDevissagePoints
public import StacksFrontier.RingTheory.Flat.DevissageDecomposition
public import StacksFrontier.RingTheory.Flat.DevissageLocalize
public import StacksFrontier.RingTheory.Flat.FlatteningStageStep

/-!
# The local flattening theorem along a complete dévissage

Let `A` be a local ring, `C` a finite type `A`-algebra, `N` a finite `C`-module and `q` a prime of
`C` over the closed point, and suppose given a complete dévissage of `N/C/A` over the closed point
together with compatible primes of its stages (`Module.CompleteDevissage.Points`). Then the
flatness condition of Stacks Tag 05ML for the local situation `(C_q, N_q)` is corepresented by an
ideal of `A` (`Module.CompleteDevissage.exists_ideal_isFlatAtPrimesAbove_iff`). This is the
induction on the length of the dévissage in the source's proof of Stacks Tag 05PG.

At the last stage the stage map is surjective, so its cokernel is zero and the condition for it
holds everywhere; the step from the cokernel at a stage to the module at that stage is
`Module.exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel`; and the cokernel at a stage is the
module at the next stage, read through the finite maps `Bᵢ → Aᵢ₊₁ ← Bᵢ₊₁` along which the stage
primes are the unique primes above one another (Stacks Tag 05P4, in the form
`Module.isFlatAtPrimesAbove_iff_of_finite`). The same transfer along `C → A₀ ← B₀` starts the
induction.

## Main results

* `Module.CompleteDevissage.exists_ideal_isFlatAtPrimesAbove_iff_stage`: the condition is
  corepresented at every stage.
* `Module.CompleteDevissage.exists_ideal_isFlatAtPrimesAbove_iff`: the condition for `N` at `q` is
  corepresented.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05P4](https://stacks.math.columbia.edu/tag/05P4)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

open scoped TensorProduct

universe u v w x

namespace Module

/-- The condition `Module.IsFlatAtPrimesAbove` holds for a zero module. -/
theorem isFlatAtPrimesAbove_of_subsingleton {A : Type u} [CommRing A] {C : Type v} [CommRing C]
    [Algebra A C] (Q : Ideal C) (N : Type w) [AddCommGroup N] [Module C N] [Subsingleton N]
    (R : Type x) [CommRing R] [IsLocalRing R] [Algebra A R] : IsFlatAtPrimesAbove A C Q N R := by
  let : Algebra R (C ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  intro 𝔮 _ _ _
  have : Subsingleton ((C ⊗[A] R) ⊗[C] N) := by
    refine subsingleton_of_forall_eq 0 fun a ↦ ?_
    induction a using TensorProduct.induction_on with
    | zero => rfl
    | tmul c n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  have : Subsingleton (LocalizedModule 𝔮.primeCompl ((C ⊗[A] R) ⊗[C] N)) := by
    refine ⟨fun a b ↦ ?_⟩
    induction a using LocalizedModule.induction_on with
    | h m s =>
      induction b using LocalizedModule.induction_on with
      | h m' s' =>
        rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
          LocalizedModule.zero_mk]
  exact Module.Flat.of_free

/-- Two finite algebras `C₁ → D ← C₂` over `A` with unique lifts of primes give equivalent
conditions `Module.IsFlatAtPrimesAbove` for the contractions of a prime of `D`. -/
private theorem isFlatAtPrimesAbove_comap_iff_comap {A : Type u} [CommRing A] {C₁ : Type*}
    [CommRing C₁] [Algebra A C₁] {C₂ : Type*} [CommRing C₂] [Algebra A C₂] {D : Type*}
    [CommRing D] [Algebra A D] [Algebra C₁ D] [Algebra C₂ D] [IsScalarTower A C₁ D]
    [IsScalarTower A C₂ D] [Module.Finite C₁ D] [Module.Finite C₂ D] {N : Type w}
    [AddCommGroup N] [Module C₁ N] [Module C₂ N] [Module D N] [IsScalarTower C₁ D N]
    [IsScalarTower C₂ D N] (P : Ideal D) [P.IsPrime]
    (huniq₁ : ∀ P' : Ideal D, P'.IsPrime →
      P'.comap (algebraMap C₁ D) = P.comap (algebraMap C₁ D) → P' = P)
    (huniq₂ : ∀ P' : Ideal D, P'.IsPrime →
      P'.comap (algebraMap C₂ D) = P.comap (algebraMap C₂ D) → P' = P)
    (R : Type x) [CommRing R] [IsLocalRing R] [Algebra A R] :
    IsFlatAtPrimesAbove A C₁ (P.comap (algebraMap C₁ D)) N R ↔
      IsFlatAtPrimesAbove A C₂ (P.comap (algebraMap C₂ D)) N R :=
  (isFlatAtPrimesAbove_iff_of_finite P huniq₁ R).trans
    (isFlatAtPrimesAbove_iff_of_finite P huniq₂ R).symm

namespace CompleteDevissage

variable {A : Type u} [CommRing A] [IsLocalRing A] {C : Type v} [CommRing C] [Algebra A C]
  [Algebra.FiniteType A C] {N : Type w} [AddCommGroup N] [Module C N] [Module.Finite C N]

/-- **The induction step at one stage of a complete dévissage.** If the flatness condition at
the stage prime is corepresented for the cokernel of the stage map, it is corepresented for the
stage module. -/
theorem exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel_stage
    (D : CompleteDevissage A C N (maximalIdeal A)) {q : Ideal C} (pts : D.Points q)
    (i : Fin (D.stepCount + 1)) (J : Ideal A)
    (hJ : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra A R]
      [IsLocalHom (algebraMap A R)],
      IsFlatAtPrimesAbove A (D.B i) (pts.p i) (D.M i ⧸ LinearMap.range (D.alpha i)) R ↔
        Ideal.map (algebraMap A R) J = ⊥) :
    ∃ I : Ideal A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra A R]
      [IsLocalHom (algebraMap A R)],
      IsFlatAtPrimesAbove A (D.B i) (pts.p i) (D.M i) R ↔ Ideal.map (algebraMap A R) I = ⊥ := by
  let : Module A (D.M i) := Module.compHom (D.M i) (algebraMap A (D.A i))
  have : IsScalarTower A (D.B i) (D.M i) :=
    Module.isScalarTower_compHom A (D.B i) (D.A i) (D.M i) (D.toLeft i)
  have : (pts.p i).IsPrime := pts.isPrime_p i
  have : Module.Projective A (D.B i) := projective_lowerAlgebra D i
  have : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A (D.B i)))) := by
    have hsmooth : Smooth (Spec.map (CommRingCat.ofHom (algebraMap A (D.B i)))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 inferInstance)
    have : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap A (D.B i)))) :=
      geometricallyReduced_of_smooth _
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  have : (Algebra.closedFiberIdeal A (D.B i)).IsPrime := D.map_isPrime i
  exact exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel (D.alpha i) (D.fiber_bijective i)
    (pts.comap_p i) J hJ

/-- **The local flattening theorem at every stage of a complete dévissage**, by descending
induction on the stage: at the last stage the cokernel vanishes, and the cokernel at a stage is
the module at the next stage. -/
theorem exists_ideal_isFlatAtPrimesAbove_iff_stage
    (D : CompleteDevissage A C N (maximalIdeal A)) {q : Ideal C} (pts : D.Points q)
    (i : Fin (D.stepCount + 1)) :
    ∃ I : Ideal A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra A R]
      [IsLocalHom (algebraMap A R)],
      IsFlatAtPrimesAbove A (D.B i) (pts.p i) (D.M i) R ↔ Ideal.map (algebraMap A R) I = ⊥ := by
  induction i using Fin.reverseInduction with
  | last =>
    refine exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel_stage D pts _ ⊥ fun R _ _ _ _ ↦ ?_
    have : Subsingleton (D.M (Fin.last D.stepCount) ⧸
        LinearMap.range (D.alpha (Fin.last D.stepCount))) :=
      Submodule.Quotient.subsingleton_iff.mpr
        (LinearMap.range_eq_top.mpr D.final_surjective)
    simp only [Ideal.map_bot, iff_true]
    exact isFlatAtPrimesAbove_of_subsingleton _ _ R
  | cast j ih =>
    obtain ⟨J, hJ⟩ := ih
    refine exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel_stage D pts _ J fun R _ _ _ _ ↦ ?_
    have : (pts.P j.succ).IsPrime := pts.isPrime_P j.succ
    have : Module.Finite (D.B j.castSucc) (D.A j.succ) := RingHom.finite_algebraMap.mp
      (RingHom.Finite.of_surjective (D.toRight j).toRingHom (D.transition_surjective j))
    have h := isFlatAtPrimesAbove_comap_iff_comap (A := A) (C₁ := D.B j.castSucc)
      (C₂ := D.B j.succ) (D := D.A j.succ) (N := D.M j.succ) (pts.P j.succ)
      (fun P' _ h ↦ Ideal.comap_injective_of_surjective _ (D.transition_surjective j) h)
      (fun P' hP' h ↦ pts.unique_P j.succ P' hP' (h.trans (pts.comap_P j.succ))) R
    erw [pts.transition j, pts.comap_P j.succ] at h
    rw [isFlatAtPrimesAbove_congr (A := A) (D.cokerEquiv j) R, h]
    exact hJ R

/-- **The local flattening theorem for a module with a complete dévissage at a point.** -/
theorem exists_ideal_isFlatAtPrimesAbove_iff
    (D : CompleteDevissage A C N (maximalIdeal A)) {q : Ideal C} [q.IsPrime] (pts : D.Points q) :
    ∃ I : Ideal A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra A R]
      [IsLocalHom (algebraMap A R)],
      IsFlatAtPrimesAbove A C q N R ↔ Ideal.map (algebraMap A R) I = ⊥ := by
  obtain ⟨I, hI⟩ := exists_ideal_isFlatAtPrimesAbove_iff_stage D pts 0
  refine ⟨I, fun R _ _ _ _ ↦ ?_⟩
  have : (pts.P 0).IsPrime := pts.isPrime_P 0
  have : Module.Finite C (D.A 0) := RingHom.finite_algebraMap.mp
    (RingHom.Finite.of_surjective D.toA₀.toRingHom D.initial_surjective)
  have h := isFlatAtPrimesAbove_comap_iff_comap (A := A) (C₁ := C) (C₂ := D.B 0) (D := D.A 0)
    (N := D.M 0) (pts.P 0)
    (fun P' _ h ↦ Ideal.comap_injective_of_surjective _ D.initial_surjective h)
    (fun P' hP' h ↦ pts.unique_P 0 P' hP' (h.trans (pts.comap_P 0))) R
  erw [pts.initial, pts.comap_P 0] at h
  rw [isFlatAtPrimesAbove_congr (A := A) D.initialEquiv R, h]
  exact hI R

end CompleteDevissage

end Module

end
