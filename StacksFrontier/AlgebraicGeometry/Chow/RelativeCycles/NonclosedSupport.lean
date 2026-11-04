module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a family of cycles need not be closed

The support of a family of cycles on the fibres of a morphism locally of finite type is a
union of images of fibrewise supports, and there is no reason for that union to be closed.
This file exhibits a counterexample: on the spectrum of the integers, viewed over itself by
the identity, the family of `0`-cycles that is the prime cycle of the generic point on the
generic fibre and zero elsewhere has support the generic point, which is not closed.

## Main results

* `Stacks.Chow.exists_family_support_not_closed` — there is a morphism locally of finite type
  and a family of cycles on its fibres whose support is not closed.

## Implementation notes

Every fibre of the identity morphism is the spectrum of a residue field, so it is a point and
its cycles of dimension zero are the free abelian group on that point; this is what makes the
family easy to write down. The scheme is `Spec (ULift ℤ)` rather than `Spec ℤ` so that it is a
scheme in the ambient universe.

## References

* [Stacks Project, Tag 0H4U](https://stacks.math.columbia.edu/tag/0H4U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The fibre of an identity morphism maps isomorphically to the spectrum of the residue field. -/
private theorem isIso_fiberToSpecResidueField_id {X : Scheme.{u}} (s : X) :
    IsIso (Scheme.Hom.fiberToSpecResidueField (𝟙 X) s) := by
  dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
  infer_instance

/-- On the fibre of an identity morphism every point has relative dimension zero: the fibre is
the spectrum of the residue field, and the residue field extension is an isomorphism. -/
private theorem genericFiber_relativeDimension_zero {X : Scheme.{u}} (s : X)
    (y : Scheme.Hom.fiber (𝟙 X) s) :
    relativeDimension (fieldChowSituation (X.residueField s)).dimensionFunction
      (Scheme.Hom.fiberToSpecResidueField (𝟙 X) s) y = 0 := by
  let K := X.residueField s
  let T := Scheme.Hom.fiber (𝟙 X) s
  let p := Scheme.Hom.fiberToSpecResidueField (𝟙 X) s
  have hp : IsIso p := isIso_fiberToSpecResidueField_id s
  have hres : IsIso (p.residueFieldMap y) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (p.stalkMap y)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let : Algebra ((Spec (.of K)).residueField (p y)) (T.residueField y) :=
    (p.residueFieldMap y).hom.toAlgebra
  have hsurj : Function.Surjective
      (algebraMap ((Spec (.of K)).residueField (p y)) (T.residueField y)) := by
    change Function.Surjective (p.residueFieldMap y).hom
    exact (ConcreteCategory.isIso_iff_bijective _).mp hres |>.2
  have htrdeg : Algebra.trdeg ((Spec (.of K)).residueField (p y)) (T.residueField y) = 0 :=
    trdeg_zero_of_surjective_algebraMap _ _ hsurj
  change (fieldChowSituation K).dimensionFunction (p y) +
      (Cardinal.toNat (Algebra.trdeg ((Spec (.of K)).residueField (p y))
        (T.residueField y)) : ℤ) = 0
  rw [fieldChowSituation_dimensionFunction_eq_zero K (p y), htrdeg]
  norm_num

/-- **Stacks Project, Tag 0H4U.** The support of a family of cycles on fibres need not be
closed in the total space. -/
@[stacks 0H4U]
theorem exists_family_support_not_closed :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S) (h : LocallyOfFiniteType f),
      letI : LocallyOfFiniteType f := h
      ∃ (r : ℕ) (α : FamilyOfCycles f r), ¬ IsClosed (supportOfFamily f α) := by
  classical
  let A : Type u := ULift.{u} ℤ
  let : IsDomain A := (ULift.ringEquiv : A ≃+* ℤ).isDomain
  let X : Scheme.{u} := Spec (.of A)
  let f : X ⟶ X := 𝟙 X
  have hfft : LocallyOfFiniteType f := inferInstanceAs (LocallyOfFiniteType (𝟙 X))
  let η : X := genericPoint X
  let q₀ : PrimeSpectrum ℤ := ⟨Ideal.span {(2 : ℤ)},
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2
      (Int.prime_iff_natAbs_prime.mpr (by norm_num))⟩
  let e : A ≃+* ℤ := ULift.ringEquiv
  let q : X := PrimeSpectrum.comap e.toRingHom q₀
  have hηq : η ≠ q := by
    intro heq
    have hI : q.asIdeal = (⊥ : Ideal A) := by
      calc
        q.asIdeal = η.asIdeal := congrArg PrimeSpectrum.asIdeal heq.symm
        _ = ⊥ := by
          dsimp [η, X]
          exact congrArg PrimeSpectrum.asIdeal
            (genericPoint_eq_bot_of_affine (CommRingCat.of A))
    have hmem : e.symm (2 : ℤ) ∈ q.asIdeal := by
      change e (e.symm (2 : ℤ)) ∈ q₀.asIdeal
      rw [e.apply_symm_apply]
      exact Ideal.subset_span (by simp)
    exact two_ne_zero ((map_eq_zero_iff e.symm e.symm.injective).1 (Ideal.mem_bot.mp (hI ▸ hmem)))
  have hclosure : closure ({η} : Set X) = Set.univ := genericPoint_closure X
  have hη_not_closed : ¬ IsClosed ({η} : Set X) := by
    intro hc
    exact hηq (Set.mem_singleton_iff.mp
      (hc.closure_subset (hclosure.symm ▸ Set.mem_univ q))).symm
  let K := X.residueField η
  let p := f.fiberToSpecResidueField η
  let : LocallyOfFiniteType p := by
    change LocallyOfFiniteType (pullback.snd f (X.fromSpecResidueField η))
    infer_instance
  let C := fieldChowSituation K
  let x₀ := f.asFiber η
  have hp : IsIso p := isIso_fiberToSpecResidueField_id η
  let c : AlgebraicCycle (f.fiber η) ℤ := Function.locallyFinsuppWithin.single x₀ (1 : ℤ)
  have hc : c ∈ cyclesOfDimension C p 0 := by
    rw [mem_cyclesOfDimension]
    intro Z hZ
    unfold deltaDimension
    exact genericFiber_relativeDimension_zero η Z.isIrreducible.genericPoint
  let cη : FiberCycleGroup f η 0 := ⟨c, hc⟩
  let α : FamilyOfCycles f 0 := fun s => if hs : s = η then hs ▸ cη else 0
  let x₀' : f.fiber η := x₀
  have hx₀ : x₀' ∈ tsupport (α η : AlgebraicCycle (f.fiber η) ℤ) := by
    apply subset_closure
    rw [show α η = cη by simp [α]]
    change (Function.locallyFinsuppWithin.single x₀ (1 : ℤ)) x₀ ≠ 0
    rw [Function.locallyFinsuppWithin.single_apply]
    simp
  have hxpoint : f.fiberι η x₀' = η := Scheme.Hom.fiberι_asFiber f η
  have : Subsingleton (f.fiber η) := by
    let H := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso p))
    have : Subsingleton (Scheme.forgetToTop.obj (Spec (X.residueField η))) := by
      change Subsingleton (PrimeSpectrum (X.residueField η))
      infer_instance
    exact ⟨fun y z => H.injective (Subsingleton.elim _ _)⟩
  have hsupport : supportOfFamily f α = {η} := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [mem_supportOfFamily] at hx
      rcases hx with ⟨s, y, hy, rfl⟩
      by_cases hs : s = η
      · subst s
        have : y = x₀' := Subsingleton.elim _ _
        subst y
        exact hxpoint
      · simp [α, hs] at hy
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      rw [mem_supportOfFamily]
      exact ⟨η, x₀', hx₀, hxpoint⟩
  refine ⟨X, X, f, hfft, 0, α, ?_⟩
  simpa [hsupport] using hη_not_closed

end Stacks.Chow
