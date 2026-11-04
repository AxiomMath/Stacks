module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjTwists.Basic

/-!
# Global sections from degree-zero and twisted homogeneous elements

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring and `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `S`-module. A
degree-zero element of `M` gives a global section of the sheaf `M̃` on `Proj 𝒮`, and the
resulting map `M₀ → Γ(Proj 𝒮, M̃)` is the canonical one; it is
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections`.

The twist `M(n)` is the same module with the grading shifted by `n`, so its degree-zero part is
`Mₙ`. The same canonical map, applied to the shifted grading, is therefore the map
`Mₙ → Γ(Proj 𝒮, M(n)~)`. For that application to typecheck, the shifted grading has to be a
graded module again: this file supplies the two missing instances, that the shift of a
decomposition is a decomposition and that the shift of a compatible action is compatible.

## Main definitions

* `Stacks.GradedModule.shiftedGradingDecomposition`: the shift of a direct-sum decomposition is
  a direct-sum decomposition.
* `Stacks.GradedModule.shiftedGradingGradedSMul`: a graded ring acts on the shift of a graded
  module compatibly with the gradings.

## Main results

* `Stacks.GradedModule.shiftedGrading_zero`: the degree-zero piece of the twist is the
  degree-`n` piece of `M`, `M(n)₀ = Mₙ`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections` is the canonical
  map `M₀ → Γ(Proj 𝒮, M̃)`, which is Tag 0AG1; that tag is recorded on it here.

## Implementation notes

The source displays these two maps as formulas, the second being the first applied to the
twist. The degree-zero map is the one already constructed, and is `𝒮 0`-linear with the scalar
action on global sections induced by the canonical map from `𝒮 0` to global functions, and
Tag 0AG1 is recorded on it. Tag 0AG2's map
`Mₙ → Γ(Proj 𝒮, M(n)~)` is not that declaration, because the degree-zero map of a grading
`𝒩` has source `𝒩 0`, and for `𝒩 = M(n)` that is `M_{0 + n}`: the identification with `Mₙ` is
`zero_add`, which is not a reduction in `ℤ`, so an element of `Mₙ` has to be transported
before it can be fed to the degree-zero map. The transport is `shiftedGrading_zero` here, and
the resulting map is
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`, where Tag 0AG2 is
recorded on it.

The decomposition of the shift is transported along the reindexing additive equivalence of
`DirectSum.equivCongrLeft` for the translation `i ↦ i - n` of `ℤ`. The grading action of `ℕ`
degrees on `ℤ` degrees is the scoped instance `Stacks.GradedLocalization.instVAddNatInt`, the
same one the global-sections map was built with.

## References

* [Stacks Project, Tag 0AG1](https://stacks.math.columbia.edu/tag/0AG1)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
-/

@[expose] public noncomputable section

namespace Stacks.GradedModule

open DirectSum
open Stacks.GradedLocalization

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- The degree-zero piece of the twist `M(n)` is the degree-`n` piece of `M`: `M(n)₀ = Mₙ`.
The two indices are `0 + n` and `n`, which are equal by `zero_add` and not by reduction. -/
@[stacks 0AG2 "twist_degree_zero"]
public theorem shiftedGrading_zero {M : Type v} {τ : Type t} [SetLike τ M] (𝒩 : ℤ → τ) (n : ℤ) :
    shiftedGrading 𝒩 n 0 = 𝒩 n :=
  congrArg 𝒩 (zero_add n)

/-- The shift of a direct-sum decomposition is a direct-sum decomposition: reindexing the
pieces by the translation `i ↦ i - n` of `ℤ` is an additive equivalence of direct sums over
the identity of the ambient module. -/
public noncomputable instance shiftedGradingDecomposition (n : ℤ) :
    Decomposition (shiftedGrading 𝒨 n) := by
  classical
  let e : ℤ ≃ ℤ :=
    { toFun := fun i => i - n
      invFun := fun i => i + n
      left_inv := by intro i; dsimp; omega
      right_inv := by intro i; dsimp; omega }
  let E : (⨁ i, 𝒨 i) ≃+ ⨁ i, 𝒨 (i + n) :=
    DirectSum.equivCongrLeft e
  have hcomp : (DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 n)).comp E.toAddMonoidHom =
      DirectSum.coeAddMonoidHom 𝒨 := by
    apply DirectSum.addHom_ext
    intro i x
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    change DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 n)
        (E (DirectSum.of (fun i => 𝒨 i) (e.symm k) x)) =
      DirectSum.coeAddMonoidHom 𝒨 (DirectSum.of (fun i => 𝒨 i) (e.symm k) x)
    rw [show E (DirectSum.of (fun i => 𝒨 i) (e.symm k) x) =
      DirectSum.of (fun j => 𝒨 (j + n)) k x from by
        simpa [E, e] using
          (DirectSum.equivCongrLeft_of (β := fun j => 𝒨 j) (h := e) (k := k) x)]
    simp only [DirectSum.coeAddMonoidHom_of]
  refine ⟨E ∘ (DirectSum.decompose 𝒨), ?_, ?_⟩
  · intro m
    exact (congrArg (fun f : (⨁ i, 𝒨 i) →+ M => f ((DirectSum.decompose 𝒨) m))
      hcomp).trans ((DirectSum.decompose 𝒨).left_inv m)
  · intro x
    have h := congrArg (fun f : (⨁ i, 𝒨 i) →+ M => f (E.symm x)) hcomp
    have hx : DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 n) x =
        DirectSum.coeAddMonoidHom 𝒨 (E.symm x) := by simpa using h
    change E ((DirectSum.decompose 𝒨)
      (DirectSum.coeAddMonoidHom (shiftedGrading 𝒨 n) x)) = x
    rw [hx]
    exact (congrArg E ((inferInstance : Decomposition 𝒨).right_inv (E.symm x))).trans
      (E.apply_symm_apply x)

/-- A graded ring acts on the shift of a graded module compatibly with the gradings: the degree
of `a • x` for `a` of degree `i` and `x` of degree `j` in `M(n)` is `(i + j) + n`. -/
public instance shiftedGradingGradedSMul (n : ℤ) :
    SetLike.GradedSMul 𝒮 (shiftedGrading 𝒨 n) := by
  refine ⟨fun {i j a b} ha hb => ?_⟩
  have h := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) ha hb
  change a • b ∈ 𝒨 ((i : ℤ) + (j + n)) at h
  change a • b ∈ 𝒨 (((i : ℤ) + j) + n)
  simpa only [add_assoc] using h

end Stacks.GradedModule

add_to_stacks 0AG1
  Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections

end
