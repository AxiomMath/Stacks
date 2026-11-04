module

public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleUniqueness0BVG

/-!
# The different does not depend on the relative dualizing module

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes.  The
different `𝔇_f = AlgebraicGeometry.Scheme.Hom.different f` of [Stacks, Tag 0BW4] is built from
the relative dualizing module `Stacks.Discriminant.relativeDualizingModuleData f`, which is one
choice among the data of [Stacks, Tag 0BVG].  This file shows that the choice does not matter:
for every relative dualizing module datum `ω` and every trace element `τ` of it, the annihilator
`Stacks.Discriminant.different ω τ` of `Coker(τ : 𝒪_Y → ω)` is `𝔇_f`.

## Main results

* `Stacks.Discriminant.different_eq_different`: any two relative dualizing module data, with
  their trace elements, give the same annihilator.
* `AlgebraicGeometry.Scheme.Hom.different_eq`: that annihilator is the different of `f`.

## Implementation notes

On an affine chart `V = Spec B` over `U = Spec A` the sections of `different ω τ` are the ideal
`Ann_B(ω_{B/A} / B τ_{B/A})` (`Stacks.Discriminant.different_sections_eq_cokerSpanIdeal`), which
is computed from a finite-open factorization of `A → B` alone and so involves no choice of `ω`.
The source charts of the affine chart pairs of `f` form a basis of `Y`, and membership in a
subsheaf is local, so the two subsheaves agree.

## References

* [Stacks Project, Tag 0BW4](https://stacks.math.columbia.edu/tag/0BW4)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Discriminant

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyQuasiFinite f]

/-- **The different does not depend on the relative dualizing module.** Any two relative
dualizing module data of `f`, with their trace elements, give the same annihilator of the
cokernel of the trace morphism: on every affine chart both are the annihilator of
`ω_{B/A} / B τ_{B/A}`, and the source charts of the affine chart pairs form a basis. -/
theorem different_eq_different (ω ω' : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (τ' : RelativeTraceSection ω') :
    different ω τ = different ω' τ' := by
  have hchart : ∀ p : AffineChartPair f,
      (different ω τ).toSubmodule.obj (op ((p.1).2).1) =
        (different ω' τ').toSubmodule.obj (op ((p.1).2).1) := by
    rintro ⟨⟨U, V⟩, hVU⟩
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
      Classical.choice (ω.factorization U V hVU)
    exact (different_sections_eq_cokerSpanIdeal ω τ U V hVU F).trans
      (different_sections_eq_cokerSpanIdeal ω' τ' U V hVU F).symm
  have hle : ∀ N₁ N₂ : (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).Submodule,
      (∀ p : AffineChartPair f,
        N₁.toSubmodule.obj (op ((p.1).2).1) = N₂.toSubmodule.obj (op ((p.1).2).1)) →
      N₁ ≤ N₂ := by
    intro N₁ N₂ h
    refine SheafOfModules.Submodule.le_iff.mpr
      (PresheafOfModules.Submodule.le_iff.mpr fun W s hs ↦ ?_)
    refine N₂.isSheaf s fun y hy ↦ ?_
    obtain ⟨p, hyp, hpW⟩ := exists_affineChartPair_le f W.unop y hy
    refine ⟨_, homOfLE hpW, ?_, hyp⟩
    have hmem := N₁.toSubmodule.map_mem (homOfLE hpW).op hs
    rw [h p] at hmem
    exact hmem
  exact le_antisymm (hle _ _ hchart) (hle _ _ fun p ↦ (hchart p).symm)

variable (f) [LocallyOfFiniteType f]

/-- **The different of `f` is the annihilator for every relative dualizing module.** For every
relative dualizing module datum `ω` of `f` and every trace element `τ` of it, the annihilator of
`Coker(τ : 𝒪_Y → ω)` is the different `𝔇_f` of [Stacks, Tag 0BW4]. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.different_eq (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) : f.different = Stacks.Discriminant.different ω τ :=
  different_eq_different (relativeDualizingModuleData f) ω
    (RelativeTraceSection.canonical (relativeDualizingModuleData f)) τ

end Stacks.Discriminant

end
