module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryLift
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryUnitClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueCechData

/-!
# The boundary of the residue sequence is cup product with the first Chern class

Let `X → S` be a morphism of schemes, `ℒ` an invertible `𝒪_X`-module, `π : L → X` the line
bundle with zero section `0 : X → L`, and `L* = L \ 0(X)` its complement. The boundary map
`δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of the shifted residue sequence
`0 → Ω^•_{X/S}[1] → (π_* Ω^•_{L*/S})_0[1] → Ω^•_{X/S} → 0` of [Stacks, Tag 0FUF], in the derived
category `D(f^{-1}𝒪_S)`, is the morphism `ξ'` attached by [Stacks, Tag 0FU7] to the de Rham first
Chern class `ξ = c₁^{dR}(ℒ) ∈ H²_{dR}(X/S)` of [Stacks, Tag 0FLE].

The proof is the Stacks one: `δ` lifts to the derived category of right differential graded
`Ω^•_{X/S}`-modules
(`Stacks.LineBundle.Situation.exists_deRhamForgetHom_eq_residueShiftedSequence_boundary`), and
`δ(1) = c₁^{dR}(ℒ)`, by mapping the sequence `0 → 𝒪_X^* → E → ℤ → 0` of abelian sheaves into the
translated residue sequence
(`Stacks.LineBundle.Situation.deRhamEvalOne_residueBoundary_eq_of_cech`, with the Čech data
`Stacks.LineBundle.Situation.exists_residueCechData` and the class of the lift of `1`,
`Stacks.LineBundle.Situation.realizationIsoAt_imageCycleClass`); the uniqueness of
[Stacks, Tag 0FU7] concludes.

## Main results

* `Stacks.LineBundle.Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism`:
  [Stacks, Tag 0FUG].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.LineBundle

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0FUG.** For a line bundle `ℒ` on `X` over `S`, the boundary map
`δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` in `D(f^{-1}𝒪_S)` of the shifted residue sequence of Tag 0FUF is the
morphism `ξ'` of Tag 0FU7 attached to the de Rham first Chern class `ξ = c₁^{dR}(ℒ)`. -/
@[stacks 0FUG "the boundary map of the shifted residue sequence of 0FUF for the complement of the
  zero section of a line bundle is the map of 0FU7 for its de Rham first Chern class"]
theorem Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism (D : Situation.{u}) :
    D.residueShiftedSequence.boundary =
      AlgebraicGeometry.SheafOfModules.deRhamClassMorphism (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) 2
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass (X := D.X.toRingedSpace)
          (Scheme.Hom.deRhamAlgebras D.f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) D.L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ D.L D.invertible)) := by
  obtain ⟨t, I, Ui, hUi, e, z, ω, he, hωz, hω, hz, hone⟩ := D.exists_residueCechData
  exact AlgebraicGeometry.SheafOfModules.eq_deRhamClassMorphism _ _ 2 _
    D.exists_deRhamForgetHom_eq_residueShiftedSequence_boundary
    (D.deRhamEvalOne_residueBoundary_eq_of_cech
      (Stacks.SheafOfModules.Picard.classOf D.X.toRingedSpace.sheaf.obj
        (_root_.structureSheaf D.X.toRingedSpace.sheaf).property D.L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ D.L D.invertible))
      t Ui hUi e he z ω hωz hω hz (D.realizationIsoAt_imageCycleClass t hone))

end Stacks.LineBundle

end
