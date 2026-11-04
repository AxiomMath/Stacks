module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionIntoFinitePresentationImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverQuasiCompactQuasiSeparated

/-!
# Stacks 0CQ1 over the integers

Over the base `Spec ℤ` (the terminal scheme of the site), a finite-type quasi-separated algebraic
stack over a quasi-compact quasi-separated algebraic space `Y` embeds over `Y` by a closed
immersion into an algebraic stack of finite presentation over `Y`. The proof is the proof of Stacks
0CQ1: by absolute Noetherian approximation `Y` is the limit of a Noetherian limit system, and
`AlgebraicGeometry.Stack.exists_closedImmersion_stageModel_of_isFiniteType` gives the stage stack
and the closed immersion.

## Main results

* `AlgebraicGeometry.Space.NoetherianApproximation.toNoetherianLimitSystem`: a Noetherian
  approximation over `Spec ℤ` is a Noetherian limit system.
* `AlgebraicGeometry.Stack.exists_finitePresentation_closedImmersion_overIntegers`: Stacks 0CQ1
  over `Spec ℤ`, granted the held statements its proof cites.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space.NoetherianApproximation

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- **A Noetherian approximation over `Spec ℤ` is a Noetherian limit system**: its stages are
quasi-separated and of finite type over `Spec ℤ`, hence Noetherian, and the approximated space is
the point of the limit cone. -/
noncomputable def toNoetherianLimitSystem (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Y)
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y) :
    letI := A.preorder; letI := A.nonempty; letI := A.isDirected
    NoetherianLimitSystem B (⊤_ Scheme.{u}) hZ hZ A.I :=
  letI := A.preorder; letI := A.nonempty; letI := A.isDirected
  { system := A.diagram
    system_isAlgebraicSpace := fun i => A.isAlgebraicSpace (op i)
    noetherian := fun i => isNoetherian_of_isFiniteType_viewOverIntegers _ _ _ _ _
      (A.isAlgebraicSpace (op i)) (A.isAbsolutelyQuasiSeparated (op i))
      (A.isFiniteTypeOverIntegers (op i))
    transition_affine := fun f => A.isAffineHom_map f
    limitCone := Cone.mk Y A.π
    isLimit := A.isLimit
    limit_isAlgebraicSpace := hY }

end AlgebraicGeometry.Space.NoetherianApproximation

namespace AlgebraicGeometry.Stack

open Space

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0CQ1 over `Spec ℤ`**, granted the held statements its proof cites: absolute
Noetherian approximation (`h07SU`, Stacks 07SU), which is also the one input of the staged
Stacks 0CP7. Let `f : 𝒳 ⟶ Y` be a 1-morphism locally of finite type and quasi-separated from a
quasi-compact algebraic stack over `Spec ℤ` to a quasi-compact quasi-separated algebraic space (a
quasi-separated 1-morphism of finite type into `Y` has quasi-compact source). Then there are a
1-morphism of finite presentation `f' : 𝒳' ⟶ Y` and a closed immersion `i : 𝒳 ⟶ 𝒳'` with
`i ≫ f' ≅ f`. -/
theorem exists_finitePresentation_closedImmersion_overIntegers
    (Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (𝒳 : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ Y hY)
    (hlft : AlgebraicStacks.IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B (⊤_ Scheme.{u}) hZ 𝒳.val 𝒳.property)
    (hqs : AlgebraicStacks.IsQuasiSeparated B (⊤_ Scheme.{u}) hZ f)
    (hYqc : Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
          B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (𝒳' : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
      (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ Y hY)
      (i : 𝒳 ⟶ 𝒳'),
      AlgebraicStacks.IsFinitePresentation B (⊤_ Scheme.{u}) hZ f' ∧
        AlgebraicStacks.IsClosedImmersion B (⊤_ Scheme.{u}) hZ i ∧
          Nonempty (i ≫ f' ≅ f) := by
  obtain ⟨A⟩ := h07SU Y hY hYqc hYqs
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let D := A.toNoetherianLimitSystem hY
  obtain ⟨G, Δ, -, -, -, hst⟩ :=
    exists_closedImmersion_stageModel_of_isFiniteType D 𝒳 f hlft h𝒳qc hqs h07SU
  obtain ⟨M, -, hfp, ι, hι, hiso⟩ := hst Δ.index le_rfl
  exact ⟨_, _, ι, hfp, hι, hiso⟩

end AlgebraicGeometry.Stack

end
