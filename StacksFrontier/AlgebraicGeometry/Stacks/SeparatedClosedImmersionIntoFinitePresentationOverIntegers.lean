module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionIntoFinitePresentationOverIntegers
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main

/-!
# Stacks 0CQ2 over the integers

Over the base `Spec ℤ` (the terminal scheme of the site), a finite-type separated algebraic stack
over a quasi-compact quasi-separated algebraic space `Y` embeds over `Y` by a closed immersion into
an algebraic stack separated and of finite presentation over `Y`. The proof is the proof of
Stacks 0CQ2: the embedding of Stacks 0CQ1
(`AlgebraicGeometry.Stack.exists_closedImmersion_stageModel_of_isFiniteType`) is into
`Y ×_{Y_i} [U_i/R_i]` for every late stage `i`; since `𝒳 = [U/R]` is separated over `Y`, the
relation `(s, t) : R ⟶ U ×_Y U` is proper, hence so is `(s_i, t_i)` for large `i`
(`GroupoidInAlgebraicSpaces.LimitDescent.eventually_isProper_relationMap_stageGroupoid`), so
`[U_i/R_i]` is separated over `Y_i`
(`AlgebraicGeometry.Stack.QuotientStackModel.isSeparated_structureMorphism_iff`), and so is its
base change to `Y`.

## Main results

* `AlgebraicGeometry.Stack.exists_separated_closedImmersion_of_noetherianLimitSystem`: the
  statement over the limit of a Noetherian limit system over any base.
* `AlgebraicGeometry.Stack.exists_separated_finitePresentation_closedImmersion_overIntegers`:
  Stacks 0CQ2 over `Spec ℤ`.

## References

* [Stacks Project, Tag 0CQ2](https://stacks.math.columbia.edu/tag/0CQ2)
* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

open Space

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Stage

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- **Stacks 0CQ2 over the limit of a Noetherian limit system**, granted the inputs of
`AlgebraicGeometry.Stack.exists_closedImmersion_stageModel_of_isFiniteType`, for stages satisfying
the chapter's convention of Section 70.2 (`hconv`). Let `f : 𝒳 ⟶ Y` be separated and locally of
finite type with `𝒳` quasi-compact, with `Y = lim Y_i`. Then `𝒳` embeds over `Y` by a closed
immersion into an algebraic stack separated and of finite presentation over `Y`: the base change
`Y ×_{Y_i} [U_i/R_i]` of the stage stack at a stage `i` at which `(s_i, t_i)` is proper. -/
theorem exists_separated_closedImmersion_of_noetherianLimitSystem
    (D : Space.NoetherianLimitSystem B S hS B.contains_terminal I)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property)
    (hlft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hsep : AlgebraicStacks.IsSeparated B S hS f)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
            B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z)
    (hconv : Space.SiteContainsBaseChangeLimits B S hS D.system) :
    ∃ (𝒳' : AlgebraicStacks.{u, w} B S hS)
      (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property)
      (i : 𝒳 ⟶ 𝒳'),
      AlgebraicStacks.IsSeparated B S hS f' ∧
        AlgebraicStacks.IsFinitePresentation B S hS f' ∧
          AlgebraicStacks.IsClosedImmersion B S hS i ∧
            Nonempty (i ≫ f' ≅ f) := by
  obtain ⟨G, Δ, hUqs, hRqs, ⟨e⟩, hst⟩ := exists_closedImmersion_stageModel_of_isFiniteType D 𝒳 f
    hlft h𝒳qc (AlgebraicStacks.isQuasiSeparated_of_isSeparated B S hS hsep) h07SU
  -- `𝒳 = [U/R]` is separated over `Y`, so `(s, t) : R ⟶ U ×_Y U` is proper
  have hrel : Space.IsProper B S hS (GroupoidInAlgebraicSpaces.relationMap G) :=
    QuotientStackModel.isProper_relationMap_of_isSeparated
      (QuotientStackModel.ofEquivalenceOver 𝒳 f e) hsep
  -- hence so is `(s_i, t_i)` at a late stage `i`
  obtain ⟨i, hi, hprop⟩ :=
    GroupoidInAlgebraicSpaces.LimitDescent.eventually_isProper_relationMap_stageGroupoid
      (Δ := Δ) hUqs hRqs hrel hconv
  obtain ⟨M, -, hfp, ι, hι, hiso⟩ := hst i hi
  -- so the stage stack `[U_i/R_i]` is separated over `Y_i`, and so is its base change to `Y`
  have hsm := Δ.stageGroupoid_isSmooth i hi
  have hMsep : AlgebraicStacks.IsSeparated B S hS M.structureMorphism :=
    (M.isSeparated_structureMorphism_iff
      (isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w} hsm) hsm).2 (hprop i le_rfl)
  refine ⟨_, _, ι, ?_, hfp, hι, hiso⟩
  exact AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct B S hS
    M.structureMorphism _ _ (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      M.structureMorphism _) hMsep

end Stage

end General

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0CQ2 over `Spec ℤ`.** Let `f : 𝒳 ⟶ Y` be a separated 1-morphism locally of finite
type from a quasi-compact algebraic stack over `Spec ℤ` to a quasi-compact quasi-separated
algebraic space (a 1-morphism of finite type into `Y` has quasi-compact source). Then there are a
separated 1-morphism of finite presentation `f' : 𝒳' ⟶ Y` and a closed immersion `i : 𝒳 ⟶ 𝒳'`
with `i ≫ f' ≅ f`.

Stacks 07SU writes `Y` as the limit of a Noetherian approximation satisfying the chapter's
convention (`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`), and
`AlgebraicGeometry.Stack.exists_separated_closedImmersion_of_noetherianLimitSystem` applies to
it. -/
theorem exists_separated_finitePresentation_closedImmersion_overIntegers
    (Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (𝒳 : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ Y hY)
    (hlft : AlgebraicStacks.IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B (⊤_ Scheme.{u}) hZ 𝒳.val 𝒳.property)
    (hsep : AlgebraicStacks.IsSeparated B (⊤_ Scheme.{u}) hZ f)
    (hYqc : Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y) :
    ∃ (𝒳' : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
      (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ Y hY)
      (i : 𝒳 ⟶ 𝒳'),
      AlgebraicStacks.IsSeparated B (⊤_ Scheme.{u}) hZ f' ∧
        AlgebraicStacks.IsFinitePresentation B (⊤_ Scheme.{u}) hZ f' ∧
          AlgebraicStacks.IsClosedImmersion B (⊤_ Scheme.{u}) hZ i ∧
            Nonempty (i ≫ f' ≅ f) := by
  obtain ⟨U, a, -, has, hae⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (⊤_ Scheme.{u}) hZ Y
      hY).mp hYqc
  obtain ⟨A, hconv⟩ := Space.hasConventionalNoetherianApproximation_of_etaleAtlas hY hYqc hYqs U a
    has hae
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let D := A.toNoetherianLimitSystem hY
  obtain ⟨𝒳', f', ι, h₁, h₂, h₃, h₄⟩ := exists_separated_closedImmersion_of_noetherianLimitSystem
    D 𝒳 f hlft h𝒳qc hsep
    (fun _ hZ' hqc hqs => Space.hasNoetherianApproximation_of_isQuasiCompactSpace hZ' hqc hqs)
    hconv
  exact ⟨𝒳', f', ι, h₁, h₂, h₃, h₄⟩

end AlgebraicGeometry.Stack

end
