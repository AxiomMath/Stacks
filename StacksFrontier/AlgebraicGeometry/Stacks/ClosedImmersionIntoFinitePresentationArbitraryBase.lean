module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionIntoFinitePresentationOverIntegers
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedClosedImmersionIntoFinitePresentationArbitraryBase

/-!
# Stacks 0CQ1 over an arbitrary base scheme

Let `f : 𝒳 ⟶ Y` be a quasi-separated 1-morphism of finite type from an algebraic stack over a
scheme `S` to a quasi-compact quasi-separated algebraic space. Then `f` factors, up to
2-isomorphism, as a closed immersion `𝒳 ⟶ 𝒳'` followed by a 1-morphism of finite presentation
`𝒳' ⟶ Y` (Stacks 0CQ1).

The source's proof writes `Y` as a limit of Noetherian algebraic spaces by absolute Noetherian
approximation (Stacks 07SU), which is a statement over `Spec ℤ`; over the base `Spec ℤ` the proof
is `AlgebraicGeometry.Stack.exists_finitePresentation_closedImmersion_overIntegers`, whose one
input is Stacks 07SU itself, here supplied by
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`. Over an arbitrary
base `S` we view everything over `Spec ℤ` by Construction A of Stacks 04X5, apply that result,
and carry the factorization back to `S` by Construction B
(`AlgebraicGeometry.Stack.exists_descent_changeBase`); finite presentation and being a closed
immersion descend along Construction A.

## Main results

* `exists_isFinitePresentation_isClosedImmersion_of_isFiniteType`: Stacks 0CQ1, over an
  arbitrary base scheme `S`.

## References

* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

/-- **Stacks 0CQ1.** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack over a scheme `S`
to an algebraic space over `S`, with `f` of finite type and quasi-separated and `Y` quasi-compact
and quasi-separated. Then there are a 1-morphism of finite presentation `f' : 𝒳' ⟶ Y` and a
closed immersion `i : 𝒳 ⟶ 𝒳'` of algebraic stacks over `Y`, that is, with `i ≫ f' ≅ f`.

The source's proof, which approximates `Y` by Noetherian algebraic spaces (Stacks 07SU), takes
place over `Spec ℤ`, where it is
`AlgebraicGeometry.Stack.exists_finitePresentation_closedImmersion_overIntegers` with Stacks 07SU
supplied by `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`.
Construction A of Stacks 04X5 carries `f` to a quasi-separated 1-morphism, locally of finite
type, from a quasi-compact algebraic stack to the view `Λ Y` of `Y` over `Spec ℤ`, which is again
quasi-compact and quasi-separated; the factorization obtained there descends to `S`
(`AlgebraicGeometry.Stack.exists_descent_changeBase`), and finite presentation and being a closed
immersion descend along Construction A. -/
@[stacks 0CQ1]
theorem exists_isFinitePresentation_isClosedImmersion_of_isFiniteType (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (𝒳' : AlgebraicStacks.{u, w} B S hS)
      (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (i : 𝒳 ⟶ 𝒳'),
      IsFinitePresentation B S hS f' ∧ IsClosedImmersion B S hS i ∧ Nonempty (i ≫ f' ≅ f) := by
  let hZ := B.contains_terminal
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  have hY' := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY
  obtain ⟨hΦ, hΦm, hΨ, -⟩ :=
    isFinitePresentation_viewAlgebraicSpaceStackComparisons.{u, w} B S (⊤_ Scheme.{u}) hS hZ g
      Y hY
  have hlft := isLocallyOfFiniteType_comp B (⊤_ Scheme.{u}) hZ _ _
    (isLocallyOfFiniteType_changeBaseHomAlgebraicStacks B S (⊤_ Scheme.{u}) hS hZ g Y hY 𝒳 f
      hft.1)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hZ hΦ.1)
  have h𝒳qc := (isQuasiCompactStack_changeBaseAlgebraicStacks_iff B S (⊤_ Scheme.{u}) hS hZ g
    𝒳).2 (isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hft.2
      (isQuasiCompactStack_fibredCategory.{u, w} B S hS Y hY hYqc _))
  have hqs' : IsQuasiSeparated B (⊤_ Scheme.{u}) hZ
      (changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g f) :=
    ⟨isQuasiCompact_relativeDiagonal_changeBase B S (⊤_ Scheme.{u}) hS hZ g _ _ f.hom hqs.1,
      isQuasiSeparated_relativeDiagonal_changeBase B S (⊤_ Scheme.{u}) hS hZ g _ _ f.hom hqs.2⟩
  obtain ⟨𝒳'', f'', ι, hfp, hι, ⟨e⟩⟩ :=
    exists_finitePresentation_closedImmersion_overIntegers hZ
      ((OverShriek.relocalizePresheafFunctor g).obj Y) hY'
      (changeBaseAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g 𝒳)
      (changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g f ≫
        viewAlgebraicSpaceStackToRelocalized.{u, w} B S (⊤_ Scheme.{u}) hS hZ g Y hY) hlft h𝒳qc
      (isQuasiSeparated_comp B _ hZ _ _ hqs'
        (isQuasiSeparated_of_isMonomorphism B _ hZ _ hΦm))
      (Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj B S (⊤_ Scheme.{u}) hS hZ g Y
        hYqc)
      (Space.isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs)
      (fun _ hZ' hqc hqs => Space.hasNoetherianApproximation_of_isQuasiCompactSpace hZ' hqc hqs)
  have e' : ι ≫ (f'' ≫ relocalizedToViewAlgebraicSpaceStack.{u, w} B S (⊤_ Scheme.{u}) hS hZ g
      Y hY) ≅ changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g f :=
    (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e _ ≪≫
      Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso _
        (viewAlgebraicSpaceStackRoundTripIso B S (⊤_ Scheme.{u}) hS hZ g Y hY) ≪≫
      Bicategory.rightUnitor _
  obtain ⟨𝒳', f', i, ⟨eiso⟩, hPf, hPi⟩ :=
    exists_descent_changeBase B S (⊤_ Scheme.{u}) hS hZ g f 𝒳'' _ ι e'
  have hfp' := isFinitePresentation_comp B _ hZ _ _ hfp hΨ
  refine ⟨𝒳', f', i, ⟨?_, ?_, ?_⟩, ?_, ⟨eiso⟩⟩
  · exact isLocallyOfFinitePresentation_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g Y hY 𝒳' f'
      (hPf (fun φ => IsLocallyOfFinitePresentation B _ hZ φ) hfp'.1)
  · exact isQuasiCompactMorphism_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g f'
      (hPf (fun φ => IsQuasiCompactMorphism B _ hZ φ) hfp'.2.1)
  · exact isQuasiSeparated_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g f'
      (hPf (fun φ => IsQuasiSeparated B _ hZ φ) hfp'.2.2)
  · exact isClosedImmersion_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g i
      (hPi (fun φ => IsClosedImmersion B _ hZ φ) hι)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
