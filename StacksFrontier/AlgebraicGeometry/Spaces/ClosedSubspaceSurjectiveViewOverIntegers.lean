module

import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# A closed subspace with all the points, viewed over the terminal scheme

Let `W` be an algebraic space over a scheme `S`, and let `Z ⊆ W` be a closed subspace whose
inclusion is surjective on points. Viewing `W` over the terminal scheme `Spec ℤ` (the
relocalization `Λ`), the image of `Λ Z ⟶ Λ W` is a closed subspace of `Λ W`, isomorphic to
`Λ Z`, and its inclusion is still surjective on points. This is what lets the proof of
Stacks 07VU (the thickening case of Stacks 07VT, used for Stacks 049D) be carried out over the
terminal base.

## Main results

* `AlgebraicGeometry.Space.exists_closedSubspace_viewOverIntegers_of_isSurjective`.

## References

* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 049D](https://stacks.math.columbia.edu/tag/049D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed subspace surjective on points, viewed over the terminal scheme.** For a closed
subspace `Z` of an algebraic space `W` over `S` whose inclusion is surjective on points, the
image `Z'` of its view over `Spec ℤ` is a closed subspace of the view of `W`, its inclusion is
surjective on points, and `Z'` is isomorphic to the view of `Z`. -/
theorem exists_closedSubspace_viewOverIntegers_of_isSurjective (W : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS W.1) (hsurj : IsSurjective B S hS Z.1.ι) :
    ∃ Z' : ClosedSubspaces B (⊤_ Scheme.{u}) B.contains_terminal
        (viewOverIntegers B S hS B.contains_terminal W.1),
      IsSurjective B _ B.contains_terminal Z'.1.ι ∧
        Nonempty (Z'.1.toFunctor ≅ viewOverIntegers B S hS B.contains_terminal Z.1.toFunctor) := by
  let hZ := B.contains_terminal
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let Λ := OverShriek.relocalizePresheafFunctor k
  let Z' : ClosedSubspaces B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ W.1) :=
    ⟨Subfunctor.range (Λ.map Z.1.ι),
      isClosedSubspace_range_of_isClosedImmersion B _ hZ _
        (isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) k _ Z.2.1)
        (isClosedImmersion_relocalize B S hS hZ k Z.2.2)⟩
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hpre := presheafSurjective_of_isSurjective B S hS Z.1.ι Z.2.2.rep hsurj
  have hΛ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf (Λ.map Z.1.ι) :=
    OverShriek.presheaf_map_relocalize _ (fun _ hk => hk) hpre
  have hfac : Subfunctor.toRange (Λ.map Z.1.ι) ≫ Z'.1.ι = Λ.map Z.1.ι :=
    Subfunctor.toRange_ι _
  have hι : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf Z'.1.ι := by
    have hiso : IsIso (Subfunctor.toRange (Λ.map Z.1.ι)) := inferInstance
    rw [← hfac] at hΛ
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hΛ
  exact ⟨Z', isSurjective_of_presheafSurjective B _ hZ _ hι,
    ⟨(asIso (Subfunctor.toRange (Λ.map Z.1.ι))).symm⟩⟩

end AlgebraicGeometry.Space

end
