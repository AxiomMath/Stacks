module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology

/-!
# Recognising the unit of derived completion by a map to a derived complete object

Let `φ : X ⟶ Y` be a morphism in `D(A)` whose target is derived `I`-complete and which derived
completion inverts. Then `φ` is, up to isomorphisms at both ends, the unit `X ⟶ X^∧` of derived
completion: by naturality `φ ≫ (Y ⟶ Y^∧) = (X ⟶ X^∧) ≫ φ^∧`, the unit at `Y` is invertible
because `Y` is complete, and `φ^∧` is invertible by hypothesis. So any functor inverts the unit
at `X` exactly when it inverts `φ`; in particular the two have the same effect on cohomology in
every degree.

This is how the proof of Stacks 0EIF reads the conclusion of Stacks 0EFL, which concerns the
unit at `RΓ_J(M)`, off an explicit model of the completion, namely the termwise completion of a
Čech complex.

## Main results

* `Stacks.Algebraization.isIso_map_adicCompletionUnit_app_iff`: for any functor `G` out of
  `D(A)`, `G` inverts the unit at `X` if and only if it inverts `φ`.
* `Stacks.Algebraization.isIso_homologyMap_adicCompletionUnit_app_iff`: the same for the
  cohomology functors.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **A functor inverts the unit of derived completion at `X` exactly when it inverts `φ`**, for
a morphism `φ : X ⟶ Y` of `D(A)` whose target is derived `I`-complete and which derived
completion inverts. -/
theorem isIso_map_adicCompletionUnit_app_iff {E : Type*} [Category* E]
    (G : DerivedCategory (ModuleCat.{u} A) ⥤ E) {X Y : DerivedCategory (ModuleCat.{u} A)}
    (φ : X ⟶ Y) (hY : IsDerivedComplete I Y) [IsIso ((adicCompletionFunctor A I hI).map φ)] :
    IsIso (G.map ((adicCompletionUnit A I hI).app X)) ↔ IsIso (G.map φ) := by
  have := isIso_completionUnit_of_derivedComplete I hI Y hY
  have h : (adicCompletionUnit A I hI).app X =
      φ ≫ (adicCompletionUnit A I hI).app Y ≫ inv ((adicCompletionFunctor A I hI).map φ) := by
    have hn : φ ≫ (adicCompletionUnit A I hI).app Y =
        (adicCompletionUnit A I hI).app X ≫ (adicCompletionFunctor A I hI).map φ :=
      (adicCompletionUnit A I hI).naturality φ
    rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h, G.map_comp]
  exact isIso_comp_right_iff _ _

/-- **Derived completion and `φ` have the same effect on cohomology.** For a morphism
`φ : X ⟶ Y` of `D(A)` whose target is derived `I`-complete and which derived completion
inverts, the unit `X ⟶ X^∧` induces an isomorphism on `Hⁱ` exactly when `φ` does. -/
theorem isIso_homologyMap_adicCompletionUnit_app_iff {X Y : DerivedCategory (ModuleCat.{u} A)}
    (φ : X ⟶ Y) (hY : IsDerivedComplete I Y) [IsIso ((adicCompletionFunctor A I hI).map φ)]
    (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((adicCompletionUnit A I hI).app X)) ↔
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ) :=
  isIso_map_adicCompletionUnit_app_iff I hI _ φ hY

end Stacks.Algebraization

end
