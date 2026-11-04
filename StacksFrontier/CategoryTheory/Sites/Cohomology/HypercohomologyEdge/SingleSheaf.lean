module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
import StacksCore.Tactic.StacksAttribute

/-! # The hypercohomology edge morphism at a sheaf in a single degree

Let `(C, O)` be a ringed site, `U` an object of `C`, `M` a sheaf of `O`-modules and `a` an
integer. The edge morphism

`H^a(U, M[a]) ⟶ Γ(U, H^a(M[a])) = Γ(U, M)`

of `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge` is an isomorphism, for every `U`
and with no hypothesis on `M`. This is the degenerate case `H^0(U, M) = Γ(U, M)` of Tag 0BKZ, and
it is the base case of the induction that proves the bounded-below case of that tag.

No acyclicity of `M` is needed, and that is the point: the edge in the *same* degree as the sheaf
sits is always invertible, whereas invertibility in the other degrees is exactly the vanishing of
the higher cohomology `H^p(U, M)` for `p > 0`.

The proof uses the reduction
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_iff`: the edge is invertible
exactly when the unit of sheafification is invertible on the degree-`a` cohomology presheaf of
`M[a]`. That presheaf is `R⁰` of the forgetful functor from sheaves to presheaves of modules
applied to `M`, which, the forgetful functor being left exact, is the underlying presheaf of `M`
itself -- already a sheaf. The unit of sheafification is invertible on the underlying presheaf of
a sheaf, because the right adjoint of sheafification is fully faithful, so its counit is
invertible and the triangle identity forces the unit to be invertible there.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.isIso_unit_app_of_iso_rightAdjoint_obj`: the unit of an
  adjunction with invertible counit is invertible at any object isomorphic to one in the image of
  the right adjoint.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_single`: the edge morphism
  at a sheaf placed in its own degree is an isomorphism.

## Implementation notes

The right adjoint of `PresheafOfModules.sheafification (𝟙 O.obj)` is
`SheafOfModules.forget O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)`, whose second factor is
definitionally the identity on objects, so the isomorphism produced by
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso` -- which is stated for
`SheafOfModules.forget O` alone -- lands at the right object with no transport.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

section Adjunction

variable {P : Type*} [Category* P] {A : Type*} [Category* A] {L : P ⥤ A} {R : A ⥤ P}

/-- If the counit of an adjunction is invertible, then its unit is invertible at every object in
the image of the right adjoint: the triangle identity exhibits it as a factor of an identity
whose other factor is invertible. -/
lemma isIso_unit_app_rightAdjoint_obj (adj : L ⊣ R) [IsIso adj.counit] (X : A) :
    IsIso (adj.unit.app (R.obj X)) := by
  have := adj.fullyFaithfulROfIsIsoCounit.full
  have := adj.fullyFaithfulROfIsIsoCounit.faithful
  exact adj.isIso_unit_app_of_iso (Iso.refl _)

/-- The unit of an adjunction with invertible counit is invertible at every object isomorphic to
one in the image of the right adjoint. -/
lemma isIso_unit_app_of_iso_rightAdjoint_obj (adj : L ⊣ R) [IsIso adj.counit] {Q : P} (X : A)
    (e : Q ≅ R.obj X) : IsIso (adj.unit.app Q) := by
  have := adj.fullyFaithfulROfIsIsoCounit.full
  have := adj.fullyFaithfulROfIsIsoCounit.faithful
  exact adj.isIso_unit_app_of_iso e

end Adjunction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
  [EnoughInjectives (SheafOfModules.{wModule} O)]

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
  [EnoughInjectives (SheafOfModules.{wModule} O)] in
/-- The counit of the sheafification adjunction for presheaves of `O`-modules is invertible,
because its right adjoint is fully faithful. -/
lemma isIso_sheafificationAdjunction_counit :
    IsIso (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj) :
        PresheafOfModules.sheafification.{wModule} (𝟙 O.obj) ⊣ _).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  exact Adjunction.instIsIsoAppCounitOfFullOfFaithful _ G

/-- The degree-`a` cohomology presheaf of a sheaf of `O`-modules placed in degree `a` is the
underlying presheaf of that sheaf: the forgetful functor is left exact, so its zeroth right
derived functor is itself. -/
def cohomologyPresheafSingleIso (M : SheafOfModules.{wModule} O) (a : ℤ) :
    (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) a).obj
        ((derivedSectionsPresheaf O).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} O) a).obj M)) ≅
      (SheafOfModules.forget O).obj M :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso (SheafOfModules.forget O)
    (derivedSectionsPresheaf O)
    ((homotopySectionsPresheaf O).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    Stacks.Cohomology.Localization.enoughKInjectives M a

/-- **The degenerate case of Tag 0BKZ.** The hypercohomology edge morphism at a sheaf of
`O`-modules placed in degree `a` is an isomorphism in degree `a`, over every object of the site
and with no hypothesis on the sheaf. -/
theorem isIso_hypercohomologyEdge_app_single (U : C) (M : SheafOfModules.{wModule} O) (a : ℤ) :
    IsIso ((hypercohomologyEdge O U a).app
      ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} O) a).obj M)) := by
  have := isIso_sheafificationAdjunction_counit O
  have hunit : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) a).obj
        ((derivedSectionsPresheaf O).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} O) a).obj M)))) :=
    isIso_unit_app_of_iso_rightAdjoint_obj _ M (cohomologyPresheafSingleIso O M a)
  rw [isIso_hypercohomologyEdge_app_iff, cohomologyPresheafUnit_app]
  exact Functor.map_isIso _ _

end Stacks.Cohomology.HypercohomologyEdge

end
