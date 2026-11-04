module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningDevissage.GradedIdealKernel
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The graded unit along a closed immersion is surjective in every degree

Let `v : V ⟶ X` be a closed immersion of schemes and `A` a sheaf of graded `𝒪_X`-algebras.  The
degree-`n` component of the graded unit `A ⟶ v_* v^* A` is an epimorphism of sheaves of modules,
hence locally surjective, **with no hypothesis on the piece at all**.

This is exactness on the right of the graded sequence
`0 → ⨁_m ℐ · A_m → ⨁_m A_m → ⨁_m v_* v^* A_m → 0`
of [Stacks, Tag 09MS], degree by degree, and it is unconditional.  Two module docstrings in this
directory previously recorded that exactness on the right was "available only under global
generation of the piece", namely through
`Stacks.PushforwardGradedAlgebra.epi_gradedUnit_app_of_generatingSections`, whose hypothesis is a
`CategoryTheory.SheafOfModules.GeneratingSections` on the piece.  That route exists but is not
the only one, and for a closed immersion it is not needed: the target `v_* v^* A_n` is a direct
image, so it is annihilated by the ideal of the closed subscheme, and so is the image of the
unit; `Stacks.ClosedImmersion.epi_unit_app` turns that into a split epimorphism onto the image
and concludes, for an arbitrary module, from [Stacks, Tag 08KS].

So the ampleness of `L` is not what makes the right-hand end of the graded extension exact, and
the surjection of the extension does not have to be restricted to high degrees.

## Main results

* `Stacks.AmpleThickeningDevissage.epi_gradedUnit_app_of_isClosedImmersion`: **the degree-`n`
  component of `A ⟶ v_* v^* A` is an epimorphism**, for a closed immersion, with no hypothesis on
  `A` or `n`.
* `Stacks.AmpleThickeningDevissage.isLocallySurjective_gradedUnit_app_of_isClosedImmersion`: the
  same read as local surjectivity of the underlying morphism of presheaves of abelian groups,
  which is the form the ungraded realization consumes.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.AmpleThickeningDevissage

variable {V X : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v]
  (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (n : ℤ)

/-- **The degree-`n` component of the graded unit `A ⟶ v_* v^* A` along a closed immersion is an
epimorphism**, with no hypothesis on the sheaf of graded algebras and none on the degree.

The component is the module-level unit at `A_n`
(`Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction_unit_app_app`), the
two adjunctions it can be read in are the same adjunction
(`Stacks.AmpleThickeningDevissage.schemeAdjunction_eq_ringedSpaceAdjunction`), and the unit along
a closed immersion is an epimorphism at every module by
`Stacks.ClosedImmersion.epi_unit_app`. -/
theorem epi_gradedUnit_app_of_isClosedImmersion :
    Epi ((Stacks.PushforwardGradedAlgebra.gradedUnit v.toLRSHom.toShHom A).app n) := by
  rw [Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction_unit_app_app
    v.toLRSHom.toShHom A n, ← schemeAdjunction_eq_ringedSpaceAdjunction v]
  exact Stacks.ClosedImmersion.epi_unit_app v (A.piece n)

/-- **The degree-`n` component of the graded unit along a closed immersion is locally
surjective** on the underlying presheaves of abelian groups.  This is the form in which the
ungraded realization of the graded unit consumes it, and like the epimorphism it carries no
hypothesis on the piece. -/
theorem isLocallySurjective_gradedUnit_app_of_isClosedImmersion :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((Stacks.PushforwardGradedAlgebra.gradedUnit v.toLRSHom.toShHom A).app n).val) :=
  have := epi_gradedUnit_app_of_isClosedImmersion v A n
  Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
    ((Stacks.PushforwardGradedAlgebra.gradedUnit v.toLRSHom.toShHom A).app n)

end Stacks.AmpleThickeningDevissage

end
