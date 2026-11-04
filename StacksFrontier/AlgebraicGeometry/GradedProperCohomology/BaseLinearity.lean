module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear

/-!
# A scalar from the base ring acts on cohomology through the sheaf

Let `g : Y ⟶ Spec B` be a scheme over a ring `B`.  The cohomology `H^p(Y, N)` of an
`𝒪_Y`-module is a module over `Γ(Y, ⊤)`, hence over `B` by restriction of scalars along
`specAlgebraRingHom B g`.  This file records that this action is the one induced by the
action of `B` on the *sheaf*: multiplication by `b` on `H^p(Y, N)` is `H^p` of the
endomorphism `b • 𝟙 N` of `N`.

That identity is what makes a comparison of cohomologies `B`-linear whenever the comparison
is natural, and it is the half of the `B`-linearity of [Stacks, Tag 0897]'s
`H^p(X, ℱ) = H^p(X', ℱ')` that lives upstairs on `X'`.

Nothing about derived functors is reproved: the `B`-linearity of `H^p(Y, −)` as a functor is
`Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`, which comes from
`CategoryTheory.Functor.linear_rightDerived` applied to the `B`-linear global sections
functor.  What is added here is the identification of the two ring maps `B →+* Γ(Y, ⊤)`
through which the two sides read the scalar: `AlgebraicGeometry.baseRingToSections` at the
open `⊤`, and `specAlgebraRingHom`.

## Main results

* `Stacks.AlgebraicGeometry.GradedProperCohomology.baseRingToSections_top`: the two ring maps
  `B →+* Γ(Y, ⊤)` agree.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.map_smul_id_cohomologyOf`: a base scalar
  acts on cohomology through the sheaf.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear
  Stacks.Cohomology.AffineBase.baseSectionsAlgebra

/-- The ring map through which the base ring acts on the sections of the structure sheaf is the
one `specAlgebraRingHom` names. -/
theorem baseRingToSections_top (B : Type u) [CommRing B] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of B)) (b : B) :
    AlgebraicGeometry.baseRingToSections B (Over.mk g) (op ⊤) b =
      specAlgebraRingHom B g b := by
  have h : (op (⊤ : Y.Opens)).unop.leTop.op = 𝟙 (op (⊤ : Y.Opens)) := rfl
  show (Y.ringCatSheaf.obj.map (op (⊤ : Y.Opens)).unop.leTop.op).hom _ = _
  rw [h, Y.ringCatSheaf.obj.map_id]
  rfl

/-- **A base scalar acts on cohomology through the sheaf.** -/
theorem map_smul_id_cohomologyOf (B : Type u) [CommRing B] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of B)) (N : Y.Modules) (p : ℕ) (b : B)
    (x : ↥(cohomologyOf Y p N)) :
    letI : Linear B Y.Modules := AlgebraicGeometry.modulesLinear B (Over.mk g)
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections Y).rightDerived p).map
        (b • 𝟙 N)).hom x = specAlgebraRingHom B g b • x := by
  let hlin : Linear B Y.Modules := AlgebraicGeometry.modulesLinear B (Over.mk g)
  let halg : Algebra B Γ(Y, ⊤) :=
    Stacks.Cohomology.AffineBase.baseSectionsAlgebra B (Over.mk g)
  have : Functor.Linear B
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections Y).rightDerived p) :=
    Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections B (Over.mk g) p
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  show (b • 𝟙 (cohomologyOf Y p N)).hom x = _
  show algebraMap B Γ(Y, ⊤) b • x = _
  exact congrArg (fun r : Γ(Y, ⊤) => r • x) (baseRingToSections_top B g b)

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
