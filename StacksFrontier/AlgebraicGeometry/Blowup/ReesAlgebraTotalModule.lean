module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraModule
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The total module of the Rees graded module of an ideal sheaf

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` an ideal sheaf and `ℱ` an `𝒪_X`-module. The Rees algebra
`𝓑 = ⨁ₙ ℐⁿ` (`Stacks.Blowup.reesGradedAlgebra`) is graded-commutative, so the graded `𝓑`-module
`⨁ₙ ℐⁿℱ` (`Stacks.Blowup.reesGradedModule`) has a total module, a sheaf of modules over the
ungraded sheaf of rings `⨁ₙ ℐⁿ`.

## Main definitions

* `Stacks.Blowup.isCommutative_reesGradedAlgebra`: the Rees algebra of an ideal sheaf is
  graded-commutative.
* `Stacks.Blowup.reesUngradedSheaf`: the ungraded sheaf of rings `⨁ₙ ℐⁿ` presented by the Rees
  algebra.
* `Stacks.Blowup.reesTotalModule`: the total module `⨁ₙ ℐⁿℱ` of the Rees graded module, as a sheaf
  of modules over `Stacks.Blowup.reesUngradedSheaf`.
* `Stacks.Blowup.reesTotalIncl`: a section of `ℐⁿℱ`, viewed in the total module.
* `Stacks.Blowup.reesAlgebraSheaf`: the Rees algebra as a sheaf of commutative algebras over
  `𝒪_X`, whose sheaf of rings is `Stacks.Blowup.reesUngradedSheaf`
  (`Stacks.Blowup.ringSheaf_reesAlgebraSheaf`).

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The Rees algebra `⨁ₙ ℐⁿ` of an ideal sheaf is graded-commutative. -/
instance isCommutative_reesGradedAlgebra :
    (reesGradedAlgebra I).IsCommutative :=
  ⟨fun i j U x y => reesMultiplication_comm I i j U x y⟩

/-- The ungraded sheaf of rings presented by the Rees algebra of an ideal sheaf: the
sheafification of `⨁ₙ ℐⁿ`. -/
noncomputable abbrev reesUngradedSheaf := (reesGradedAlgebra I).ungradedSheaf

/-- The total module `⨁ₙ ℐⁿℱ` of the Rees graded module of an ideal sheaf, as a sheaf of
modules over the ungraded sheaf of rings `⨁ₙ ℐⁿ`. -/
noncomputable abbrev reesTotalModule (F : SheafOfModules.{u} X.ringCatSheaf) :
    SheafOfModules.{u} (reesUngradedSheaf I) :=
  (reesGradedModule I F).ungradedSheaf

/-- A local section of `ℐⁿℱ`, viewed in the total module `⨁ₙ ℐⁿℱ`. -/
noncomputable abbrev reesTotalIncl (F : SheafOfModules.{u} X.ringCatSheaf) {U : (Opens X)ᵒᵖ}
    (n : ℤ) (x : ((reesGradedModule I F).piece n).val.obj U) :
    ((reesTotalModule I F).val.obj U : Type u) :=
  (reesGradedModule I F).ungradedIncl n x

/-- The Rees algebra of an ideal sheaf, as a sheaf of commutative algebras over `𝒪_X`. -/
@[sga "2 XII 4.2" "partial"]
noncomputable abbrev reesAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  Stacks.RelativeSpec.gradedAlgebraSheaf X (reesGradedAlgebra I)
    (fun i j W a b => reesMultiplication_comm I i j W a b)

/-- The sheaf of rings of `Stacks.Blowup.reesAlgebraSheaf` is the ungraded realization itself. -/
theorem ringSheaf_reesAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.ringSheaf (reesAlgebraSheaf I) = reesUngradedSheaf I :=
  rfl

end Stacks.Blowup

end
