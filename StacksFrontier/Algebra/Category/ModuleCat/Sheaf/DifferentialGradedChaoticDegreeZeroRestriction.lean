module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestriction

/-!
# Restricting an algebra concentrated in degree zero

The restriction `A|_{C'}` of a sheaf of differential graded algebras along a functor of chaotic
sites `F : C' ⥤ C` is concentrated in degree zero when `A` is, with the restricted presheaf of
rings `F⁻¹O`: its sections over `U'` are those of `A` over `F U'`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.DegreeZero.Data.restrict`: the identification of
  `A.restrict F` with `F.op ⋙ O` placed in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory

universe a v u v' u'

namespace SheafOfModules.DifferentialGradedModule.DegreeZero

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{a}}
  {A : SheafOfModules.DifferentialGradedAlgebra.{a, a}
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {O : Cᵒᵖ ⥤ RingCat.{a}}

/-- **The restriction of an algebra concentrated in degree zero is concentrated in degree zero**,
with the restricted presheaf of rings. -/
def Data.restrict (D : Data A O) : Data (A.restrict F) (F.op ⋙ O) where
  ψ U' := D.ψ (F.op.obj U')
  ψ_mul _ x y := D.ψ_mul _ x y
  ψ_one _ := D.ψ_one _
  ψ_map f x := D.ψ_map (F.op.map f) x
  subsingleton n hn _ := D.subsingleton n hn _
  comm _ := D.comm _

end SheafOfModules.DifferentialGradedModule.DegreeZero

end
