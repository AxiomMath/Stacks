module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeEssentiallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# Finite type quasi-coherent modules on a ringed space form a set up to isomorphism

For a ringed space, the sheaves of modules of finite type over its structure sheaf have only a
set of isomorphism classes, and therefore so do the quasi-coherent ones among them. This is
what makes the fibre categories of the stack of finitely generated quasi-coherent sheaves
small, as required of a stack in groupoids over the big fppf site.

## Main results

* `Stacks.SheafOfModules.essentiallySmall_isFiniteType_and_isQuasicoherent`: the finite type
  quasi-coherent sheaves of modules on a ringed space form an essentially small class.

## Implementation notes

The existence of a set of representatives of the isomorphism classes is expressed as essential
smallness of the corresponding object property, as in
`Stacks.SheafOfModules.essentiallySmall_isFiniteType` (Stacks 01BC), of which the finite type
half of this statement is a restatement; the quasi-coherent half follows by restricting that
class. The structure sheaf is regarded as a sheaf of not-necessarily-commutative rings by
applying `forget₂ CommRingCat RingCat`.

## References

* [Stacks Project, Tag 04U5](https://stacks.math.columbia.edu/tag/04U5)
* [Stacks Project, Tag 01BC](https://stacks.math.columbia.edu/tag/01BC)
-/

add_to_stacks 04U5 "finite_type_modules"
  Stacks.SheafOfModules.essentiallySmall_isFiniteType

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- The finite type quasi-coherent sheaves of modules on a ringed space have only a set
of isomorphism classes. -/
@[stacks 04U5 "finite_type_quasi_coherent_modules"]
theorem essentiallySmall_isFiniteType_and_isQuasicoherent (X : RingedSpace.{u, u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat)).obj X.sheaf) ↦
        SheafOfModules.IsFiniteType M ∧ SheafOfModules.IsQuasicoherent M) :=
  (essentiallySmall_isFiniteType X).of_le (fun _ h ↦ h.1)

end Stacks.SheafOfModules

end
