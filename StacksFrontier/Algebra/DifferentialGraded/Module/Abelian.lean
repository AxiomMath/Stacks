module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# The abelian structure on differential graded modules

The category `Mod_{(A,d)}` of right differential graded modules over a differential graded
algebra is abelian. This file equips it with an abelian structure, as an instance, whose
underlying preadditive structure is `DifferentialGradedModule.instPreadditive`.

## Main definitions

* `DifferentialGradedModule.instAbelian`: the abelian structure on `Mod_{(A,d)}`.

## References

* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- The abelian structure on the category of right differential graded modules, with underlying
preadditive structure `DifferentialGradedModule.instPreadditive`. -/
@[instance_reducible]
noncomputable instance instAbelian (A : DifferentialGradedAlgebra.{u, v} R) :
    Abelian (DifferentialGradedModule.{u, v, w} A) :=
  letI : HasFiniteProducts (DifferentialGradedModule.{u, v, w} A) :=
    hasFiniteProducts_of_hasProducts.{w} _
  Abelian.mk

end DifferentialGradedModule
