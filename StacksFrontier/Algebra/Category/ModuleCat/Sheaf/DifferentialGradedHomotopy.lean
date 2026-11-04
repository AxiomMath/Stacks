module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Homotopies between morphisms of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A homotopy between two morphisms `f, g : M ⟶ N` of right differential graded
`A`-modules is a map of graded `A`-modules of degree `-1` whose commutator with the
differentials is `f - g`. Two morphisms are homotopic when such a map exists.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Homotopy` is a degree `-1` graded-module map
  satisfying the homotopy equation.
* `SheafOfModules.DifferentialGradedModule.Homotopic` is the relation of admitting a homotopy.

## Implementation notes

The defining equations are the fields of `Homotopy`, so there are no separate results.

The components are morphisms of sheaves of modules, hence automatically additive, linear over
the sheaf of rings and natural under restriction; only compatibility with the action of `A` has
to be imposed, and it is an equality of homogeneous sections in the propositionally — but not
definitionally — equal degrees `(n + m) - 1` and `(n - 1) + m`, so it is stated with `HEq`. In
the homotopy equation the transport `eqToHom` identifies `(n + 1) - 1` with `n`.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module
pieces are independent, matching the differential graded modules of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean`; a ringed site `X` is
the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- A homotopy between two morphisms of right differential graded modules: a map of graded
modules of degree `-1` whose commutator with the differentials is the difference of the two
morphisms. -/
@[stacks 0FS0 "homotopies"]
structure Homotopy {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) where
  /-- The component in degree `n`, of degree `-1`. -/
  app (n : ℤ) : M.complex.X n ⟶ N.complex.X (n - 1)
  /-- The homotopy is a map of graded right modules. -/
  map_mul (n m : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U)
      (a : (A.complex.X m).val.obj U) :
    HEq ((app (n + m)).val.app U ((M.mul n m).app U x a))
      ((N.mul (n - 1) m).app U ((app n).val.app U x) a)
  /-- The difference of the two morphisms is `d ∘ h + h ∘ d`. -/
  comm (n : ℤ) : f.toHomologicalComplex.f n - g.toHomologicalComplex.f n =
    (app n ≫ N.complex.d (n - 1) n) + ((M.complex.d n (n + 1) ≫ app (n + 1)) ≫
      eqToHom (congrArg N.complex.X (show (n + 1) - 1 = n by omega)))

/-- Two morphisms of right differential graded modules are homotopic if there is a homotopy
between them. -/
@[stacks 0FS0 "homotopic morphisms"]
abbrev Homotopic {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) : Prop :=
  Nonempty (Homotopy f g)

end DifferentialGradedModule

end SheafOfModules
