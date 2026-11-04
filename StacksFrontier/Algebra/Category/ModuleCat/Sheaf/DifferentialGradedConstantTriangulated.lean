module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRealization
public import Mathlib.CategoryTheory.Localization.Linear

/-!
# The derived category of a sheaf of differential graded algebras over a constant ring

Let `C` be a category in one universe with `R : Type u` a commutative ring, and let `(A, d)` be
a sheaf of differential graded algebras over the constant sheaf of rings with value `R` on `C`
with the chaotic topology, the setting of Section 24.35. The triangulated structures of Tags 0FS7
and 0FT4 on `K(Mod(A, d))` and `D(A, d)` are stated for a ringed site; the constant sheaf of
rings is, on the nose, the sheaf of rings of the ringed site `Stacks.ChaoticSite.constRingedSite`,
and this file states those structures for `A` itself. It then puts on `D(A, d)` the `R`-linear
structure induced from `K(Mod(A, d))`, for which the localization functor is `R`-linear; full
subcategories such as `QC(A, d)` inherit it.

## Main definitions

* `Stacks.ChaoticSite.constRingedSite`: the chaotic site `C` with the constant sheaf of
  commutative rings with value `R`.
* The instances `HasShift`, `Pretriangulated`, `IsTriangulated` on the homotopy category and the
  calculus-of-fractions instances on the quasi-isomorphisms, for `A` over the constant sheaf.
* `SheafOfModules.DifferentialGradedModule.derivedCategoryLinear`: the `R`-linear structure on
  `D(A, d)`.

## References

* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.ChaoticSite

/-- The chaotic site `C` with the constant sheaf of commutative rings with value `R`, as a ringed
site. Its sheaf of rings is `Stacks.PresheafOfModules.constRingSheaf R` on the nose. -/
def constRingedSite (C : Type u) [Category.{u} C] (R : Type u) [CommRing R] :
    AlgebraicGeometry.RingedSite.{u, u, u} :=
  ⟨C, ⊥, Stacks.PresheafOfModules.constCommRingSheaf (C := C) R⟩

/-- The sheaf of rings of `constRingedSite C R` is the constant sheaf of rings with value `R`. -/
theorem constRingedSite_ringSheaf (C : Type u) [Category.{u} C] (R : Type u) [CommRing R] :
    (Stacks.SheafOfModules.Tensor.ringSheaf (constRingedSite C R).O) =
      Stacks.PresheafOfModules.constRingSheaf (C := C) R :=
  rfl

end Stacks.ChaoticSite

namespace SheafOfModules.DifferentialGradedModule

open Stacks.ChaoticSite

variable {C : Type u} [Category.{u} C] {R : Type u} [CommRing R]
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.PresheafOfModules.constRingSheaf (C := C) R))

namespace HomotopyCategory

/-- The translation functors of `K(Mod(A, d))` (Tag 0FS7), over the constant sheaf of rings. -/
@[instance_reducible]
noncomputable instance constHasShift : HasShift (HomotopyCategory.{u, u, u} A) ℤ :=
  instHasShift (X := constRingedSite C R) A

/-- The translation functors of `K(Mod(A, d))` are additive, over the constant sheaf of rings. -/
instance constShiftFunctor_additive (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{u, u, u} A) n).Additive :=
  shiftFunctor_additive (X := constRingedSite C R) A n

/-- `K(Mod(A, d))` is pretriangulated (Tag 0FS7), over the constant sheaf of rings. -/
@[instance_reducible]
noncomputable instance constPretriangulated : Pretriangulated (HomotopyCategory.{u, u, u} A) :=
  instPretriangulated (X := constRingedSite C R) A

/-- `K(Mod(A, d))` is triangulated (Tag 0FS7), over the constant sheaf of rings. -/
instance constIsTriangulated : IsTriangulated (HomotopyCategory.{u, u, u} A) :=
  instIsTriangulated (X := constRingedSite C R) A

end HomotopyCategory

/-- The quasi-isomorphisms of `K(Mod(A, d))` are closed under composition and contain the
identities, over the constant sheaf of rings. -/
instance const_quasiIsomorphisms_isMultiplicative :
    (quasiIsomorphisms.{u, u, u} A).IsMultiplicative :=
  quasiIsomorphisms_isMultiplicative' (X := constRingedSite C R) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` admit a left calculus of fractions, over the
constant sheaf of rings. -/
instance const_quasiIsomorphisms_hasLeftCalculusOfFractions :
    (quasiIsomorphisms.{u, u, u} A).HasLeftCalculusOfFractions :=
  quasiIsomorphisms_hasLeftCalculusOfFractions (X := constRingedSite C R) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` admit a right calculus of fractions, over the
constant sheaf of rings. -/
instance const_quasiIsomorphisms_hasRightCalculusOfFractions :
    (quasiIsomorphisms.{u, u, u} A).HasRightCalculusOfFractions :=
  quasiIsomorphisms_hasRightCalculusOfFractions (X := constRingedSite C R) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` are compatible with the triangulation, over the
constant sheaf of rings. -/
instance const_quasiIsomorphisms_isCompatibleWithTriangulation :
    (quasiIsomorphisms.{u, u, u} A).IsCompatibleWithTriangulation :=
  quasiIsomorphisms_isCompatibleWithTriangulation (X := constRingedSite C R) A

/-- **The `R`-linear structure on `D(A, d)`**, induced from `K(Mod(A, d))` along the localization
functor. -/
@[instance_reducible]
noncomputable instance derivedCategoryLinear : Linear R (derivedCategory.{u, u, u} A) :=
  Localization.linear R (toDerivedCategory.{u, u, u} A) (quasiIsomorphisms.{u, u, u} A)

/-- The localization functor `K(Mod(A, d)) ⥤ D(A, d)` is `R`-linear. -/
instance toDerivedCategory_linear : Functor.Linear R (toDerivedCategory.{u, u, u} A) :=
  Localization.functor_linear R (toDerivedCategory.{u, u, u} A) (quasiIsomorphisms.{u, u, u} A)

end SheafOfModules.DifferentialGradedModule
