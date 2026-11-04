module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHom
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleIdealTorsion
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedTensorHomMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `EffectiveCartierDerivedSheafHom`

For an effective Cartier divisor `D` on a scheme `X` with closed immersion `i : D ⟶ X`, an
invertible `𝒪_X`-module has no nonzero morphisms in `D(𝒪_X)` from `(i_* G)[0]`, for any
`𝒪_D`-module `G`; in particular `Hom_{D(𝒪_X)}((i_* 𝒩)[0], 𝒪_X(D)[0]) = 0` for the normal sheaf `𝒩`.

## Main results

* `Stacks.Divisors.subsingleton_singleFunctor_hom_pushforward_of_isInvertible`: morphisms
  `(i_* G)[0] ⟶ L[0]` in `D(𝒪_X)` are unique when `L` is invertible.
* `Stacks.Divisors.subsingleton_singleFunctor_normalShortComplex_X₃_hom_divisorSheaf`: morphisms
  `(i_* 𝒩)[0] ⟶ 𝒪_X(D)[0]` in `D(𝒪_X)` are unique.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-! ### Torsion vanishing -/

/-- **An invertible sheaf has no sections supported on `D`, read in the derived category.** For
`G` an arbitrary `𝒪_D`-module and `L` an invertible `𝒪_X`-module, the group
`Hom_{D(𝒪_X)}((i_* G)[0], L[0])` vanishes. -/
theorem subsingleton_singleFunctor_hom_pushforward_of_isInvertible
    (G : D.subscheme.Modules) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((Scheme.Modules.pushforward D.subschemeι).obj G) ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj L) := by
  refine ⟨fun f g => ?_⟩
  obtain ⟨f', rfl⟩ := (DerivedCategory.singleFunctor X.Modules 0).map_surjective f
  obtain ⟨g', rfl⟩ := (DerivedCategory.singleFunctor X.Modules 0).map_surjective g
  rw [hom_pushforward_eq_zero_of_isInvertible D f',
    hom_pushforward_eq_zero_of_isInvertible D g']

/-- **The vanishing `Hom_{D(𝒪_X)}(i_* 𝒩, 𝒪_X(D)) = 0`**, at the third term of the normal short
exact sequence: there is at most one morphism `(i_* 𝒩)[0] ⟶ 𝒪_X(D)[0]` in `D(𝒪_X)`, namely zero.
-/
theorem subsingleton_singleFunctor_normalShortComplex_X₃_hom_divisorSheaf :
    Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj (normalShortComplex D).X₃ ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj (divisorSheaf D)) :=
  subsingleton_singleFunctor_hom_pushforward_of_isInvertible D
    ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) (divisorSheaf D)

end Stacks.Divisors

end
