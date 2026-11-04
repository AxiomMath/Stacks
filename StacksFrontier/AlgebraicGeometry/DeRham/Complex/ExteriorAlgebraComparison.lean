module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences

/-!
# Comparing the exterior algebras of isomorphic sheaves of modules

`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceIso` compares two exterior algebras of
*one* sheaf of modules. This file compares the exterior algebras of two *isomorphic* sheaves of
modules: an isomorphism `c : M ≅ N` makes an exterior algebra of `N` into an exterior algebra of
`M`, by precomposing its generator with `c`, and the resulting comparison is an isomorphism in
every degree.

This is the degreewise invertibility statement used for sheaves of relative differential forms:
once the canonical map on relative differentials is known to be an isomorphism, every exterior
power of it is.

## Main definitions

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceIsoOfIso` is the degreewise comparison
  of the exterior algebras of two isomorphic sheaves of modules.

## Main results

* `SheafOfModules.GradedAlgebra.SquareZero.comp`: precomposing a square-zero degree-one
  generator with any morphism of sheaves of modules leaves it square-zero.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app`: the comparison
  homomorphism out of an exterior algebra of `M` into one of `N` extending an isomorphism
  `M ⟶ N` is an isomorphism in every degree.

## Implementation notes

The transport of the unique-extension statement itself is
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`, which this file
imports; nothing is constructed there either. `isIso_desc_app` is then `pieceIso` applied to it,
so the inverse it produces is the comparison homomorphism in the other direction, not an ad hoc
map.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory

universe t a v₁ u₁

namespace SheafOfModules.GradedAlgebra

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{a} R} {A B : GradedAlgebra.{t, a} R}

/-- Precomposing a square-zero degree-one generator with a morphism of sheaves of modules
leaves it square-zero. -/
theorem SquareZero.comp {κ : N ⟶ B.piece 1} (hκ : SquareZero κ) (c : M ⟶ N) :
    SquareZero (c ≫ κ) := by
  intro U s
  change (B.mul 1 1).app U (κ.val.app U (c.val.app U s)) (κ.val.app U (c.val.app U s)) = 0
  exact hκ U (c.val.app U s)

/-- The exterior algebras of two isomorphic sheaves of modules are isomorphic in every degree,
by the comparison homomorphism determined by the generators and the isomorphism. -/
noncomputable def IsExteriorAlgebra.pieceIsoOfIso {ι : M ⟶ A.piece 1} {κ : N ⟶ B.piece 1}
    (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (c : M ⟶ N) (hc : IsIso c)
    (n : ℤ) : A.piece n ≅ B.piece n :=
  hA.pieceIso (hB.comp_iso c hc) n

/-- The comparison homomorphism out of an exterior algebra of `M` into one of `N` extending an
isomorphism `M ⟶ N` is an isomorphism in every degree. -/
theorem IsExteriorAlgebra.isIso_desc_app {ι : M ⟶ A.piece 1} {κ : N ⟶ B.piece 1}
    (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (c : M ⟶ N) (hc : IsIso c)
    (hκ : SquareZero (c ≫ κ)) (n : ℤ) : IsIso ((hA.desc B (c ≫ κ) hκ).app n) :=
  (hA.pieceIsoOfIso hB c hc n).isIso_hom

end SheafOfModules.GradedAlgebra
