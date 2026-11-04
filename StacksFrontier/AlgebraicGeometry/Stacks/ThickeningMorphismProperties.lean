module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismAffineIntegral
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismTopologicalProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningUniversallyInjective

/-!
# Morphisms of thickenings of algebraic stacks (Stacks 0CJ9)

Stacks 0CJ9 reads, verbatim:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> (1) `f` is an affine morphism if and only if `f'` is an affine morphism,
> (2) `f` is a surjective morphism if and only if `f'` is a surjective morphism,
> (3) `f` is quasi-compact if and only if `f'` quasi-compact,
> (4) `f` is universally closed if and only if `f'` is universally closed,
> (5) `f` is integral if and only if `f'` is integral,
> (6) `f` is universally injective if and only if `f'` is universally injective,
> (7) `f` is universally open if and only if `f'` is universally open,
> (8) `f` is quasi-DM if and only if `f'` is quasi-DM,
> (9) `f` is DM if and only if `f'` is DM,
> (10) `f` is (quasi-)separated if and only if `f'` is (quasi-)separated,
> (11) `f` is representable if and only if `f'` is representable,
> (12) `f` is representable by algebraic spaces if and only if `f'` is representable by
> algebraic spaces,
> (13) add more here.

Item (13) is a placeholder of the source and states nothing. This file proves item (10) and
assembles all twelve items into one statement,
`AlgebraicGeometry.Stack.thickeningMorphism_inner_iff_outer`.

## Where each item is proved

* (1) `AlgebraicGeometry.Stack.isAffineHom_inner_iff_outer` and (5)
  `AlgebraicGeometry.Stack.isIntegralHom_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismAffineIntegral`);
* (2) `AlgebraicGeometry.Stack.isSurjective_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective`);
* (3) `AlgebraicGeometry.Stack.isQuasiCompactMorphism_inner_iff_outer`, (4)
  `AlgebraicGeometry.Stack.universallyClosed_inner_iff_outer` and (7)
  `AlgebraicGeometry.Stack.universallyOpen_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismTopologicalProperties`);
* (6) `AlgebraicGeometry.Stack.universallyInjective_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningUniversallyInjective`);
* (8) `AlgebraicGeometry.Stack.isQuasiDM_inner_iff_outer`, (9)
  `AlgebraicGeometry.Stack.isDM_inner_iff_outer` and (12)
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford`);
* (10) `AlgebraicGeometry.Stack.isQuasiSeparated_inner_iff_outer` and
  `AlgebraicGeometry.Stack.isSeparated_inner_iff_outer` (this file);
* (11) `AlgebraicGeometry.Stack.isRepresentableMorphism_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningMorphismRepresentable`).

The notions are those of the library: affine is **Stacks 0CHQ**, surjective **Stacks 04ZS**,
quasi-compact **Stacks 050U**, universally closed **Stacks 0513**, integral **Stacks 0CHU**,
universally injective **Stacks 0CI2**, universally open **Stacks 06U2**, quasi-DM, DM,
quasi-separated and separated **Stacks 04YW**, representable **Stacks 02Y7** and representable by
algebraic spaces **Stacks 02ZW**.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- **Stacks 0CJ9, part (10), the quasi-separated half.** In a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the restricted 1-morphism `f` is
quasi-separated (**Stacks 04YW**) if and only if the ambient 1-morphism `f'` is.

As in the source, this is a condition on the relative diagonals, which form a morphism of
thickenings (**Stacks 0BPU**), and it is clauses (d) and (g) of **Stacks 0BPV**:
`AlgebraicGeometry.Stack.isQuasiSeparated_outer_of_inner` and
`AlgebraicGeometry.Stack.isQuasiSeparated_inner_of_outer`. -/
@[stacks 0CJ9 "part (10): quasi-separated"]
theorem isQuasiSeparated_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.IsQuasiSeparated B S hS m.inner ↔
      AlgebraicStacks.IsQuasiSeparated B S hS m.outer :=
  ⟨isQuasiSeparated_outer_of_inner B S hS m, isQuasiSeparated_inner_of_outer B S hS m⟩

/-- **Stacks 0CJ9, part (10), the separated half.** In a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the restricted 1-morphism `f` is
separated (**Stacks 04YW**) if and only if the ambient 1-morphism `f'` is.

Separatedness is properness of the relative diagonal, and this is clause (q) of **Stacks 0BPV**:
`AlgebraicGeometry.Stack.isSeparated_outer_of_inner` and
`AlgebraicGeometry.Stack.isSeparated_inner_of_outer`. -/
@[stacks 0CJ9 "part (10): separated"]
theorem isSeparated_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.IsSeparated B S hS m.inner ↔ AlgebraicStacks.IsSeparated B S hS m.outer :=
  ⟨isSeparated_outer_of_inner B S hS m, isSeparated_inner_of_outer B S hS m⟩

/-- **Stacks 0CJ9.** Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of
algebraic stacks over `S`, `f = m.inner` and `f' = m.outer`. Then
(1) `f` is affine if and only if `f'` is affine,
(2) `f` is surjective if and only if `f'` is surjective,
(3) `f` is quasi-compact if and only if `f'` is quasi-compact,
(4) `f` is universally closed if and only if `f'` is universally closed,
(5) `f` is integral if and only if `f'` is integral,
(6) `f` is universally injective if and only if `f'` is universally injective,
(7) `f` is universally open if and only if `f'` is universally open,
(8) `f` is quasi-DM if and only if `f'` is quasi-DM,
(9) `f` is DM if and only if `f'` is DM,
(10) `f` is quasi-separated if and only if `f'` is quasi-separated, and `f` is separated if and
only if `f'` is separated,
(11) `f` is representable if and only if `f'` is representable,
(12) `f` is representable by algebraic spaces if and only if `f'` is representable by algebraic
spaces.

The conjuncts are, in order, the twelve items of the source; item (13) ("add more here") states
nothing. -/
@[stacks 0CJ9]
theorem thickeningMorphism_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    (AlgebraicStacks.IsAffineHom B S hS m.inner ↔ AlgebraicStacks.IsAffineHom B S hS m.outer) ∧
    (IsSurjective B S hS m.inner ↔ IsSurjective B S hS m.outer) ∧
    (IsQuasiCompactMorphism B S hS m.inner ↔ IsQuasiCompactMorphism B S hS m.outer) ∧
    (AlgebraicStacks.UniversallyClosed B S hS m.inner ↔
      AlgebraicStacks.UniversallyClosed B S hS m.outer) ∧
    (AlgebraicStacks.IsIntegralHom B S hS m.inner ↔
      AlgebraicStacks.IsIntegralHom B S hS m.outer) ∧
    (UniversallyInjective B S hS m.inner ↔ UniversallyInjective B S hS m.outer) ∧
    (AlgebraicStacks.UniversallyOpen B S hS m.inner ↔
      AlgebraicStacks.UniversallyOpen B S hS m.outer) ∧
    (AlgebraicStacks.IsQuasiDM B S hS m.inner ↔ AlgebraicStacks.IsQuasiDM B S hS m.outer) ∧
    (IsDM B S hS m.inner ↔ IsDM B S hS m.outer) ∧
    ((AlgebraicStacks.IsQuasiSeparated B S hS m.inner ↔
        AlgebraicStacks.IsQuasiSeparated B S hS m.outer) ∧
      (AlgebraicStacks.IsSeparated B S hS m.inner ↔
        AlgebraicStacks.IsSeparated B S hS m.outer)) ∧
    (Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor m.inner.hom) ↔
      Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p 𝒴'.val.val.p
        (CatFiberedInGroupoids.homFunctor m.outer.hom)) ∧
    (IsRepresentableByAlgebraicSpaces B S hS m.inner.hom.hom ↔
      IsRepresentableByAlgebraicSpaces B S hS m.outer.hom.hom) :=
  ⟨isAffineHom_inner_iff_outer B S hS m, isSurjective_inner_iff_outer m,
    isQuasiCompactMorphism_inner_iff_outer B S hS m, universallyClosed_inner_iff_outer B S hS m,
    isIntegralHom_inner_iff_outer B S hS m, universallyInjective_inner_iff_outer B S hS m,
    universallyOpen_inner_iff_outer B S hS m, isQuasiDM_inner_iff_outer B S hS m,
    isDM_inner_iff_outer B S hS m,
    ⟨isQuasiSeparated_inner_iff_outer B S hS m, isSeparated_inner_iff_outer B S hS m⟩,
    isRepresentableMorphism_inner_iff_outer B S hS m,
    isRepresentableByAlgebraicSpaces_inner_iff_outer B S hS m⟩

end AlgebraicGeometry.Stack

end
