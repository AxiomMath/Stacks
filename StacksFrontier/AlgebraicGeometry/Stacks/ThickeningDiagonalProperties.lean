module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalClauses
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalPointTest
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse

/-!
# The relative diagonals of a morphism of thickenings of algebraic stacks (Stacks 0BPV)

Stacks 0BPV reads, verbatim:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Let
> `Δ : 𝒳 → 𝒳 ×_𝒴 𝒳` and `Δ' : 𝒳' → 𝒳' ×_{𝒴'} 𝒳'` be the corresponding diagonal morphisms.
> Then each property from the following list is satisfied by `Δ` if and only if it is satisfied
> by `Δ'`: (a) representable by schemes, (b) affine, (c) surjective, (d) quasi-compact,
> (e) universally closed, (f) integral, (g) quasi-separated, (h) separated, (i) universally
> injective, (j) universally open, (k) locally quasi-finite, (l) finite, (m) unramified,
> (n) monomorphism, (o) immersion, (p) closed immersion, and (q) proper.

This file assembles the seventeen equivalences into one statement,
`AlgebraicGeometry.Stack.thickeningMorphism_relativeDiagonal_inner_iff_outer`.

## Where each property is proved

Every property is proved for an arbitrary morphism of thickenings and assumes nothing beyond it;
the comparison `𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` being a thickening is the first assertion of
**Stacks 0BPU**, `AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`, and the diagonal
square being cartesian its second assertion,
`AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductDiagonalSquare`.

* (a) `AlgebraicGeometry.Stack.isRepresentableMorphism_relativeDiagonal_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalRepresentable`);
* (b) `AlgebraicGeometry.Stack.isAffineHom_relativeDiagonal_inner_iff_outer` and (f)
  `AlgebraicGeometry.Stack.isIntegralHom_relativeDiagonal_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalAffine`);
* (c) `AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_inner_iff_outer` and (i)
  `AlgebraicGeometry.Stack.universallyInjective_relativeDiagonal_inner_iff_outer`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalClauses`);
* (d) `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff`, (e)
  `AlgebraicGeometry.Stack.universallyClosed_relativeDiagonal_iff`, (g)
  `AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_iff`, (h)
  `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_iff`, (j)
  `AlgebraicGeometry.Stack.universallyOpen_relativeDiagonal_iff` and (q)
  `AlgebraicGeometry.Stack.isProper_relativeDiagonal_iff`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`);
* (k) `AlgebraicGeometry.Stack.isLocallyQuasiFinite_relativeDiagonal_iff`, (l)
  `AlgebraicGeometry.Stack.isFinite_relativeDiagonal_iff`, (m)
  `AlgebraicGeometry.Stack.unramified_relativeDiagonal_iff`, (n)
  `AlgebraicGeometry.Stack.mono_relativeDiagonal_iff`, (o)
  `AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_iff` and (p)
  `AlgebraicGeometry.Stack.isClosedImmersion_relativeDiagonal_iff`
  (`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalPointTest`).

The relative diagonal of a 1-morphism of algebraic stacks is representable by algebraic spaces
(**Stacks 04XS**), so each of (b)–(q) is the condition of Properties of Stacks, Section 04XB, at
the corresponding property of morphisms of algebraic spaces; (a) is representability by schemes
(**Stacks 02Y7**), (c) surjectivity (**Stacks 04ZS**) and (i) universal injectivity
(**Stacks 0CI2**).

## References

* [Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- **Stacks 0BPV.** Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of
algebraic stacks over `S`, `f = m.inner` and `f' = m.outer`, and let `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` and
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` be the relative diagonals. Then `Δ` has each of the following
properties if and only if `Δ'` has it:
(a) representable by schemes, (b) affine, (c) surjective, (d) quasi-compact,
(e) universally closed, (f) integral, (g) quasi-separated, (h) separated,
(i) universally injective, (j) universally open, (k) locally quasi-finite, (l) finite,
(m) unramified, (n) monomorphism, (o) immersion, (p) closed immersion, (q) proper.

The conjuncts are, in order, the seventeen properties of the source; (b) and (d)–(q) are the
conditions of Properties of Stacks, Section 04XB, at the corresponding properties of morphisms of
algebraic spaces. -/
@[stacks 0BPV]
theorem thickeningMorphism_relativeDiagonal_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    -- (a) representable by schemes
    (Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p
        (AlgebraicStacks.twoFibreProduct B S hS m.inner m.inner).val.val.p
        (CatFiberedInGroupoids.homFunctor
          (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom) ↔
      Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p
        (AlgebraicStacks.twoFibreProduct B S hS m.outer m.outer).val.val.p
        (CatFiberedInGroupoids.homFunctor
          (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom)) ∧
    -- (b) affine
    (Stack.IsAffineHom B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsAffineHom B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (c) surjective
    (IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner) ↔
      IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer)) ∧
    -- (d) quasi-compact
    (Stack.IsQuasiCompact B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsQuasiCompact B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (e) universally closed
    (Stack.UniversallyClosed B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.UniversallyClosed B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (f) integral
    (HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)) ∧
    -- (g) quasi-separated
    (Stack.IsQuasiSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsQuasiSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (h) separated
    (Stack.IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsSeparated B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (i) universally injective
    (UniversallyInjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner) ↔
      UniversallyInjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer)) ∧
    -- (j) universally open
    (HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.universallyOpenMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.universallyOpenMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)) ∧
    -- (k) locally quasi-finite
    (Stack.IsLocallyQuasiFinite B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsLocallyQuasiFinite B S hS
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (l) finite
    (HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.finiteMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.finiteMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)) ∧
    -- (m) unramified
    (haveI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
      Space.isUnramified_isStableUnderBaseChange B S hS
    haveI : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
      (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)) ∧
    -- (n) monomorphism
    (HasRelativeProperty.{u, u, u + 1, u} B S hS
        (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)) ∧
    -- (o) immersion
    (Stack.IsImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (p) closed immersion
    (Stack.IsClosedImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsClosedImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) ∧
    -- (q) proper
    (Stack.IsProper B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsProper B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) :=
  ⟨isRepresentableMorphism_relativeDiagonal_inner_iff_outer B S hS m,
    isAffineHom_relativeDiagonal_inner_iff_outer B S hS m,
    isSurjective_relativeDiagonal_inner_iff_outer B S hS m,
    isQuasiCompact_relativeDiagonal_iff B S hS m,
    universallyClosed_relativeDiagonal_iff B S hS m,
    isIntegralHom_relativeDiagonal_inner_iff_outer B S hS m,
    isQuasiSeparated_relativeDiagonal_iff B S hS m,
    isSeparated_relativeDiagonal_iff B S hS m,
    universallyInjective_relativeDiagonal_inner_iff_outer B S hS m,
    universallyOpen_relativeDiagonal_iff B S hS m,
    isLocallyQuasiFinite_relativeDiagonal_iff B S hS m,
    isFinite_relativeDiagonal_iff B S hS m,
    unramified_relativeDiagonal_iff B S hS m,
    mono_relativeDiagonal_iff B S hS m,
    isImmersion_relativeDiagonal_iff B S hS m,
    isClosedImmersion_relativeDiagonal_iff B S hS m,
    isProper_relativeDiagonal_iff B S hS m⟩

end AlgebraicGeometry.Stack

end
