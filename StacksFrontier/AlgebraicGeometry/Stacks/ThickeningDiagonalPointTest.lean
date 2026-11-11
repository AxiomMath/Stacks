module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.ProperFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UnramifiedPointTest
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford

/-!
# The clauses of Stacks 0BPV that go through the point test of Stacks 0BPJ

**Stacks 0BPV** asserts, for a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks and each of seventeen properties, that the
property holds for the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` exactly when it holds for
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'`. This file proves six of them — (k) local quasi-finiteness,
(l) finiteness, (m) unramifiedness, (n) being a monomorphism, (o) being an immersion and (p)
being a closed immersion.

All six are instances of one engine,
`AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff_of_pointTest` of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford`, which transfers a
condition of Properties of Stacks, Section 04XB, between the two relative diagonals as soon as
the condition transfers across a cartesian square of thickenings of algebraic *spaces* whose two
horizontal morphisms are locally of finite type. That transfer is **Stacks 0BPJ** at the point
test of Section 04XB, and the six parts of 0BPJ this file consumes are parts (1), (2), (5), (6),
(7) and (3), in that order.

## Why these six do not go through the cancellation engine

The other engine, `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff` of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`, asks that the property
cancel against a surjective closed immersion of morphisms of algebraic spaces: a composite
`a ≫ b` with the property whose first factor is a surjective closed immersion has `b` with the
property. For four of the six that cancellation is **false**, and the thickening itself refutes
it: `Spec(k) ⟶ Spec(k[ε]) ⟶ Spec(k)` has a surjective closed immersion for first factor and the
identity for composite, and the identity is a closed immersion, an immersion, a monomorphism and
unramified while `Spec(k[ε]) ⟶ Spec(k)` is none of those. For local quasi-finiteness and
finiteness the refutation is instead an affine thickening `Spec(k) ⊂ Spec(R)` with `R` a
non-finitely-generated `k`-algebra with residue field `k`: the composite is the identity again,
and `Spec(R) ⟶ Spec(k)` is not even locally of finite type. Properness survives that refutation
only because it splits into conjuncts, the locally-of-finite-type one being free for a relative
diagonal by part (2) of **Stacks 04XS**; neither local quasi-finiteness nor finiteness is a
conjunction of that shape in this library, so no instance of the cancellation engine reaches any
of the six.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.isFinite_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.unramified_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.mono_relativeDiagonal_iff`,
  `AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_iff` and
  `AlgebraicGeometry.Stack.isClosedImmersion_relativeDiagonal_iff`: **Stacks 0BPV** at its
  properties (k), (l), (m), (n), (o) and (p).

## Implementation notes

Three of the six are written at the abbreviation this library has for the condition of Section
04XB at the property — `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`,
`AlgebraicGeometry.Stack.IsImmersion` and `AlgebraicGeometry.Stack.IsClosedImmersion` — and the
other three at `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) directly, there
being no such abbreviation for finiteness, unramifiedness or monomorphy of a representable
1-morphism. Clause (j), universal openness, is written at Stacks 03YK for the same reason.

Clause (k) is **Stacks 0CJ9** item (8) read at this part key: being quasi-DM is by definition
(**Stacks 04YW**) local quasi-finiteness of the relative diagonal in the sense of Section 04XB, so
`AlgebraicGeometry.Stack.isQuasiDM_inner_iff_outer` *is* this clause, and it is reused rather than
reproved. Clauses (m) and (n) are *not* read off items (9) and (12) in the same way: the DM
condition and the monomorphy condition of **Stacks 04ZW** each carry a representability conjunct
which the clause of 0BPV does not — a conjunct that costs nothing, by part (1) of **Stacks 04XS**,
but which makes the statements different — so those two are fresh instances of the engine.

The permanence instances the engine asks of each property — stability under base change and
locality on the target for the fppf precoverage — are introduced locally in each proof when they
are not found by instance resolution, as the clauses of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse` do; no global instance is
added. For finiteness and for monomorphy both are instances already
(`AlgebraicGeometry.Space.isFinite_isLocalAtTarget_fppf`, **Stacks 0426**, and
`AlgebraicGeometry.Space.mono_isLocalAtTarget_fppf`, **Stacks 042D**), for closed immersions the
locality instance is **Stacks 0420**
(`AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fppf`), and for immersions and
unramifiedness it is the fpqc statement restricted along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
* [Stacks Project, Tag 042A](https://stacks.math.columbia.edu/tag/042A)
* [Stacks Project, Tag 042D](https://stacks.math.columbia.edu/tag/042D)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is locally quasi-finite in the sense of Stacks 04XB
(**Stacks 03XJ**, part (1)) if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem isLocallyQuasiFinite_relativeDiagonal_iff :
    Stack.IsLocallyQuasiFinite B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsLocallyQuasiFinite B S hS
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  isQuasiDM_inner_iff_outer B S hS m

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is finite in the sense of Stacks 04XB (**Stacks 03ZP**) if and
only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem isFinite_relativeDiagonal_iff :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.finiteMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.finiteMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (Space.finiteMorphismProperty B S hS)
    fun ha hb hsq hlft hlft' =>
      (Space.finiteMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is unramified in the sense of Stacks 04XB (**Stacks 03ZH**,
part (1)) if and only if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem unramified_relativeDiagonal_iff :
    haveI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
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
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) := by
  have _hunrBC : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have _hunrLoc : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (Space.unramifiedMorphismProperty B S hS)
    fun ha hb hsq hlft hlft' =>
      (Space.unramifiedMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is a monomorphism in the sense of Stacks 04XB if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem mono_relativeDiagonal_iff :
    HasRelativeProperty.{u, u, u + 1, u} B S hS
        (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
    fun ha hb hsq hlft hlft' hmono =>
      (Space.mono_iff_of_cartesianSquareOfThickeningHoms B S hS ha hb hsq hlft hlft').1 hmono

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is an immersion in the sense of Stacks 04XB if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem isImmersion_relativeDiagonal_iff :
    Stack.IsImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom := by
  have _himmLoc : (Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf B S hS
  exact hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (Space.immersionProperty B S hS)
    fun ha hb hsq hlft hlft' =>
      (Space.immersionProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the
relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is a closed immersion in the sense of Stacks 04XB if and only
if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem isClosedImmersion_relativeDiagonal_iff :
    Stack.IsClosedImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsClosedImmersion B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom :=
  hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (Space.closedImmersionProperty B S hS)
    fun ha hb hsq hlft hlft' =>
      (Space.closedImmersionProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1

end Diagonal

end AlgebraicGeometry.Stack

end
