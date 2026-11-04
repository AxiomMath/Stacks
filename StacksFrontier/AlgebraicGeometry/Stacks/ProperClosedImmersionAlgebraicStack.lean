module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange

/-!
# A closed immersion of algebraic stacks is proper (Stacks 0CL8)

**Stacks 0CL8** says that a closed immersion of algebraic stacks over `S` is a proper
1-morphism of algebraic stacks. Properness is **Stacks 0CL5**, the conjunction of three
conditions on an *arbitrary* 1-morphism of algebraic stacks — separatedness (**Stacks 04YW**),
finite type (**Stacks 06FS**, part (2)) and universal closedness (**Stacks 0513**, part (2)) —
and each conjunct is discharged separately below.

As the source puts it, a closed immersion is by definition representable (**Stacks 04YL**,
part (2)), so the discussion of **Stacks 04XB** applies and the statement follows from the
corresponding result for morphisms of algebraic spaces, **Stacks 04XZ**. Concretely:

* *Separatedness* asks that the relative diagonal `Δ_f` be proper in the sense of Stacks 04XB.
  A closed immersion is an immersion and hence a monomorphism (**Stacks 0504**), and a
  monomorphism of algebraic stacks is separated (**Stacks 06MY**) — whose proof runs the
  Stacks 04XB discussion at the properness of the diagonal, using Stacks 04XZ by way of
  Stacks 042N.
* *Finite type* is local finite type together with quasi-compactness. An immersion is locally
  of finite type by **Stacks 06FV**, and a closed immersion is quasi-compact by
  **Stacks 0CL1**.
* *Universal closedness* asks that every base change of `f` along a 1-morphism of algebraic
  stacks be closed on the topological spaces of points of **Stacks 04XG** and **04XL**. A base
  change of a closed immersion is a closed immersion (**Stacks 045C** at the closed-immersion
  property of Stacks 04XB, conjoined with **Stacks 0302**), and a closed immersion of algebraic
  stacks is closed on points (**Stacks 0H20**), which is where Stacks 04XZ enters for this
  conjunct.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_isClosedImmersion`: **Stacks 0CL8**.

## Implementation notes

The source asserts one proposition and the covering set is
`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_isClosedImmersion`; the two auxiliary
results stated before it are the closed-immersion cases of two statements the library already
has for immersions, recorded separately because each is used in two of the three conjuncts.

Nothing is carried as a hypothesis: the representability clause of part (2) of Stacks 04YL is
exactly what the Stacks 04XB machinery consumes, and the universal-closedness conjunct is
quantified over 1-morphisms of algebraic stacks with the canonical 2-fibre product square of
**Stacks 04T2** supplying the base change, so the 2-fibre product is available unconditionally.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 06MY](https://stacks.math.columbia.edu/tag/06MY)
* [Stacks Project, Tag 0CL1](https://stacks.math.columbia.edu/tag/0CL1)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0CL8](https://stacks.math.columbia.edu/tag/0CL8)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- A closed immersion of algebraic stacks over `S` is separated in the sense of
**Stacks 04YW**, that is, its relative diagonal is proper in the relative sense of
Stacks 04XB.

A closed immersion is an immersion and hence a monomorphism by **Stacks 0504**, and a
monomorphism is separated by **Stacks 06MY**. -/
theorem isSeparated_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsClosedImmersion B S hS f) :
    IsSeparated B S hS f :=
  isSeparated_of_isMonomorphism B S hS f
    (isMonomorphism_of_isImmersion B S hS f (isImmersion_of_isClosedImmersion B S hS f hf))

/-- A closed immersion of algebraic stacks over `S` is universally closed in the sense of
part (2) of **Stacks 0513**.

Every base change of `f` along a 1-morphism of algebraic stacks is again a closed immersion,
by **Stacks 045C** at the closed-immersion property of Stacks 04XB together with **Stacks
0302** for representability, and a closed immersion of algebraic stacks is a closed map on the
spaces of points by **Stacks 0H20**. -/
theorem universallyClosed_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsClosedImmersion B S hS f) :
    UniversallyClosed B S hS f :=
  fun _ g =>
    isClosedMap_pointsMap_of_isClosedImmersion B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g f).fst
      (isClosedImmersion_baseChange B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS g f)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hf)

/-- **Stacks 0CL8.** A closed immersion of algebraic stacks over `S` is a proper 1-morphism of
algebraic stacks.

Properness is the conjunction of **Stacks 0CL5**, and its three conjuncts are discharged in
turn: separatedness through monomorphy (**Stacks 0504** and **06MY**), local finite type by
**Stacks 06FV** for immersions, quasi-compactness by **Stacks 0CL1**, and universal closedness
from stability of closed immersions under base change (**Stacks 045C**) together with their
closedness on points (**Stacks 0H20**). -/
@[stacks 0CL8]
theorem isProper_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsClosedImmersion B S hS f) :
    IsProper B S hS f :=
  ⟨isSeparated_of_isClosedImmersion B S hS f hf,
    ⟨isLocallyOfFiniteType_of_isImmersion B S hS f (isImmersion_of_isClosedImmersion B S hS f hf),
      isQuasiCompactMorphism_of_isClosedImmersion B S hS f hf⟩,
    universallyClosed_of_isClosedImmersion B S hS f hf⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
