module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedImpliesValuativeUniqueness
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeExistenceUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeUniquenessSeparated

/-!
# Valuative criterion for properness (Stacks 0CLZ)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site `B`,
of finite type (**Stacks 06FS**, part (2)) and quasi-separated (**Stacks 04YW**). **Stacks
0CLZ** says that `f` is proper if and only if it satisfies both the uniqueness and the existence
parts of the valuative criterion.

Properness of `f` (**Stacks 0CL5**) is the conjunction of separatedness, finite type and
universal closedness, so with finite type standing as a hypothesis the equivalence splits into
two halves which are matched by the four surrounding results.

* *Separated and uniqueness.* `f` separated gives the uniqueness part by **Stacks 0CLU**, and a
  quasi-separated `f` satisfying the uniqueness part is separated by **Stacks 0CLT**.
* *Universally closed and existence.* `f` quasi-separated and universally closed gives the
  existence part by **Stacks 0CLX**, and `f` quasi-compact — the second conjunct of finite type
  — satisfying the existence part is universally closed by **Stacks 0CLW**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_iff_valuativeCriterion`: **Stacks 0CLZ**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.valuativeCriterion_of_isProper`: the direction from
  properness to the two criteria, which needs the finite type hypothesis nowhere.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_valuativeCriterion`: the direction from
  the two criteria to properness.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_relativeDiagonal`: the relative
  diagonal of a 1-morphism locally of finite type is locally of finite type in the relative sense
  of Stacks 04XB.

## Implementation notes

Finite type enters the equivalence twice over. As a hypothesis it supplies the middle conjunct
of properness in the direction from the criteria; and its quasi-compactness conjunct — finite
type being local finite type together with quasi-compactness — is the hypothesis of Stacks 0CLW.
Quasi-separatedness enters twice as well: it is the hypothesis of Stacks 0CLX in one direction
and of Stacks 0CLT in the other. Neither hypothesis is used in the direction from properness to
the two criteria beyond quasi-separatedness, so that direction is stated separately without them.

`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_relativeDiagonal` below records
the finiteness of the relative diagonal that the finite type hypothesis gives on its own: for `f`
locally of finite type, `Δ_f` is locally of finite presentation by the first assertion of
**Stacks 0CMG**, hence locally of finite type by the first assertion of **Stacks 06Q5**, in the
universal smooth-diagram sense of **Stacks 06FS**; and `Δ_f` is representable by algebraic spaces
by part (1) of **Stacks 04XS**, so the assertion of **Stacks 06FM** for a representable
1-morphism identifies that sense with the relative one. Stacks 0CLT does not need it: part (2)
of Stacks 04XS gives local finiteness of type of `Δ_f` for a 1-morphism subject to no finiteness
hypothesis at all.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLT](https://stacks.math.columbia.edu/tag/0CLT)
* [Stacks Project, Tag 0CLU](https://stacks.math.columbia.edu/tag/0CLU)
* [Stacks Project, Tag 0CLW](https://stacks.math.columbia.edu/tag/0CLW)
* [Stacks Project, Tag 0CLX](https://stacks.math.columbia.edu/tag/0CLX)
* [Stacks Project, Tag 0CLZ](https://stacks.math.columbia.edu/tag/0CLZ)
* [Stacks Project, Tag 0CMG](https://stacks.math.columbia.edu/tag/0CMG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- A quasi-separated proper 1-morphism of algebraic stacks satisfies both the uniqueness and the
existence parts of the valuative criterion.

This is the direction of **Stacks 0CLZ** which does not need the finite type hypothesis:
separatedness, the first conjunct of properness,
gives the uniqueness part by **Stacks 0CLU**, and universal closedness, the third conjunct, gives
the existence part by **Stacks 0CLX** in the presence of quasi-separatedness. -/
theorem valuativeCriterion_of_isProper (f : 𝒳 ⟶ 𝒴)
    (hqs : IsQuasiSeparated B S hS f) (hf : IsProper B S hS f) :
    ValuativeCriterion.Uniqueness B S hS f ∧ ValuativeCriterion.Existence B S hS f :=
  ⟨Stack.valuativeCriterionUniqueness_of_isSeparated B S hS f hf.1,
    Stack.valuativeCriterionExistence_of_universallyClosed B S hS hqs hf.2.2⟩

/-- **The relative diagonal of a 1-morphism of algebraic stacks which is locally of finite type
is locally of finite type**, in the relative sense of Stacks 04XB.

`Δ_f` is locally of finite presentation by the first assertion of **Stacks 0CMG**, hence locally
of finite type by the first assertion of **Stacks 06Q5**, in the universal smooth-diagram sense
of **Stacks 06FS**; being representable by algebraic spaces by part (1) of **Stacks 04XS**, it
satisfies the relative condition of Stacks 04XB by the assertion of **Stacks 06FM** for a
representable 1-morphism. -/
theorem isLocallyOfFiniteType_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) :
    Stack.IsLocallyOfFiniteType B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) := by
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS
      (fun _ _ g => Space.IsLocallyOfFiniteType B S hS g)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property (twoFibreProduct B S hS f f).property (relativeDiagonal B S hS f).hom
      (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).1
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf))

/-- A quasi-separated 1-morphism of algebraic stacks of finite type which satisfies both the
uniqueness and the existence parts of the valuative criterion is proper.

This is the direction of **Stacks 0CLZ** from the criteria: the uniqueness part gives
separatedness by **Stacks 0CLT**, finite type is a hypothesis, and the existence part gives
universal closedness by **Stacks 0CLW**, whose quasi-compactness hypothesis is the second
conjunct of finite type. -/
theorem isProper_of_valuativeCriterion (f : 𝒳 ⟶ 𝒴)
    (hft : IsFiniteType B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hu : ValuativeCriterion.Uniqueness B S hS f)
    (he : ValuativeCriterion.Existence B S hS f) :
    IsProper B S hS f :=
  ⟨isSeparated_of_valuativeCriterionUniqueness B S hS f hqs hu, hft,
    universallyClosed_of_isQuasiCompactMorphism_of_valuativeCriterionExistence B S hS f hft.2 he⟩

/-- **Stacks 0CLZ.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is of
finite type (**Stacks 06FS**, part (2)) and quasi-separated (**Stacks 04YW**). Then `f` is proper
(**Stacks 0CL5**) if and only if it satisfies both the uniqueness part (**Stacks 0CLG**) and the
existence part (**Stacks 0CLK**) of the valuative criterion.

Properness is separatedness, finite type and universal closedness, and under the standing
hypotheses the equivalence is the conjunction of two equivalences: separatedness is the
uniqueness part, by **Stacks 0CLU** forwards and **Stacks 0CLT** backwards, and universal
closedness is the existence part, by **Stacks 0CLX** forwards and **Stacks 0CLW** backwards. -/
@[stacks 0CLZ]
theorem isProper_iff_valuativeCriterion (f : 𝒳 ⟶ 𝒴)
    (hft : IsFiniteType B S hS f)
    (hqs : IsQuasiSeparated B S hS f) :
    IsProper B S hS f ↔
      ValuativeCriterion.Uniqueness B S hS f ∧ ValuativeCriterion.Existence B S hS f :=
  ⟨valuativeCriterion_of_isProper B S hS f hqs,
    fun h => isProper_of_valuativeCriterion B S hS f hft hqs h.1 h.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
