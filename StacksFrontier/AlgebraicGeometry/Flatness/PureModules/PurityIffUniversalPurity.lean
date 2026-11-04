module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.UniversalPurityCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.NoetherianStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Relative purity versus universal relative purity

Let `f : X ⟶ S` be a morphism of finite type and let `ℱ` be a finite type quasi-coherent
`𝒪_X`-module which is flat over `S`. Universal purity of `ℱ` relative to `S` always implies
purity relative to `S`, there being fewer impurity diagrams to exclude, and for a module flat
over the base the converse holds as well, so the two notions agree.

## Main results

* `AlgebraicGeometry.isPureRelative_of_isUniversallyPureRelative`: universal purity relative to
  the base implies purity relative to the base, with no hypothesis on the base.
* `AlgebraicGeometry.isUniversallyPureRelative_of_isPureRelative`: for a module flat over the
  base, purity relative to the base implies universal purity relative to the base.
* `AlgebraicGeometry.isPureRelative_iff_isUniversallyPureRelative`: for a module flat over the
  base, purity relative to the base is the same as universal purity relative to the base.
* `AlgebraicGeometry.isPureRelative_iff_isUniversallyPureRelative_of_isLocallyNoetherian`: over
  a locally Noetherian base, the same equivalence without the flatness hypothesis.

## Implementation notes

Both notions are the pointwise conditions of Tag 05J4, so every statement here is obtained from
the corresponding statement along a single fibre by quantifying over the point of the base. The
harder implication is Tag 05L5, applied to the pre-pure situation at each point; flatness over
the base restricts to flatness at every point of each fibre. Over a locally Noetherian base the
harder implication is instead Tag 05J8, which needs no flatness, the Noetherian hypothesis on
the local ring coming from the Mathlib instance for a locally Noetherian scheme.

## References

* [Stacks Project, Tag 05L6](https://stacks.math.columbia.edu/tag/05L6)
* [Stacks Project, Tag 05L5](https://stacks.math.columbia.edu/tag/05L5)
* [Stacks Project, Tag 05J8](https://stacks.math.columbia.edu/tag/05J8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 05L6**, the implication which needs no hypothesis on the base: a
finite type quasi-coherent module which is universally pure relative to the base is pure
relative to the base, there being fewer impurity diagrams to exclude. -/
@[stacks 05L6 "the implication universally pure relative to S implies pure relative to S, with
no flatness and no Noetherian hypothesis"]
theorem isPureRelative_of_isUniversallyPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (h : IsUniversallyPureRelative f F) :
    IsPureRelative f F :=
  fun s D _ _ => h s D

/-- **Stacks Project, Tag 05L6**, the harder implication. Let `f : X ⟶ S` be of finite type and
let `ℱ` be a finite type quasi-coherent `𝒪_X`-module which is flat over `S`. If `ℱ` is pure
relative to `S` then it is universally pure relative to `S`. -/
@[stacks 05L6 "the implication pure relative to S implies universally pure relative to S, for a
module flat over S, with no hypothesis on S"]
theorem isUniversallyPureRelative_of_isPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (h : IsPureRelative f F) :
    IsUniversallyPureRelative f F :=
  fun s => isUniversallyPureAlong_of_isPureAlong f F s
    (fun x => hflat (f.fiberι s x)) (h s)

/-- **Stacks Project, Tag 05L6.** Let `f : X ⟶ S` be of finite type and let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module which is flat over `S`. Then `ℱ` is pure relative to `S` if and only
if it is universally pure relative to `S`. -/
@[stacks 05L6]
theorem isPureRelative_iff_isUniversallyPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsPureRelative f F ↔ IsUniversallyPureRelative f F :=
  ⟨isUniversallyPureRelative_of_isPureRelative f F hflat,
    isPureRelative_of_isUniversallyPureRelative f F⟩

/-- **Stacks Project, Tag 05L6** over a locally Noetherian base, where the flatness hypothesis
is unnecessary. Let `f : X ⟶ S` be of finite type and let `ℱ` be a finite type quasi-coherent
`𝒪_X`-module. If `S` is locally Noetherian then `ℱ` is pure relative to `S` if and only if it is
universally pure relative to `S`. -/
@[stacks 05L6 "a strengthening over a locally Noetherian base: Tag 05J8 replaces Tag 05L5 and
needs no flatness, so the flatness hypothesis of the source is dropped here"]
theorem isPureRelative_iff_isUniversallyPureRelative_of_isLocallyNoetherian
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    IsPureRelative f F ↔ IsUniversallyPureRelative f F := by
  refine ⟨fun h s => ?_, isPureRelative_of_isUniversallyPureRelative f F⟩
  exact (isPureAlong_iff_isUniversallyPureAlong_of_isNoetherianRing_stalk
    ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u})).mp (h s)

end AlgebraicGeometry

end
