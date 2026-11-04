module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# A finite locally free morphism is proper, flat and of relative dimension zero

A morphism of schemes that is finite locally free of rank `r` is finite, flat and locally of
finite presentation (Stacks 02KB). This file reads off the three further properties that a
degree calculation on cycles needs: such a morphism is locally of finite type, it is proper,
it is flat, and — the only one that is not immediate from the definition — it has relative
dimension zero in the sense of `AlgebraicGeometry.RelativeDimension`.

Relative dimension zero is where the content is. A finite morphism is locally quasi-finite,
and a morphism locally of finite type is locally quasi-finite exactly when every nonempty fibre
is equidimensional of topological Krull dimension zero (Stacks 0397); the second condition is
the definition of relative dimension zero.

## Main results

* `Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank` — a finite locally free
  morphism is locally of finite type.
* `Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank` — a finite locally free morphism is
  proper.
* `Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank` — a finite locally free morphism is flat.
* `Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank` — a finite locally free
  morphism has relative dimension zero.

## Implementation notes

The three properties of the morphism are stated as theorems rather than instances, because the
rank `r` occurs in the hypothesis and cannot be recovered from the conclusion; instance search
would have to guess it. That is the same reason
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree` is not an instance.

`relativeDimension_zero_of_isFiniteLocallyFreeOfRank` opens with a `let` supplying
`LocallyOfFiniteType`, because `AlgebraicGeometry.RelativeDimension` is only defined for a
morphism locally of finite type and the hypothesis here is the rank condition instead. The
instance is the one produced by `locallyOfFiniteType_of_isFiniteLocallyFreeOfRank`, so a
consumer that already has `LocallyOfFiniteType` in scope should check that the two agree — they
do, `LocallyOfFiniteType` being a `Prop`.

## References

* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- The characterisation of Stacks 02KB applied to a finite locally free morphism of rank `r`. -/
private theorem isFinite_and_flat_and_locallyOfFinitePresentation_of_isFiniteLocallyFreeOfRank
    {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) [IsFiniteLocallyFreeOfRank f r] :
    IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f :=
  (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r)

/-- A morphism that is finite locally free of rank `r` is finite: this is one third of the
characterisation of Stacks 02KB. -/
theorem isFinite_of_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : IsFinite f :=
  (isFinite_and_flat_and_locallyOfFinitePresentation_of_isFiniteLocallyFreeOfRank f r).1

/-- A morphism that is finite locally free of rank `r` is locally of finite type: it is finite,
hence affine with a finite algebra of sections, hence of finite type. -/
theorem locallyOfFiniteType_of_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : LocallyOfFiniteType f := by
  let _ : IsFinite f := isFinite_of_isFiniteLocallyFreeOfRank f r
  infer_instance

/-- A morphism that is finite locally free of rank `r` is proper. A finite morphism is exactly a
proper affine one. -/
theorem isProper_of_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : IsProper f :=
  (AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mp
    (isFinite_of_isFiniteLocallyFreeOfRank f r)).1

/-- A morphism that is finite locally free of rank `r` is flat: this is another third of the
characterisation of Stacks 02KB. -/
theorem flat_of_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : Flat f :=
  (isFinite_and_flat_and_locallyOfFinitePresentation_of_isFiniteLocallyFreeOfRank f r).2.1

/-- A morphism that is finite locally free of rank `r` has relative dimension zero: it is
finite, hence locally quasi-finite, and for a morphism locally of finite type that is the same
as relative dimension zero. -/
theorem relativeDimension_zero_of_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S)
    (r : ℕ) [IsFiniteLocallyFreeOfRank f r] :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isFiniteLocallyFreeOfRank f r
    AlgebraicGeometry.RelativeDimension f 0 := by
  let _ : IsFinite f := isFinite_of_isFiniteLocallyFreeOfRank f r
  let _ : LocallyOfFiniteType f := locallyOfFiniteType_of_isFiniteLocallyFreeOfRank f r
  exact (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero f).mp inferInstance

end Stacks.Morphisms

end
