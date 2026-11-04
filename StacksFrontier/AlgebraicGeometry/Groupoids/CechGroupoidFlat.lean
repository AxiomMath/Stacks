module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Groupoids.CechGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback

/-!
# The Čech groupoid of a flat quasi-compact morphism

The source and target maps of the Čech groupoid of a morphism `f : Z ⟶ W` of schemes over `S`
are the two projections of the kernel pair `Z ×_W Z`, so on underlying schemes they are base
changes of `f` itself. Every property of morphisms of schemes which is stable under base change
therefore passes from `f` to both of them.

## Main results

* `AlgebraicGeometry.cechGroupoid_source_left` and
  `AlgebraicGeometry.cechGroupoid_target_left` transfer an arbitrary property stable under base
  change.
* `AlgebraicGeometry.flat_cechGroupoid_source`,
  `AlgebraicGeometry.flat_cechGroupoid_target`,
  `AlgebraicGeometry.quasiCompact_cechGroupoid_source` and
  `AlgebraicGeometry.quasiCompact_cechGroupoid_target` are the two cases used by the theory of
  flat quasi-compact groupoid schemes, stated as instances.

## Implementation notes

The two named cases are instances rather than plain theorems: the hypotheses of the results on
flat quasi-compact groupoid schemes are typeclass assumptions on `G.source.left` and
`G.target.left`, so a consumer applying them at the Čech groupoid needs exactly these four
facts found by instance search. Their discrimination keys mention
`AlgebraicGeometry.cechGroupoid`, so they are only ever tried on a goal about a Čech groupoid.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {Z W : Over S} (f : Z ⟶ W)

/-- The source map of the Čech groupoid of `f` is the second projection of the kernel pair of
`f`, so on underlying schemes it inherits from `f` every property stable under base change. -/
theorem cechGroupoid_source_left {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] (hf : P f.left) : P (cechGroupoid f).source.left :=
  overFibreProduct_snd f f hf

/-- The target map of the Čech groupoid of `f` is the first projection of the kernel pair of
`f`, so on underlying schemes it inherits from `f` every property stable under base change. -/
theorem cechGroupoid_target_left {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] (hf : P f.left) : P (cechGroupoid f).target.left :=
  overFibreProduct_fst f f hf

/-- The source map of the Čech groupoid of a flat morphism is flat. -/
instance flat_cechGroupoid_source [Flat f.left] : Flat (cechGroupoid f).source.left :=
  cechGroupoid_source_left (P := @Flat) f ‹Flat f.left›

/-- The target map of the Čech groupoid of a flat morphism is flat. -/
instance flat_cechGroupoid_target [Flat f.left] : Flat (cechGroupoid f).target.left :=
  cechGroupoid_target_left (P := @Flat) f ‹Flat f.left›

/-- The source map of the Čech groupoid of a quasi-compact morphism is quasi-compact. -/
instance quasiCompact_cechGroupoid_source [QuasiCompact f.left] :
    QuasiCompact (cechGroupoid f).source.left :=
  cechGroupoid_source_left (P := @QuasiCompact) f ‹QuasiCompact f.left›

/-- The target map of the Čech groupoid of a quasi-compact morphism is quasi-compact. -/
instance quasiCompact_cechGroupoid_target [QuasiCompact f.left] :
    QuasiCompact (cechGroupoid f).target.left :=
  cechGroupoid_target_left (P := @QuasiCompact) f ‹QuasiCompact f.left›

end AlgebraicGeometry

end
