module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Base change of a quasi-projective morphism

[Stacks, Tag 0B3G] asserts that a base change of a quasi-projective morphism is quasi-projective.
Quasi-projectivity of `f : X ⟶ S` is `AlgebraicGeometry.IsQuasiProjective`, the predicate of
[Stacks, Tag 01VW]: `f` is of finite type and `X` carries an invertible sheaf that is ample
relative to `f`. Both conjuncts are stable under base change, and the source's proof is exactly
that observation: finite type by [Stacks, Tag 01T4] and relative ampleness by
[Stacks, Tag 0893].

## Main results

* `AlgebraicGeometry.IsQuasiProjective.of_isPullback`: **[Stacks, Tag 0B3G]** for an arbitrary
  cartesian square. If `f' : X' ⟶ S'` is a base change of a quasi-projective `f : X ⟶ S`, then
  `f'` is quasi-projective, and the relatively ample sheaf witnessing it is the pullback along
  `X' ⟶ X` of the one witnessing quasi-projectivity of `f`.
* `AlgebraicGeometry.IsQuasiProjective.pullback_snd`: the same for the chosen fibre product,
  `pullback.snd f g : X ×_S S' ⟶ S'`.

## Implementation notes

**Finite type is the conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`**, as in [Stacks, Tag 01T1] and as
`AlgebraicGeometry.IsQuasiProjective` spells it, so the finite-type half of the source's
[Stacks, Tag 01T4] is two applications of
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`, against Mathlib's
instances for the two properties.

**Relative ampleness is `Stacks.AmpleBridge.relativelyAmpleBaseChange`**, which is
[Stacks, Tag 0893] for an arbitrary cartesian square in the spelling
`Stacks.RelativeAmple.IsRelativelyAmple` that
`AlgebraicGeometry.IsQuasiProjective` is stated over. No hypothesis is carried: that declaration
is already unconditional.

**The invertibility of the pulled-back sheaf is reinstated by hand.** The sheaf is existentially
bound by `AlgebraicGeometry.IsQuasiProjective` together with a proof of its invertibility, so
after destructuring there is nothing for instance synthesis to key on; the two invertibility
facts the statement of [Stacks, Tag 0893] asks for — for the sheaf on `X` and for its pullback to
`X'`, the latter being [Stacks, Tag 0B8L] through
`Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback` — are supplied as local
instances. `AlgebraicGeometry.SheafOfModules.IsInvertible` is `Prop`-valued, so proof irrelevance
makes the conclusion independent of which witness is used.

## References

* [Stacks Project, Tag 0B3G](https://stacks.math.columbia.edu/tag/0B3G)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01T4](https://stacks.math.columbia.edu/tag/01T4)
* [Stacks Project, Tag 01T1](https://stacks.math.columbia.edu/tag/01T1)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace IsQuasiProjective

/-- **[Stacks, Tag 0B3G].** A base change of a quasi-projective morphism is quasi-projective: if
`f' : X' ⟶ S'` fits into a cartesian square over a quasi-projective `f : X ⟶ S`, then `f'` is
quasi-projective.

Finite type is stable under base change, which is the finite-type half of [Stacks, Tag 01T4],
and the pullback along `X' ⟶ X` of a sheaf ample relative to `f` is ample relative to `f'`,
which is [Stacks, Tag 0893] in the form `Stacks.AmpleBridge.relativelyAmpleBaseChange`. -/
@[stacks 0B3G]
public theorem of_isPullback {X S X' S' : Scheme.{u}} {p : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (hsq : IsPullback p f' f g) (hf : IsQuasiProjective f) :
    IsQuasiProjective f' := by
  obtain ⟨L, hL, hLA⟩ := hf.exists_isRelativelyAmple
  have hLi : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have hLp : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback p).obj L) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback p.toLRSHom.toShHom L
  refine ⟨⟨MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hsq hf.locallyOfFiniteType,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hsq hf.quasiCompact⟩,
    (Scheme.Modules.pullback p).obj L, hLp, ?_⟩
  exact Stacks.AmpleBridge.relativelyAmpleBaseChange hsq L hLA

/-- **[Stacks, Tag 0B3G] for the chosen fibre product.** The base change
`pullback.snd f g : X ×_S S' ⟶ S'` of a quasi-projective morphism `f : X ⟶ S` along any
`g : S' ⟶ S` is quasi-projective. -/
public theorem pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : IsQuasiProjective f) : IsQuasiProjective (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g) hf

end IsQuasiProjective

end AlgebraicGeometry

end
