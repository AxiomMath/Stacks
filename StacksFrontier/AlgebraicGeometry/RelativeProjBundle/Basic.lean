module

public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective bundle of a quasi-coherent module

Let `X` be a scheme and `F` a quasi-coherent sheaf of modules on it. The symmetric algebra
`Sym(F)` is a commutative, nonnegatively graded algebra over the structure sheaf whose
homogeneous pieces are quasi-coherent, so it is a relative `Proj` situation, and

`𝐏(F) = Proj_X(Sym(F)) ⟶ X`

is its relative projective spectrum together with its structure morphism. This is the
projective bundle of `F`.

## Main definitions

* `Stacks.RelativeProj.projectiveBundle`: the projective bundle `𝐏(F)` of `F`, as a scheme.
* `Stacks.RelativeProj.projectiveBundleToBase`: its projection `π : 𝐏(F) ⟶ X`.

## Implementation notes

Both are `abbrev`s on top of `Stacks.RelativeProj.Situation.relativeProj` and
`Stacks.RelativeProj.Situation.relativeProjToBase` applied to
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent`, which is the symmetric algebra of `F`
as a relative `Proj` situation. No new mathematics is done here: everything is already proved,
and what this file supplies is the *name* of the object those two constructions produce. Being
reducible, it inherits the whole affine-chart API of a relative `Proj` situation — in
particular `Stacks.RelativeProj.Situation.relativeProjChart`, its cartesian square
`Stacks.RelativeProj.Situation.relativeProjChart_isPullback` and the transition equation
`Stacks.RelativeProj.Situation.relativeProjChart_transition` — with no transport.

`projectiveBundleToBase` is stated with target `X` rather than
`(symmetricSituationOfQuasicoherent X F).base`; the two agree by `rfl`, since
`Stacks.RelativeProj.symmetricSituation` sets its base field to `X`.

**There is no `projectiveBundleSituation` here, by design.** The relative `Proj` situation of
the symmetric algebra of a quasi-coherent module already has a name —
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent` — and a second name for it would be a
duplicate notion rather than a definition.

**The attribute is clause-qualified.** Tag 01OB defines the projective bundle with its
projection *and* the twists `𝒪_{𝐏(F)}(n)` of its structure sheaf, the latter being the
invertible module of Tag 01O4. This file names only the bundle and its projection, so the
attribute names only that clause.

The twists themselves are *not* missing from the library, and nothing here should be read as
asking for them to be built. Tag 01O4 is proved as
`Stacks.AlgebraicGeometry.relativeProjTwists_isInvertible`
(`StacksFrontier/AlgebraicGeometry/TwistMapsInvertible/Basic.lean:171`): every integral twist on a
relative homogeneous spectrum is invertible when the algebra is generated in degree one over its
degree-zero part. For the projective bundle specifically, `𝒪_{𝐏(E)}(1)` is constructed as
`Stacks.RelativeVeryAmpleTwist.twistOne` and proved invertible by
`Stacks.RelativeVeryAmpleTwist.isInvertibleModule_twistOne`
(`StacksFrontier/AlgebraicGeometry/RelativeVeryAmpleTwist/DegreeOne.lean:193, 221`), where
`Stacks.RelativeVeryAmpleTwist.schemeProjectiveBundle_eq` records that the `𝐏(E)` used there and
the relative `Proj` named here are the same datum, by `rfl`. The general-degree twists are
`gluedTwist` and `gluedTwistNatCast`
(`StacksFrontier/AlgebraicGeometry/TwistDataConstruction/NonnegativeDegree.lean:392`).

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [EGA II, Definition 4.1.1]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

/-- **The projective bundle `𝐏(F) = Proj_X(Sym(F))` of a quasi-coherent sheaf of modules**, the
relative projective spectrum of its symmetric algebra. -/
@[stacks 01OB "the projective bundle and its projection", ega "II 4.1.1" "P(E) itself"]
abbrev projectiveBundle (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] : Scheme.{u} :=
  (symmetricSituationOfQuasicoherent X F).relativeProj

/-- **The projection `π : 𝐏(F) ⟶ X` of a projective bundle**, the structure morphism of the
relative projective spectrum of `Sym(F)` over its base. -/
@[stacks 01OB "the projective bundle and its projection", ega "II 4.1.1" "projection to Y"]
abbrev projectiveBundleToBase (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    projectiveBundle X F ⟶ X :=
  (symmetricSituationOfQuasicoherent X F).relativeProjToBase

end Stacks.RelativeProj

end
