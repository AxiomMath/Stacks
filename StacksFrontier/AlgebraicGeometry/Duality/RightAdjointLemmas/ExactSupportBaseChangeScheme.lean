module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChange

/-!
# Base change for the right adjoint of pushforward, for a square of schemes

Let

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

be a cartesian square of schemes with `i` a closed immersion, and suppose `Z` and `X'` are tor
independent over `X`. [Stacks, Tag 0E2L] compares two base change maps in this situation: the map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

of [Stacks, Tag 0E2K], and the map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`

obtained from it by pushing forward along `i'`. It says each is an isomorphism exactly when the
other is.

That statement is
`isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`, in the
namespace `Stacks.Duality.ExactSupportBaseChange`.
`RingedSpaceModuleAdjunction.ClosedQuotientBaseChange.isIso_rightAdjointBaseChangeMap_iff` proves
the comparison for a square of ringed spaces with the tor-independence consequence
`Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` supplied as a named hypothesis. What this module provides is the
construction of that hypothesis from the geometry: the square being cartesian with `i` a closed
immersion makes `i'` a closed immersion too, both legs then present their source as a closed
quotient of their target, and tor independence supplies the identification through
[Stacks, Tag 0E23].

## Main definitions

* `AlgebraicGeometry.Duality.closedImmersionPushforwardComparison`: the comparison of the two
  models of `Ri_*` used on either side of the instantiation.
* `AlgebraicGeometry.Duality.derivedBaseChangeIso`: the identification
  `Lg^* ⋙ Ri'_* ≅ Ri_* ⋙ Lf^*` of [Stacks, Tag 0E23], transported to the model of `Ri_*` that
  [Stacks, Tag 0E2L] is stated for.

## Implementation notes

Two models of `Ri_*` meet here and they are not definitionally equal. [Stacks, Tag 0E2L] is
stated for `(RingedSpaceModuleAdjunction.modulePushforward _).mapDerivedCategory`, the derived
functor of an exact functor; [Stacks, Tag 0E23] is stated for
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`, a total right derived
functor. The second is by `rfl` the total right derived functor that
`Stacks.ClosedImmersion.exists_closedImmersionDerivedPushforwardComparison` compares the first
to, and `closedImmersionPushforwardComparison` below is that comparison; `derivedBaseChangeIso`
conjugates [Stacks, Tag 0E23] by it on both legs. The comparison is extracted from an existential
by `Exists.choose`, so it is noncomputable and opaque — only its existence is used, which is all
the statement needs, since `IsIso` of a map built from it is what is being characterized and the
characterization holds for any choice.

The tor-independence input is `AlgebraicGeometry.TorIndependent i f` of [Stacks, Tag 08IA], in the
argument order [Stacks, Tag 0E23] uses: `Z` and `X'` over `X`, with `i : Z ⟶ X` first.

`derivedBaseChangeIso` takes `DerivedStalkBaseChangeEqKFlat` as a hypothesis, as
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIsoOfKFlatEq` does.

## References

* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Duality

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- The comparison between the two models of `Ri_*` for a closed immersion of schemes: the derived
functor of the exact pushforward of modules, and the total right derived functor of its action on
homotopy categories. This is
`Stacks.ClosedImmersion.exists_closedImmersionDerivedPushforwardComparison` with the existential
discharged; only its existence is used. -/
def closedImmersionPushforwardComparison (i : Z ⟶ X) [IsClosedImmersion i] :
    (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory ≅
      derivedPushforward i.toLRSHom.toShHom :=
  (Stacks.ClosedImmersion.exists_closedImmersionDerivedPushforwardComparison i).choose

/-- **Stacks 0E23, in the model of `Ri_*` that Stacks 0E2L is stated for.** For a cartesian square
of schemes with `i` a closed immersion and `Z`, `X'` tor independent over `X`, the identification
`Lg^* ⋙ Ri'_* ≅ Ri_* ⋙ Lf^*`.

This is `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIsoOfKFlatEq`
conjugated on both legs by `AlgebraicGeometry.Duality.closedImmersionPushforwardComparison`, and
turned around: that result is stated as `Ri_* ⋙ Lf^* ≅ Lg^* ⋙ Ri'_*`. -/
def derivedBaseChangeIso (sq : IsPullback i' g f i) [IsClosedImmersion i]
    [IsClosedImmersion i'] (htor : TorIndependent i f)
    (hkflat : Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqKFlat sq) :
    derivedPullback g.toLRSHom.toShHom ⋙
        (modulePushforward i'.toLRSHom.toShHom).mapDerivedCategory ≅
      (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory ⋙
        derivedPullback f.toLRSHom.toShHom :=
  Functor.isoWhiskerLeft _ (closedImmersionPushforwardComparison i') ≪≫
    (Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIsoOfKFlatEq
      sq htor hkflat).symm ≪≫
    Functor.isoWhiskerRight (closedImmersionPushforwardComparison i).symm _

end AlgebraicGeometry.Duality

end
