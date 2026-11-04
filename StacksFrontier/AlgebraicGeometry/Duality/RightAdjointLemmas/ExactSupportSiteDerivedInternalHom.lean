module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHom
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor

/-!
# The two forms of Stacks 0A77 are one isomorphism

For a closed quotient morphism `i : Z ⟶ X` of ringed spaces, [Stacks, Tag 0A77] identifies
`Ri_* R ℰom(𝒪_Z, -)` with derived internal Hom out of `i_* 𝒪_Z`. This library has it twice, with
two different right-hand sides:

* `ClosedQuotientMorphismOfRingedSpaces.derivedModulePushforwardDerivedSheafHomExactSupportIso`
  lands in `derivedHomSheafFromPushforwardStructureSheaf`, the right derived functor of
  coextension of scalars along `𝒪_X ⟶ i_* 𝒪_Z` followed by restriction of scalars;
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso`
  lands in the derived internal Hom **bifunctor of the ringed site of opens of `X`**,
  `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, at the first argument `Ri_* 𝒪_Z`.

The two have the same left-hand side, so composing them identifies the two right-hand sides.
That composite is what this file records.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.derivedHomSheafFromPushforwardStructureSheafSiteIso`:
  `R ℰom_{𝒪_X}(i_* 𝒪_Z, -)`, built by coextension of scalars and right-deriving, is the derived
  internal Hom of the ringed site of opens of `X` out of `Ri_* 𝒪_Z`.

## Why this composite is worth a name

It is the step that brings the duality development of [Stacks, Tag 0A76] into the vocabulary the
site-level tensor–Hom theory is stated in. The diagonal of [Stacks, Tag 0BYS],
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`, and with it the three cases of
[Stacks, Tag 0ATN] — in particular
`RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent_of_hasTorAmplitudeGE`, part (3) with
a tensor factor of Tor amplitude in `[a, ∞)` — are stated for `derivedSheafHomBifunctor` on an
arbitrary ringed site, and the ringed site of opens of a scheme is such a site. So the content of
[Stacks, Tag 0E2N] on the `X` side of `i` is available from the site-level theory
**without replacing `X` by an affine open**: no localisation, no [Stacks, Tag 0A78], no ring-level
[Stacks, Tag 0ATK]. The module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitude.lean` records what
still stands between that and the tag.

Neither leg is proved here and no new mathematics is introduced: the content is that the two
isomorphisms from the library compose, which they do because their left-hand sides are the same functor and
both files work at `CategoryTheory.HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The two right-hand sides of [Stacks, Tag 0A77] agree.** For a closed quotient morphism
`i : Z ⟶ X` of ringed spaces, the right derived functor of coextension of scalars along
`𝒪_X ⟶ i_* 𝒪_Z` is the derived internal Hom of the ringed site of opens of `X` out of
`Ri_* 𝒪_Z`:

`R ℰom_{𝒪_X}(i_* 𝒪_Z, -) ≅ RSheafHom(Ri_* 𝒪_Z, -)`.

Both sides are the common value of the two formalized forms of [Stacks, Tag 0A77], whose shared
left-hand side is `R ℰom(𝒪_Z, -)` followed by `i_*` on derived categories. -/
@[stacks 0A77 "the two right-hand sides identified: coextension of scalars and the site-level \
derived internal Hom bifunctor"]
def derivedHomSheafFromPushforwardStructureSheafSiteIso :
    S.derivedHomSheafFromPushforwardStructureSheaf ≅
      (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) :=
  S.derivedModulePushforwardDerivedSheafHomExactSupportIso.symm ≪≫
    S.derivedSheafHomExactSupportPushforwardNatIso

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
