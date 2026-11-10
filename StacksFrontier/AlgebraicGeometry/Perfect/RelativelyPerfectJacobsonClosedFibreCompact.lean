module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreStalkwise
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkCompact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed fibre of Stacks 0DJZ is quasi-compact, and its stalk bound is uniform

Let `(R, I)` be a ring with an ideal, write `S = Spec R` and `S₀ = Spec (R/I)`, let
`f : X ⟶ S` be proper, flat and locally of finite presentation, and write `X₀ = S₀ ×_S X`.

The source's proof of Stacks 0DJZ opens by reading a Tor-amplitude interval off the closed fibre:
*for each `i` the complex `E_0|_{U_{i, 0}}` has tor amplitude in `[a_i, b_i]`*. Because `f` is
proper, the closed fibre is quasi-compact, so the finitely many intervals of that step are
contained in a single one and the reading is uniform on the whole of `X₀`. This module proves
that.

## Main results

* `AlgebraicGeometry.Scheme.Hom.compactSpace_closedFibre`: the closed fibre `X₀` of a proper `f`
  is quasi-compact.
* `AlgebraicGeometry.Scheme.Hom.exists_stalkTorAmplitude_closedFibre`: from `S₀`-perfectness of
  the derived restriction of `E` to `X₀` there is a *single* interval containing the Tor amplitude
  of the stalk at every point of `X₀` of that restriction, read over `f₀^{-1}𝒪_{S₀}`.

## Implementation notes

Quasi-compactness of `X₀` is read off the structure morphism `f₀ = closedFibreToBase f I` rather
than off the projection `X₀ ⟶ X`: `f₀` is the base change of `f` along `S₀ ⟶ S`, properness is
stable under base change, a proper morphism is quasi-compact, and `Spec (R/I)` is quasi-compact.
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` then applies. This is the same route
the sibling module `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonChart`
takes for `X` itself, there off universal closedness of `f`.

Flatness and local finite presentation of `f₀` are not hypotheses: both are stable under base
change and instance search supplies them from `[Flat f]` and `[LocallyOfFinitePresentation f]`, as
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibre`.

No `stacks` attribute is placed here. Neither statement is a clause of Stacks 0DJZ: the first is a
topological fact about the square and the second is the forward extraction of an interval from the
tag's *hypothesis*, so neither asserts any part of the tag's conclusion.

The hypothesis pair `D₀`, `hD₀` is satisfiable and not an empty demand: the canonical family
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily` inhabits `D₀`, and
`AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical` discharges `hD₀` at it.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.48.8 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- The closed fibre `X₀ = S₀ ×_S X` of the square of Stacks 0DJZ, as a scheme.

`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibre` names the three
morphisms of the square but not its corner, and the corner is needed as a `Scheme` in its own
right here: `CompactSpace (pullback (closedBase I) f)` elaborates the pullback in the category of
types rather than of schemes, since `CompactSpace` asks for a type and nothing in that expression
pins the category. Being an `abbrev` this unfolds reducibly, so it unifies with the spelling
`pullback (closedBase I) f` that the rest of the chain uses. -/
public abbrev closedFibre : Scheme.{u} := pullback (closedBase I) f

/-- **The closed fibre of a proper morphism over an affine base is quasi-compact.** The structure
morphism `X₀ ⟶ S₀` is the base change of `f` along `S₀ ⟶ S`, hence proper, hence quasi-compact;
and `S₀ = Spec (R/I)` is quasi-compact. -/
@[ega "III 6.9.4" "special case"]
public theorem compactSpace_closedFibre [IsProper f] :
    CompactSpace (closedFibre f I) :=
  QuasiCompact.compactSpace_of_compactSpace (closedFibreToBase f I)

/-- The stalk ring of the inverse-image ringed space of the closed fibre's structure morphism is
commutative, at every point.

The sibling modules seat the same fact for `f` itself, each under a name of its own because a
`local instance` attribute does not reach an importing module; this is the instance for `f₀`. -/
local instance commRing_stalk_inverseImage_closedFibre (y : closedFibre f I) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base)).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **One Tor-amplitude interval bounding every stalk on the closed fibre.** Let `E` be an object
of `D(𝒪_X)` whose derived restriction to `X₀` is `S₀`-perfect for a family of certificates pinned
to the genuine tensor product of sheaves of modules. Then there is a single interval `[a, b]`
containing, for every point `y` of `X₀`, the Tor amplitude over `(f₀^{-1}𝒪_{S₀})_y` of the stalk
at `y` of that restriction read over `f₀^{-1}𝒪_{S₀}`.

This is the source's *for each `i` the complex `E_0|_{U_{i, 0}}` has tor amplitude in
`[a_i, b_i]`*, with the finitely many intervals already merged into one: the closed fibre is
quasi-compact by `compactSpace_closedFibre`, so
`exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_compactSpace` applies to it directly. -/
public theorem exists_stalkTorAmplitude_closedFibre [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hD₀ : IsGenuineRelativeTensorFamily (closedFibreToBase f I) D₀)
    (E₀ : DerivedCategory (OXMod.{u, u} (closedFibre f I).toRingedSpace))
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀ E₀) :
    ∃ a b : ℤ, ∀ y : closedFibre f I,
      HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
              (closedFibreToBase f I).base)).obj y))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
                (closedFibreToBase f I).base)) y).mapDerivedCategory.obj
          ((derivedScalarRestriction (closedFibreToBase f I)).obj E₀)) a b :=
  have := compactSpace_closedFibre f I
  exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_compactSpace
    (closedFibreToBase f I) D₀ hD₀ E₀ hE₀

end AlgebraicGeometry.Scheme.Hom

end
