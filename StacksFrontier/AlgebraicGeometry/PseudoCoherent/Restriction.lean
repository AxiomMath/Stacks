module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Relative

/-!
# Restricting relative pseudo-coherence to an affine open

The locality statements about relative pseudo-coherence (Stacks 09VC, 09VD, 09VE) all compare
the condition "the derived pushforward along some closed immersion into an affine space over the
base is `m`-pseudo-coherent" for a morphism of affine schemes with the same condition for
restrictions of that morphism to affine opens of the source. This file collects the part of that
comparison which is independent of pseudo-coherence itself: the *shape* of the conclusion — a
closed immersion of an affine open of the source into an affine space over the base, factoring
the restricted morphism — always exists.

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_ι_comp`: an affine open `U` of the
  source of a morphism `f` locally of finite type into an affine base admits a closed immersion
  into an affine space over that base factoring `U.ι ≫ f`.
* `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_ι_comp_ι`: the same when the base is
  reached through an affine open of it, which is the shape Stacks 09VD asks for.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom.isPseudoCoherentFrom_Q`: an object
  of the derived category represented by an `m`-pseudo-coherent complex is `m`-pseudo-coherent.

## Implementation notes

`AlgebraicGeometry.exists_isClosedImmersion_affineSpace` already produces a closed immersion into
an affine space over an affine base for a morphism of affine schemes locally of finite type, so
the two existence statements here are that lemma applied to `U.ι ≫ f`; what has to be supplied is
that `U.ι ≫ f` is again locally of finite type, which holds because an open immersion is and the
property is stable under composition, and that the scheme underlying an affine open is affine.
Both existence statements are stated over an *affine* base rather than for
`AlgebraicGeometry.Scheme.Hom.resLE`, because that is the form in which the source phrases the
local condition after passing to an affine open of the base: the composite
`U.ι ≫ f ≫ V.ι` rather than the restriction `f.resLE V U h`.

What is *not* here is the mathematical content of Stacks 09VC, 09VD and 09VE, namely that
`m`-pseudo-coherence can be transported along a closed immersion whose pushforward of the
structure sheaf is pseudo-coherent (Stacks 09VA). That lemma rests on the theory of
pseudo-coherent complexes on a ringed space — two-out-of-three in a distinguished triangle
(Stacks 08CD), finite-typeness of the top cohomology sheaf (Stacks 08DN) and the comparison with
module-level pseudo-coherence on an affine scheme (Stacks 08E7) — of which this library currently
has only the definitions, in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`.

## References

* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u d

/-- **The remark preceding Stacks 09UI, on an affine open of the source.** For a morphism
`f : X ⟶ S` locally of finite type with `S` affine and an affine open `U` of `X`, the composite
`U.ι ≫ f` factors as a closed immersion of `U` into an affine space over `S` followed by the
structure morphism of that affine space.

This is the shape of the conclusion of Stacks 09VD and of each clause of Stacks 09VE; neither
asks for a *particular* closed immersion, and by Stacks 09VC the choice does not matter. -/
public theorem exists_isClosedImmersion_affineSpace_ι_comp {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] (U : X.affineOpens) :
    ∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = U.1.ι ≫ f :=
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  exists_isClosedImmersion_affineSpace (U.1.ι ≫ f)

/-- **The remark preceding Stacks 09UI, in the form Stacks 09VD consumes.** Let `S` be affine,
let `V` be an affine open of `S`, let `f : X ⟶ V` be locally of finite type and let `U` be an
affine open of `X`. Then `U.ι ≫ f ≫ V.ι`, the restriction of `f` to `U` viewed as a morphism to
`S`, factors as a closed immersion of `U` into an affine space over `S` followed by the structure
morphism of that affine space. -/
public theorem exists_isClosedImmersion_affineSpace_ι_comp_ι {S X : Scheme.{u}} [IsAffine S]
    (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u})) [LocallyOfFiniteType f]
    (U : X.affineOpens) :
    ∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = U.1.ι ≫ f ≫ V.1.ι :=
  exists_isClosedImmersion_affineSpace_ι_comp (f ≫ V.1.ι) U

namespace RingedSpace

variable {X : RingedSpace.{u, u}}
  [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]

/-- An object of the derived category of `𝒪_X`-modules represented by an `m`-pseudo-coherent
complex is `m`-pseudo-coherent. -/
public theorem IsPseudoCoherentComplexFrom.isPseudoCoherentFrom_Q
    {K : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} {m : ℤ}
    (hK : IsPseudoCoherentComplexFrom K m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m :=
  ⟨K, hK, ⟨Iso.refl _⟩⟩

end RingedSpace

end AlgebraicGeometry

end
