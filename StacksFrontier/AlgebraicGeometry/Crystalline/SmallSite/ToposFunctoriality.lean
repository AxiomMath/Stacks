module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekExact

/-!
# Functoriality of the small crystalline topos

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes over `ℤ_{(p)}` and let
`f : X ⟶ Y` be a morphism of schemes over the closed fibres `S₀ ⟶ S'₀`, with `p` locally
nilpotent on `X` and on `Y`.  The morphism of small crystalline topoi attached to these data is
the composite

`f_cris = π_Y ∘ f_CRIS ∘ i_X : (X/S)_cris ⟶ (Y/S')_cris`,

where `i_X : (X/S)_cris ⟶ (X/S)_CRIS` and the retraction `π_Y : (Y/S')_CRIS ⟶ (Y/S')_cris` are
the two morphisms of [Stacks, Tag 07IJ] and `f_CRIS` is change of divided power base on the big
crystalline topoi, [Stacks, Tag 07IC].  The retraction `π` has direct image `i^{-1}`, restriction
of a sheaf on the big site to the small one, and inverse image the lower shriek `i_!` along the
inclusion.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation`.

* `CrystallineThickening.lowerShriek` — the functor `i_!`, left adjoint to restriction along the
  inclusion `Cris(X/S) ⥤ CRIS(X/S)`.
* `CrystallineThickening.retractionMorphism` — the retraction `π : (X/S)_CRIS ⟶ (X/S)_cris` as a
  morphism of topoi, [Stacks, Tag 07IJ].
* `crisMorphism` — the morphism of small crystalline topoi `f_cris : (X/S)_cris ⟶ (Y/S')_cris`,
  [Stacks, Tag 07IK].

## Main results

* `CrystallineThickening.retractionMorphism_pushforward` and
  `CrystallineThickening.retractionMorphism_inverseImage` — the direct image of `π` is
  restriction and its inverse image is `i_!`.
* `CrystallineThickening.retractionPushforwardIsoInverseImage` — the formula `π_* = i^{-1}`
  relating the two morphisms of topoi, [Stacks, Tag 07IJ].
* `crisMorphism_pushforward` and `crisMorphism_inverseImage` — the two halves of `f_cris` as the
  displayed composites.
* `CrystallineThickening.retractionMorphism_comp_smallToBigMorphism_inverseImage` and
  `CrystallineThickening.retractionMorphism_comp_smallToBigMorphism_pushforward` — the composite
  `π ∘ i : (X/S)_cris ⟶ (X/S)_cris` is the identity morphism of topoi: both its inverse image and
  its direct image are the identity functor, [Stacks, Tag 07IJ].

## References

* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

namespace CrystallineThickening

/-- The lower shriek `i_!` along the inclusion `Cris(X/S) ⥤ CRIS(X/S)`: the left adjoint of
restriction, which is the inverse image of the retraction `π` of [Stacks, Tag 07IJ]. -/
noncomputable abbrev lowerShriek (S : GlobalCrystallineSituation.{u}) :
    smallTopos S ⥤ topos S :=
  Functor.sheafPullbackConstruction.sheafPullback (ι S) (Type (u + 1))
    (smallTopology S) (topology S)

/-- The retraction `π : (X/S)_CRIS ⟶ (X/S)_cris` as a morphism of topoi: its direct image is
`i^{-1}`, restriction of a sheaf on the big crystalline site to the small one, and its inverse
image is the lower shriek `i_!`, the two being adjoint. -/
@[stacks 07IJ "the retraction π as a morphism of topoi"]
noncomputable def retractionMorphism (S : GlobalCrystallineSituation.{u}) :
    MorphismOfTopoi (topos S) (smallTopos S) where
  pushforward := (ι S).sheafPushforwardContinuous (Type (u + 1)) (smallTopology S) (topology S)
  inverseImage := lowerShriek S
  adj := ιSheafAdjunctionLowerShriek S
  preservesFiniteLimits := preservesFiniteLimits_lowerShriek S

/-- The direct image of the retraction `π` is `i^{-1}`, restriction of a sheaf on the big
crystalline site to the small one. -/
@[simp]
theorem retractionMorphism_pushforward (S : GlobalCrystallineSituation.{u}) :
    (retractionMorphism S).pushforward =
      (ι S).sheafPushforwardContinuous (Type (u + 1)) (smallTopology S) (topology S) :=
  rfl

/-- The inverse image of the retraction `π` is the lower shriek `i_!`. -/
@[simp]
theorem retractionMorphism_inverseImage (S : GlobalCrystallineSituation.{u}) :
    (retractionMorphism S).inverseImage = lowerShriek S :=
  rfl

/-- **`π_* = i^{-1}`**: the direct image of the retraction `π : (X/S)_CRIS ⟶ (X/S)_cris` is
isomorphic to the inverse image of the inclusion morphism of topoi
`i : (X/S)_cris ⟶ (X/S)_CRIS`. -/
@[stacks 07IJ "π_* = i^{-1}, relating the direct image of π to the inverse image of i"]
noncomputable def retractionPushforwardIsoInverseImage (S : GlobalCrystallineSituation.{u}) :
    (retractionMorphism S).pushforward ≅ (smallToBigMorphism S).inverseImage :=
  (inverseImageIsoRestriction S).symm

/-- **The composite `π ∘ i` is the identity, on inverse images**: the inverse image of the
composite `(X/S)_cris ⟶ (X/S)_CRIS ⟶ (X/S)_cris` is isomorphic to the identity functor. -/
@[stacks 07IJ "the composite π ∘ i is the identity: its inverse image is the identity functor"]
noncomputable def retractionMorphism_comp_smallToBigMorphism_inverseImage
    (S : GlobalCrystallineSituation.{u}) : 𝟭 (smallTopos S) ≅
      ((retractionMorphism S).comp (smallToBigMorphism S)).inverseImage :=
  lowerShriekRestrictionIsoId S ≪≫
    Functor.isoWhiskerLeft (lowerShriek S) (inverseImageIsoRestriction S).symm

/-- **The counit `i^{-1}i_*ℱ ⟶ ℱ` of `i^{-1} ⊣ i_*` is an isomorphism.** -/
instance isIso_ιSheafAdjunctionCocontinuous_counit (S : GlobalCrystallineSituation.{u}) :
    IsIso ((ι S).sheafAdjunctionCocontinuous (Type (u + 1))
      (smallTopology S) (topology S)).counit :=
  Functor.isIso_sheafAdjunctionCocontinuous_counit _ _ _ _

/-- **`i^{-1} ∘ i_* = 𝟭`**: restricting the pushforward of a sheaf on `Cris(X/S)` along the
cocontinuous inclusion back to `Cris(X/S)` returns it, the comparison being the counit of
`i^{-1} ⊣ i_*`. -/
noncomputable def directImageRestrictionIsoId (S : GlobalCrystallineSituation.{u}) :
    (ι S).sheafPushforwardCocontinuous (Type (u + 1)) (smallTopology S) (topology S) ⋙
        (ι S).sheafPushforwardContinuous (Type (u + 1)) (smallTopology S) (topology S) ≅
      𝟭 (smallTopos S) :=
  asIso ((ι S).sheafAdjunctionCocontinuous (Type (u + 1)) (smallTopology S) (topology S)).counit

/-- **The composite `π ∘ i` is the identity, on direct images**: the direct image of the
composite `(X/S)_cris ⟶ (X/S)_CRIS ⟶ (X/S)_cris` is isomorphic to the identity functor, by the
counit of `i^{-1} ⊣ i_*`. -/
@[stacks 07IJ "the composite π ∘ i is the identity: its direct image is the identity functor"]
noncomputable def retractionMorphism_comp_smallToBigMorphism_pushforward
    (S : GlobalCrystallineSituation.{u}) :
    ((retractionMorphism S).comp (smallToBigMorphism S)).pushforward ≅ 𝟭 (smallTopos S) :=
  directImageRestrictionIsoId S

end CrystallineThickening

open CrystallineThickening

/-- The morphism of small crystalline topoi `f_cris : (X/S)_cris ⟶ (Y/S')_cris` attached to a
morphism of divided power bases `S ⟶ S'` and a compatible morphism `X ⟶ Y` of schemes over their
closed fibres: the composite `π_Y ∘ f_CRIS ∘ i_X` of the inclusion morphism of topoi for `X/S`,
change of divided power base on the big crystalline topoi, and the retraction for `Y/S'`. -/
@[stacks 07IK "f_cris = π_Y ∘ f_CRIS ∘ i_X"]
noncomputable def crisMorphism (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    MorphismOfTopoi (smallTopos S) (smallTopos S') :=
  (retractionMorphism S').comp
    ((changeBaseMorphism S S' f g h).comp (smallToBigMorphism S))

/-- The direct image of `f_cris` is the composite `i_Y^{-1} ∘ f_{CRIS, *} ∘ i_{X, *}` of the
direct images of its three factors. -/
@[simp]
theorem crisMorphism_pushforward (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisMorphism S S' f g h).pushforward =
      (smallToBigMorphism S).pushforward ⋙ (changeBaseMorphism S S' f g h).pushforward ⋙
        (ι S').sheafPushforwardContinuous (Type (u + 1)) (smallTopology S') (topology S') :=
  rfl

/-- The inverse image of `f_cris` is the composite `i_X^{-1} ∘ f_{CRIS}^{-1} ∘ i_{Y,!}` of the
inverse images of its three factors, taken in the opposite order. -/
@[simp]
theorem crisMorphism_inverseImage (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisMorphism S S' f g h).inverseImage =
      lowerShriek S' ⋙ (changeBaseMorphism S S' f g h).inverseImage ⋙
        (smallToBigMorphism S).inverseImage :=
  rfl

end Crystalline.GlobalCrystallineSituation

end
