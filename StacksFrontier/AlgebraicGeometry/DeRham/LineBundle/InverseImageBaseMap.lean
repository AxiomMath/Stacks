module

public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.GradedDifferential

/-!
# The inverse-image ringed spaces of a composite, and the projection between them

Let `(X, 𝒪_X)` be a ringed space and let `j : W ⟶ Z` and `i : Z ⟶ X` be continuous maps. The two
inverse-image ringed spaces `(W, (j ≫ i)^{-1}𝒪_X)` and `(Z, i^{-1}𝒪_X)` are related by a
canonical morphism over `j`, whose structure datum

`i^{-1}𝒪_X ⟶ j_*((j ≫ i)^{-1}𝒪_X)`

is the unit of the inverse-image/direct-image adjunction for `j`, followed by the direct image of
the identification `(j ≫ i)^{-1}𝒪_X ≅ j^{-1}(i^{-1}𝒪_X)` of [Stacks, Tag 008I].

For a line bundle this is the morphism that the pushforward of the de Rham complex of `L^⋆` to
`X` has to be taken along: the de Rham complex of `L^⋆ ⟶ S` is a complex of sheaves of
`(π ≫ f)^{-1}𝒪_S`-modules on `L^⋆`, and direct image along this morphism carries it to a complex
of sheaves of `f^{-1}𝒪_S`-modules on `X`, which is the category the weight-zero complex
`Ω^•_{L^⋆/S, 0}` of [Stacks, Tag 0FUF] lives in.

## Main definitions

* `AlgebraicGeometry.RingedSpace.inverseImageCompMap`: **the canonical morphism
  `(W, (j ≫ i)^{-1}𝒪_X) ⟶ (Z, i^{-1}𝒪_X)`** over `j`.
* `Stacks.LineBundle.Situation.laurentInverseImageBaseMap`: **its instance for the punctured line
  bundle**, the morphism `(L^⋆, (π ≫ f)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)` over the projection `π`.

## Main results

* `AlgebraicGeometry.RingedSpace.inverseImageCompMap_base` and
  `AlgebraicGeometry.RingedSpace.inverseImageCompMap_c`: its underlying continuous map is `j` and
  its structure datum is the composite above, both by definition.

## Implementation notes

The identification of the pullback along a composite is `sheafPullbackCompIso`, in the form
`TopCat.Sheaf.pullback A (j ≫ i) ≅ pullback A i ⋙ pullback A j` obtained from uniqueness of left
adjoints against the strict composition isomorphism for the direct image; only its `inv` at `𝒪_X`
enters the construction.

A morphism of `AlgebraicGeometry.RingedSpace` is a morphism of the induced category, so it is
built with `CategoryTheory.InducedCategory.homMk` from a `base` and a `c`, as
`AlgebraicGeometry.RingedSpace.inverseImageProjection` is.

## References

* [Stacks Project, Tag 008I](https://stacks.math.columbia.edu/tag/008I)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u}) {W Z : TopCat.{u}} (j : W ⟶ Z) (i : Z ⟶ X.carrier)

/-- **The canonical morphism of inverse-image ringed spaces
`(W, (j ≫ i)^{-1}𝒪_X) ⟶ (Z, i^{-1}𝒪_X)`** over `j`. Its structure datum is the unit of the
inverse-image/direct-image adjunction for `j` at `i^{-1}𝒪_X`, followed by the direct image of the
identification `(j ≫ i)^{-1}𝒪_X ≅ j^{-1}(i^{-1}𝒪_X)` of [Stacks, Tag 008I]. -/
def inverseImageCompMap : inverseImage X (j ≫ i) ⟶ inverseImage X i :=
  InducedCategory.homMk
    { base := j
      c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).unit.app
              ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf) ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} j).map
              ((sheafPullbackCompIso j i CommRingCat.{u}).inv.app X.sheaf)).hom }

/-- The underlying continuous map of `inverseImageCompMap X j i` is `j`. -/
@[simp]
theorem inverseImageCompMap_base : (inverseImageCompMap X j i).hom.base = j := rfl

/-- The structure datum of `inverseImageCompMap X j i` is the unit of the
inverse-image/direct-image adjunction for `j` at `i^{-1}𝒪_X`, followed by the direct image of the
inverse of `sheafPullbackCompIso j i` at `𝒪_X`. -/
@[simp]
theorem inverseImageCompMap_c :
    (inverseImageCompMap X j i).hom.c =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).unit.app
            ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf) ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} j).map
            ((sheafPullbackCompIso j i CommRingCat.{u}).inv.app X.sheaf)).hom :=
  rfl

end AlgebraicGeometry.RingedSpace

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The morphism of ringed spaces `(L^⋆, (π ≫ f)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)`** over the
projection `π : L^⋆ ⟶ X` of a line bundle, namely `inverseImageCompMap` for `π` and `f`. -/
def Situation.laurentInverseImageBaseMap :
    Stacks.DeRhamDirectImage.inverseImageBase D.laurentToBase ⟶
      Stacks.DeRhamDirectImage.inverseImageBase D.f :=
  AlgebraicGeometry.RingedSpace.inverseImageCompMap D.S.toRingedSpace
    D.laurentSpectrumToBase.base D.f.base

/-- The underlying continuous map is that of the projection `π : L^⋆ ⟶ X`. -/
@[simp]
theorem Situation.laurentInverseImageBaseMap_base :
    D.laurentInverseImageBaseMap.hom.base = D.laurentSpectrumToBase.base :=
  rfl

end Stacks.LineBundle

end
