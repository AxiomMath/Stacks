module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

/-!
# The canonical morphism from the spectrum of the henselian local ring at a point

Let `X` be an algebraic space over `S`, let `x ∈ |X|` and let `(W, w) → (X, x)` be an
elementary étale neighborhood.  The henselian local ring `𝒪^h_{X, x}` of Stacks 0BGW is a
henselization of the local ring `𝒪_{W, w}` by Stacks 0EMY, so for any henselization `R` of
`𝒪_{W, w}` which belongs to the chosen big site there is a canonical morphism

`c_x : Spec(R) = Spec(𝒪^h_{X, x}) ⟶ X`,

namely the spectrum of `𝒪_{W, w} → R` followed by `Spec(𝒪_{W, w}) → W → X`.  This file
constructs it and identifies what it does on points: the closed point of `Spec(R)` lies over
`x`, and the morphism factors through the chart `W → X` by construction.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.specToScheme` is the morphism of
  schemes `Spec(R) ⟶ W`, and
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.henselianObj` is `Spec(R)` as an object
  of the chosen big site over `S`, with
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSchemeHom` the morphism of objects of
  the site and `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.henselianSpace` the
  algebraic space it represents.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom` is the canonical morphism
  `c_x : Spec(𝒪^h_{X, x}) ⟶ X` of algebraic spaces over the base.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.henselianClosedPoint` is the closed
  point `𝔪^h_x` of `Spec(𝒪^h_{X, x})`, as a point of the algebraic space that spectrum
  represents.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom_hom`: the morphism `c_x`
  factors through the chart `W → X`, which is the compatibility of `c_x` with the chart map.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.specToScheme_closedPoint`: the
  morphism `Spec(R) ⟶ W` carries the closed point of `Spec(R)` to the distinguished point `w`.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.pointsMap_toSpaceHom_henselianClosedPoint`:
  the morphism `c_x` carries `𝔪^h_x` to `x`.  Together with the factorization through the
  chart this is what pins `c_x` down.

## Implementation notes

The henselian local ring `AlgebraicGeometry.Space.henselianLocalRing` of Stacks 0BGW is a
`CommRingCat.{u + 1}`, because it is a colimit over the category of elementary étale
neighborhoods, whose objects form a `Type (u + 1)`.  Its spectrum is therefore a
`Scheme.{u + 1}` and is *not* an object of the big fppf site over `S`, which is built from
`Scheme.{u}`; so `c_x` cannot be formed from `henselianLocalRing` itself.  It is formed here
instead from an arbitrary henselization `R` in `Type u` of the Zariski local ring of a chosen
elementary étale neighborhood at its distinguished point, carried as a parameter together with
its containment in the site, exactly as
`AlgebraicGeometry.Space.ClosedPointNeighborhood.toSpaceHom` does at a closed point.  That
this is no loss is `AlgebraicGeometry.Space.henselianLocalRing_isHenselization`: the henselian
local ring of the space is itself such a henselization, so `R` and `𝒪^h_{X, x}` are
isomorphic as henselizations of `𝒪_{W, w}` and `Spec(R)` deserves the name
`Spec(𝒪^h_{X, x})`.

Only algebraicity of the space is used.  Decency enters nowhere: it is what makes elementary
étale neighborhoods exist at all, but one is supplied here as a parameter rather than
produced from the space.

## References

* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace ElementaryEtaleNeighborhood

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {x : points B S hS F} (U : ElementaryEtaleNeighborhood B S hS F hF x)

section Henselian

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra (U.scheme.left.1.presheaf.stalk U.point) R]
  [IsLocalRing.IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
    (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- The canonical morphism of schemes `Spec(R) ⟶ W`: the spectrum of the henselization maps to
the spectrum of the local ring of `W` at `w`, which maps to `W`. -/
def specToScheme : Spec (.of R) ⟶ U.scheme.left.1 :=
  Spec.map (CommRingCat.ofHom (algebraMap (U.scheme.left.1.presheaf.stalk U.point) R)) ≫
    U.scheme.left.1.fromSpecStalk U.point

/-- `Spec(R) = Spec(𝒪^h_{X, x})`, as an object of the big fppf site over `S`. -/
def henselianObj : BigFppfOver B S hS :=
  Over.mk (⟨U.specToScheme R ≫ U.scheme.hom.1⟩ : B.obj hR ⟶ B.obj hS)

/-- The canonical morphism `Spec(R) ⟶ W` of objects of the site. -/
def toSchemeHom : U.henselianObj R hR ⟶ U.scheme :=
  Over.homMk ⟨U.specToScheme R⟩ rfl

omit [IsLocalRing R]
  [IsLocalRing.IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
    (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point)) R] in
/-- The underlying morphism of schemes of the canonical morphism `Spec(R) ⟶ W` of objects of
the site is `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.specToScheme`. -/
@[simp]
theorem toScheme_map_toSchemeHom :
    (BigFppfOver.toScheme B S hS).map (U.toSchemeHom R hR) = U.specToScheme R := rfl

/-- `Spec(R) = Spec(𝒪^h_{X, x})`, as an algebraic space over the base. -/
def henselianSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (U.henselianObj R hR),
    isAlgebraicSpace_yoneda B S hS (U.henselianObj R hR)⟩

/-- **The canonical morphism `c_x : Spec(𝒪^h_{X, x}) ⟶ X`** of algebraic spaces over the
base, at a point `x` of an algebraic space equipped with an elementary étale neighborhood.

This is the geometric half of Stacks 0ENK, at an arbitrary point rather than only at the
generic point of a prime divisor. -/
def toSpaceHom : U.henselianSpace R hR ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (yoneda.map (U.toSchemeHom R hR) ≫ U.toSpace)

omit [IsLocalRing R]
  [IsLocalRing.IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
    (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point)) R] in
/-- **The canonical morphism `c_x` factors through the chart.** The morphism of presheaves
underlying `c_x` is the morphism `Spec(R) ⟶ W` of the site followed by the structure morphism
`W ⟶ X` of the neighborhood. -/
theorem toSpaceHom_hom :
    (U.toSpaceHom R hR).hom = yoneda.map (U.toSchemeHom R hR) ≫ U.toSpace := rfl

/-- The closed point `𝔪^h_x` of `Spec(𝒪^h_{X, x})`, as a point of the algebraic space that
spectrum represents. -/
def henselianClosedPoint : points B S hS (U.henselianSpace R hR).obj :=
  presheafPoint B S hS (U.henselianObj R hR) (IsLocalRing.closedPoint R)
    (B.residueField_spec_contains (U.henselianObj R hR).left.property
      (IsLocalRing.closedPoint R))

omit [IsLocalRing.IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
  (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point)) R] in
/-- The scheme point underlying `𝔪^h_x` is the closed point of `Spec(R)`. -/
theorem pointsToScheme_henselianClosedPoint :
    pointsToScheme B S hS (U.henselianObj R hR) (U.henselianClosedPoint R hR) =
      IsLocalRing.closedPoint R :=
  pointsToScheme_presheafPoint B S hS _ _ _

/-- **What `c_x` does on points, read on the chart.** The morphism `Spec(R) ⟶ W` carries the
closed point of `Spec(R)` to the distinguished point `w` of the neighborhood: the structure
map of a henselization is local, so it carries the closed point to the closed point, and
`Spec(𝒪_{W, w}) ⟶ W` carries the closed point to `w`. -/
theorem specToScheme_closedPoint :
    U.specToScheme R (IsLocalRing.closedPoint R) = U.point := by
  have hlocal : IsLocalHom
      (algebraMap (U.scheme.left.1.presheaf.stalk U.point) R) :=
    IsLocalRing.IsHenselization.isLocalHom
      (L := IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  have hspec : (Spec.map (CommRingCat.ofHom
        (algebraMap (U.scheme.left.1.presheaf.stalk U.point) R)))
          (IsLocalRing.closedPoint R) =
      IsLocalRing.closedPoint (U.scheme.left.1.presheaf.stalk U.point) := by
    show PrimeSpectrum.comap _ (IsLocalRing.closedPoint R) = _
    exact IsLocalRing.comap_closedPoint _
  show U.scheme.left.1.fromSpecStalk U.point
      ((Spec.map (CommRingCat.ofHom
        (algebraMap (U.scheme.left.1.presheaf.stalk U.point) R)))
          (IsLocalRing.closedPoint R)) = U.point
  rw [hspec]
  exact Scheme.fromSpecStalk_closedPoint

/-- The closed point `𝔪^h_x` of `Spec(𝒪^h_{X, x})` lies over the distinguished point of the
neighborhood under `Spec(R) ⟶ W`. -/
theorem pointsMap_toSchemeHom_henselianClosedPoint :
    pointsMap B S hS (U.henselianSpace R hR).obj
        (yoneda.map (U.toSchemeHom R hR)) (U.henselianClosedPoint R hR) =
      presheafPoint B S hS U.scheme U.point U.residueField_contained := by
  refine injective_pointsToScheme B S hS U.scheme ?_
  have h1 : pointsToScheme B S hS U.scheme
      (pointsMap B S hS (U.henselianSpace R hR).obj (yoneda.map (U.toSchemeHom R hR))
        (U.henselianClosedPoint R hR)) =
      U.specToScheme R (pointsToScheme B S hS (U.henselianObj R hR)
        (U.henselianClosedPoint R hR)) :=
    pointsToScheme_pointsMap B S hS (U.toSchemeHom R hR) (U.henselianClosedPoint R hR)
  rw [h1, U.pointsToScheme_henselianClosedPoint R hR, pointsToScheme_presheafPoint]
  exact U.specToScheme_closedPoint R

/-- **The canonical morphism `c_x` carries the closed point of `Spec(𝒪^h_{X, x})` to `x`.**

Together with
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom_hom`, the factorization
through the chart, this is what pins `c_x` down. -/
theorem pointsMap_toSpaceHom_henselianClosedPoint :
    pointsMap B S hS (U.henselianSpace R hR).obj (U.toSpaceHom R hR).hom
        (U.henselianClosedPoint R hR) = x := by
  have hcomp : pointsMap B S hS (U.henselianSpace R hR).obj (U.toSpaceHom R hR).hom
      (U.henselianClosedPoint R hR) =
      pointsMap B S hS (yoneda.obj U.scheme) U.toSpace
        (pointsMap B S hS (U.henselianSpace R hR).obj
          (yoneda.map (U.toSchemeHom R hR)) (U.henselianClosedPoint R hR)) :=
    congrFun (pointsMap_comp B S hS (yoneda.obj (U.henselianObj R hR))
      (yoneda.map (U.toSchemeHom R hR)) U.toSpace) (U.henselianClosedPoint R hR)
  rw [hcomp, U.pointsMap_toSchemeHom_henselianClosedPoint R hR]
  exact U.map_point

end Henselian

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
