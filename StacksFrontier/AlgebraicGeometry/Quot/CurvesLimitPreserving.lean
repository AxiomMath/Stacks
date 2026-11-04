module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStrictlyFull

/-!
# Limit preservation for the stack of curves (Stacks 0D55)

The stack of families of curves is limit preserving as soon as the category of finitely
presented, flat and proper families of algebraic spaces is, and the bound on the relative
dimension descends from the vertex of an affine cofiltered cone to a finite stage.

That is the source's proof of Stacks 0D55 verbatim: *using the embedding (0D50), the
description of the image, and the corresponding fact for the finitely presented flat proper
families (Stacks 0D1I), this reduces to the statement that, for an object of the larger
category over a stage whose base change to the limit has relative dimension at most one, the
base change to some later stage already has relative dimension at most one.* The last
statement is Stacks 0D4K; it is carried here as
`AlgebraicGeometry.DescendsRelativeDimensionLEOne`.

The embedding and the full faithfulness that makes the families of curves a strictly full
subcategory are `AlgebraicGeometry.curvesToCartesianProperFlat` and its two companions in
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered`; the transport of limit preservation
along a fully faithful 1-morphism whose image is recognised at a finite stage is
`AlgebraicGeometry.Stack.isLimitPreserving_of_morphismOver`. What this module adds is the
*description of the image*: the image clause
`Deformation.Artin.DescentImage` of that transport, for this particular embedding, is exactly
the descent of the relative-dimension bound.

## Main definitions

* `AlgebraicGeometry.DescendsRelativeDimensionLEOne`: the bound on the relative dimension of
  the structure morphism of a finitely presented flat proper family descends from the vertex
  of an affine cofiltered cone to a finite stage. This is Stacks 0D4K read in the fibred
  category of such families.

## Main results

* `AlgebraicGeometry.descentImage_curvesToCartesianProperFlat`: the image of the embedding
  (0D50) is recognised at a finite stage as soon as the relative-dimension bound descends.
* `AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory`: **Stacks 0D55 reduced to Stacks
  0D1I**, the stack of curves is limit preserving as soon as the finitely presented flat proper
  families are and the relative-dimension bound descends.

## Implementation notes

*Why the image description is this clause and nothing more.* An object of the larger category
is in the image of the embedding exactly when its structure morphism has relative dimension at
most one: a family of curves is a finitely presented, flat and proper family carrying that one
extra condition, and the embedding forgets precisely it. So an object of the fibre over a stage
lies in the image after passing to a later stage exactly when the bound descends to that stage,
and the object produced there is the same object read as a family of curves — no comparison
isomorphism is needed, the two structures having the same underlying data. That is why the
proof below builds the curve family by a structure literal and reuses the very morphism the
descent clause returns.

*Why the ambient fact appears as a hypothesis.* Stacks 0D1I — limit preservation of the
finitely presented flat proper families of algebraic spaces — has no carrier in this library.
It is stated here as the hypothesis `h0D1I`, at the same index universes as the conclusion, so
that the reduction is exactly the source's and nothing of 0D55 beyond 0D1I is left open.

## References

* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0D50](https://stacks.math.columbia.edu/tag/0D50)
* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The bound on the relative dimension descends to a finite stage.** Let `T = lim Tᵢ` be an
affine cofiltered inverse limit in the big fppf site of `Spec(ℤ)`, let `Zi` be a finitely
presented, flat and proper family of algebraic spaces over the stage `Tᵢ`, and let `ZT ⟶ Zi` be
a morphism of such families lying over the cone projection `T ⟶ Tᵢ` — so that `ZT` is the base
change of `Zi` to the limit. If the structure morphism of `ZT` has relative dimension at most
one, then the base change of `Zi` to some later stage already has.

This is **Stacks 0D4K** read in the category of finitely presented flat proper families: it is
the one geometric statement the source's proof of Stacks 0D55 reduces to. -/
def DescendsRelativeDimensionLEOne : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B integerBase hZ) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c) →
    ∀ (i : I) (Zi ZT : CartesianProperFlatSpaces B integerBase hZ) (ε : ZT ⟶ Zi),
    (cartesianProperFlatProjection B integerBase hZ).IsHomLift
        ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ε →
    Space.HasRelativeDimensionLE 1 B integerBase hZ ZT.obj.obj.hom →
    ∃ (k : I) (s : k ⟶ i) (Zk : CartesianProperFlatSpaces B integerBase hZ) (d : Zk ⟶ Zi),
      (cartesianProperFlatProjection B integerBase hZ).IsHomLift
          ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)) d ∧
        Space.HasRelativeDimensionLE 1 B integerBase hZ Zk.obj.obj.hom

/-- The embedding (0D50) of families of curves into finitely presented, flat and proper families
of algebraic spaces, as a 1-morphism over the big fppf site of `Spec(ℤ)` in the sense of
`CategoryTheory.StacksRepresentableCFG.MorphismOver`. -/
def curvesToCartesianProperFlatOver :
    StacksRepresentableCFG.MorphismOver (curvesProjectionOver B hZ)
      (cartesianProperFlatProjection B integerBase hZ) where
  functor := curvesToCartesianProperFlat B hZ
  w := rfl

section Image

attribute [local implicit_reducible] Functor.Fiber

/-- **The image of the embedding (0D50) is recognised at a finite stage.** An object of the
larger category over a stage which, after base change to the vertex, carries a family of curves
is already a family of curves after base change to a later stage.

The image of the embedding consists of the families whose structure morphism has relative
dimension at most one, so this is exactly the descent of that bound. -/
theorem descentImage_curvesToCartesianProperFlat
    (hdesc : DescendsRelativeDimensionLEOne.{u, v, w} B hZ)
    (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B integerBase hZ) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c)) :
    Deformation.Artin.DescentImage (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).mapCone c)
      (curvesToCartesianProperFlatOver B hZ) := by
  intro i x zi ε hε
  obtain ⟨k, s, Zk, d, hd, hdim⟩ :=
    hdesc I D c hc i zi.1 ((curvesToCartesianProperFlat B hZ).obj x.1) ε hε
      x.1.relativeDimensionLE
  refine ⟨k, s, ⟨{ base := Zk.obj.obj.right
                   total := Zk.obj.obj.left
                   toBase := ObjectProperty.homMk Zk.obj.obj.hom
                   flat := Zk.obj.property.2.1
                   proper := Zk.obj.property.2.2
                   finitePresentation := Zk.obj.property.1
                   relativeDimensionLE := hdim }, ?_⟩, d, hd⟩
  exact IsHomLift.domain_eq (cartesianProperFlatProjection B integerBase hZ)
    ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)) d

end Image

/-- **Stacks 0D55, reduced to Stacks 0D1I.** The stack of families of curves over the big fppf
site of `Spec(ℤ)` is limit preserving in the sense of Stacks 07XL, as soon as the category of
finitely presented, flat and proper families of algebraic spaces is and the bound on the
relative dimension descends to a finite stage along an affine cofiltered cone.

This is the source's proof of Stacks 0D55: the embedding (0D50), the description of its image,
and the corresponding fact for the larger category. The hypothesis `h0D1I` is Stacks 0D1I
verbatim at the same index universes as the conclusion; `hdesc` is Stacks 0D4K in the form the
image description needs. -/
theorem isLimitPreserving_curvesFiberedCategory
    (hdesc : DescendsRelativeDimensionLEOne.{u, v, w} B hZ)
    (h0D1I : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u + 1} B integerBase hZ
      (cartesianProperFlatFiberedCategory B integerBase hZ)) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ) :=
  AlgebraicGeometry.Stack.isLimitPreserving_of_morphismOver B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (curvesToCartesianProperFlatOver B hZ)
    (curvesToCartesianProperFlat_full B hZ) (curvesToCartesianProperFlat_faithful B hZ)
    (fun J _ _ E cc hcc => descentImage_curvesToCartesianProperFlat B hZ hdesc J E cc hcc)
    h0D1I

end AlgebraicGeometry

end
