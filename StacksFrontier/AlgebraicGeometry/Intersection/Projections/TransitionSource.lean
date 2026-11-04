module

public import StacksFrontier.AlgebraicGeometry.Constructions.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionBase

/-!
# The source of the parametrisation of the incidence correspondence of Tag 0B1S

The classifying morphism that exhibits the incidence correspondence `T` of Tag 0B1S as the closure
of the image of a product has as its source the product of the base `X × Y` with the affine space
of the parameters `(c, u, u', w, h)` of the bilinear parametrisation
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd`. This file builds that source.

It is **affine space over the base** rather than a product of `X × Y` with an affine space over
`Spec k`, which is the same scheme and a strictly cheaper spelling: Mathlib's
`AlgebraicGeometry.AffineSpace` carries `𝔸(n; S).CanonicallyOver S`, so the projection to the base
is the structure morphism and needs no `pullback` plumbing, and it carries
`IrreducibleSpace 𝔸(n; S)` as an instance for irreducible `S`, so irreducibility of the source
follows from `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_prodOfClosed` with no
product argument at all.

Nothing of affine space is constructed here. Mathlib has the scheme, its structure morphism, its
coordinate functions `AlgebraicGeometry.AffineSpace.coord` — which are the coefficient functions
the parametrisation's coordinates are assembled from — and the universal property
`AlgebraicGeometry.AffineSpace.homOfVector`, by which a morphism into it over the base *is* a
family of global sections, with `AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord` reading a
coordinate back off one. Tag 01M0 is registered against those declarations in
`StacksFrontier.AlgebraicGeometry.Constructions.AffineSpace`.

**Why the parameter factor may be affine.** The affine factor lies in the *source* of the
classifying morphism, not in `T`: the correspondence is a closed subscheme of `X × Y × 𝐏`, and the
properness of its projection to `𝐏` — which is what makes the clause-(2) bad locus closed, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar` — is a statement
about that product and is untouched by the parameters. The alternative, a *projective* parameter
factor, is available because `transitionEnd` is homogeneous of degree three in
`(c, u, u', w, h)`; it is not taken, because the coordinates would then be sections of a degree
`(1, 1, 3)` twist, and the tautological twist calculus of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm` is degree
`(1, 1, 1)`. Keeping the parameters affine keeps the twist at `(1, 1, 1)`, which is what lets
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairTaut` be an abbreviation for it and inherit the
whole calculus unchanged.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionParamIndex`: the index type of the
  parameters `(c, u, u', w, h)`, read off a basis of `V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSource`: the source `X × Y × 𝔸(params)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.tsSource` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tsTarget`: its two projections to `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSourceToSpec`: its structure morphism.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.tsSource_comp_toSpec` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tsTarget_comp_toSpec`: both projections lie over
  `Spec k`. These are the hypotheses `h₁` and `h₂` that the tautological germ calculus asks of a
  pair of projections.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_transitionSource`: the source is
  irreducible when `X` and `Y` are.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The index type of the parameters of the bilinear parametrisation.** The parameters of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd` are a scalar `c`, three vectors
`u, u', w` and an endomorphism `h`, so in a basis of `V` indexed by `Fin (dim V)` the coordinates
are indexed by one point, three copies of the basis, and a square of it. The `ULift` puts the
index type in the universe of `V`, which is where Mathlib's affine space wants it. -/
public abbrev transitionParamIndex : Type u :=
  ULift.{u} (Unit ⊕ Fin (Module.finrank k V) ⊕ Fin (Module.finrank k V) ⊕
    Fin (Module.finrank k V) ⊕ (Fin (Module.finrank k V) × Fin (Module.finrank k V)))

variable (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)

/-- **The source of the parametrisation**: affine space on the parameters over the product of the
two closed subvarieties. -/
public abbrev transitionSource : Scheme.{u} :=
  AffineSpace (transitionParamIndex k V) (prodOfClosed k V X Y hXc hYc)

/-- The projection of the source to `X × Y`, which is the structure morphism of affine space over
that base. -/
public abbrev transitionSourceToBase :
    transitionSource k V X Y hXc hYc ⟶ prodOfClosed k V X Y hXc hYc :=
  transitionSource k V X Y hXc hYc ↘ prodOfClosed k V X Y hXc hYc

/-- The projection of the source to the copy of `𝐏(V)` carrying the point of `X`. -/
public def tsSource : transitionSource k V X Y hXc hYc ⟶ projectiveSpaceOfModule k V :=
  transitionSourceToBase k V X Y hXc hYc ≫
    pullback.fst (closedSubschemeOfToSpec k V X hXc) (closedSubschemeOfToSpec k V Y hYc) ≫
      closedSubschemeOfι k V X hXc

/-- The projection of the source to the copy of `𝐏(V)` carrying the point of `Y`. -/
public def tsTarget : transitionSource k V X Y hXc hYc ⟶ projectiveSpaceOfModule k V :=
  transitionSourceToBase k V X Y hXc hYc ≫
    pullback.snd (closedSubschemeOfToSpec k V X hXc) (closedSubschemeOfToSpec k V Y hYc) ≫
      closedSubschemeOfι k V Y hYc

/-- The structure morphism of the source over the ground field, taken as the composite through
the first projection; the second projection gives the same morphism, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.tsTarget_comp_toSpec`. -/
public def transitionSourceToSpec :
    transitionSource k V X Y hXc hYc ⟶ Spec (CommRingCat.of k) :=
  tsSource k V X Y hXc hYc ≫ projectiveSpaceOfModuleToSpec k V

/-- The source is a scheme over the ground field. -/
public instance over_transitionSource :
    (transitionSource k V X Y hXc hYc).Over (Spec (CommRingCat.of k)) :=
  ⟨transitionSourceToSpec k V X Y hXc hYc⟩

/-- **The first projection lies over `Spec k`** — the hypothesis `h₁` of the tautological germ
calculus, which the structure morphism is defined to make true. -/
public theorem tsSource_comp_toSpec :
    tsSource k V X Y hXc hYc ≫ projectiveSpaceOfModuleToSpec k V =
      transitionSourceToSpec k V X Y hXc hYc := rfl

/-- **The second projection lies over `Spec k`** — the hypothesis `h₂`. The two projections of
the product have the same composite with the structure morphism of `𝐏(V)`, which is the pullback
condition defining the product. -/
public theorem tsTarget_comp_toSpec :
    tsTarget k V X Y hXc hYc ≫ projectiveSpaceOfModuleToSpec k V =
      transitionSourceToSpec k V X Y hXc hYc := by
  have hcond : pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc =
      pullback.snd (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V Y hYc :=
    pullback.condition
  have hbase := congrArg
    (fun m : prodOfClosed k V X Y hXc hYc ⟶ Spec (CommRingCat.of k) =>
      transitionSourceToBase k V X Y hXc hYc ≫ m) hcond
  have hL : tsTarget k V X Y hXc hYc ≫ projectiveSpaceOfModuleToSpec k V =
      transitionSourceToBase k V X Y hXc hYc ≫
        (pullback.snd (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfToSpec k V Y hYc) := by
    simp only [tsTarget, Category.assoc]
    rfl
  have hR : transitionSourceToSpec k V X Y hXc hYc =
      transitionSourceToBase k V X Y hXc hYc ≫
        (pullback.fst (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfToSpec k V X hXc) := by
    simp only [transitionSourceToSpec, tsSource, Category.assoc]
    rfl
  exact hL.trans (hbase.symm.trans hR.symm)

/-- **The source is irreducible** when `X` and `Y` are: affine space over an irreducible base is
irreducible, and the base is
`AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_prodOfClosed`. -/
public theorem irreducibleSpace_transitionSource [IsAlgClosed k] (hXirr : IsIrreducible X)
    (hYirr : IsIrreducible Y) :
    IrreducibleSpace (transitionSource k V X Y hXc hYc) :=
  have : IrreducibleSpace (prodOfClosed k V X Y hXc hYc) :=
    irreducibleSpace_prodOfClosed k V X Y hXc hYc hXirr hYirr
  inferInstance

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
