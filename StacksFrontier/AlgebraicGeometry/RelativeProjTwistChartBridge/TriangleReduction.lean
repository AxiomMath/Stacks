module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTriangle

/-!
# Lemma 01O1's triangle, reduced to an arbitrary comparison of the source

`...RelativeProjTwistChartBridge.TriangleCommutes` of
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTriangle` asks for the
commutativity of [Stacks, Tag 01O1]'s triangle for one *particular* isomorphism of graded
algebras: the recognition comparison
`...RelativeVeroneseTwists.laurentComparisonOfDegreeOpen` built out of a degree-one datum `α`.
That is the shape the existence proof downstream consumes, but it is a bad shape to *produce*: a
caller holding some comparison of the tag's source with `⨁_n ℒ^{⊗ n}` would additionally have to
identify it with the one the recognition theorem builds by its inductive climb through the
degrees.

This file removes that obligation. The identification is automatic.

## Why any solution of the triangle is the recognition comparison

An isomorphism of graded algebras `c : r^*(⨁_n 𝒪(nd)) ≅ ⨁_n ℒ^{⊗ n}` has an inverse, which is a
homomorphism **out of** a Laurent algebra, and a homomorphism out of a Laurent algebra is
determined by its degree-one component
(`...RelativeProjQcohSheaf.laurent_app_eq_of_app_one`). So two isomorphisms of graded algebras
with that source and that target agreeing in degree one agree in every degree: compose the inverse
of one with the other and compare the resulting endomorphism of `⨁_n ℒ^{⊗ n}` with the identity in
degree one, where they agree by construction.

The recognition comparison built out of `α` does agree with `c` in degree one as soon as `α` is
taken to be the degree-one component of `c`, because
`...GradedLaurentRecognition.pieceIso_one_comp_oneIsoL` says the degree-one component of the
recognition comparison is `α` read through the identification `ℒ^{⊗ 1} ≅ ℒ` of [Stacks, Tag
01CU]. The degree-one component of `c` is invertible, so it supplies such an `α`.

This is the asymmetry recorded in the module docstring of `ThetaTriangle`, used in the one
direction in which it is available: *uniqueness* in the `θ`-assertion of Tag 01O1 is degree-one
business, and the comparison of two candidate `θ`s is an instance of it. What remains genuinely
open is the *existence* of any comparison at all.

## Main definitions

* `...RelativeProjTwistChartBridge.degreeOnePieceIso`: the degree-one component of an isomorphism
  of sheaves of graded algebras, as an isomorphism of its degree-one pieces.

## Main results

* `...RelativeProjTwistChartBridge.gradedIso_app_eq_laurentComparisonOfDegreeOpen`: **an
  isomorphism of graded algebras from the tag's source onto `⨁_n ℒ^{⊗ n}` is the recognition
  comparison built out of its own degree-one component**, in every integer degree.
* `...RelativeProjTwistChartBridge.triangleCommutes_of_gradedIso`: **Lemma 01O1's triangle
  commutes as soon as *some* isomorphism of graded algebras makes it commute** — the degree-one
  datum `α` of `TriangleCommutes` need not be produced, and the recognition comparison need not be
  recognised.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {d : ℕ} {f : T ⟶ S}
  (D : TwistData A) (r : T ⟶ (relativeProj A).scheme)
  (P : Quadruple f (situationAlgebra A) (d : ℤ))

/-! ### The degree-one component of an isomorphism of graded algebras -/

/-- **The degree-one component of an isomorphism of sheaves of graded algebras, as an
isomorphism.** Its inverse is the degree-one component of the inverse: the two composites are the
degree-one components of the two composites of the isomorphism, which are identities.

Stated for the source of [Stacks, Tag 01O1]'s `θ` and the Laurent algebra of a quadruple's
invertible module, the only instance used below. -/
def degreeOnePieceIso (c : pullbackTwistVeronese D (d : ℤ) r ≅ laurent P.L) :
    (pullbackTwistVeronese D (d : ℤ) r).piece 1 ≅ (laurent P.L).piece 1 where
  hom := c.hom.app 1
  inv := c.inv.app 1
  hom_inv_id :=
    congrArg (fun φ : pullbackTwistVeronese D (d : ℤ) r ⟶ pullbackTwistVeronese D (d : ℤ) r =>
      φ.app 1) c.hom_inv_id
  inv_hom_id :=
    congrArg (fun φ : laurent P.L ⟶ laurent P.L => φ.app 1) c.inv_hom_id

/-- The degree-one datum that an isomorphism of graded algebras onto `⨁_n ℒ^{⊗ n}` carries: its
degree-one component, read through the identification `ℒ^{⊗ 1} ≅ ℒ` of [Stacks, Tag 01CU]. -/
def degreeOneDatum (c : pullbackTwistVeronese D (d : ℤ) r ≅ laurent P.L) :
    (pullbackTwistVeronese D (d : ℤ) r).piece 1 ≅ P.L :=
  degreeOnePieceIso D r P c ≪≫ P.oneIso

/-! ### Any solution of the triangle is the recognition comparison -/

/-- **An isomorphism of sheaves of graded algebras from the source of [Stacks, Tag 01O1]'s `θ`
onto `⨁_{n ∈ ℤ} ℒ^{⊗ n}` is the recognition comparison built out of its own degree-one
component**, in every integer degree.

The two agree in degree one by `...GradedLaurentRecognition.pieceIso_one_comp_oneIsoL`, which
computes the degree-one component of the recognition comparison as the datum it was built from.
They therefore agree in every degree: the composite of the inverse of `c` with the recognition
comparison is an endomorphism of the Laurent algebra agreeing with the identity in degree one, and
`...RelativeProjQcohSheaf.laurent_app_eq_of_app_one` makes a homomorphism out of a Laurent algebra
a function of its degree-one component. -/
theorem gradedIso_app_eq_laurentComparisonOfDegreeOpen
    (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
    (c : pullbackTwistVeronese D (d : ℤ) r ≅ laurent P.L) (n : ℤ) :
    (laurentComparisonOfDegreeOpen D d r hg (degreeOneDatum D r P c)).hom.app n = c.hom.app n := by
  set ω := laurentComparisonOfDegreeOpen D d r hg (degreeOneDatum D r P c) with hωdef
  have h1 : ω.hom.app 1 = c.hom.app 1 :=
    (Iso.cancel_iso_hom_right _ _ P.oneIso).mp
      (GradedLaurentRecognition.pieceIso_one_comp_oneIsoL _ _ (degreeOneDatum D r P c) _ _)
  have hω : ∀ m : ℤ, (c.inv ≫ ω.hom).app m = (CategoryStruct.id (laurent P.L)).app m := by
    intro m
    refine laurent_app_eq_of_app_one (γ := c.inv ≫ ω.hom)
      (γ' := CategoryStruct.id (laurent P.L)) (e := Iso.refl P.L) ?_ ?_ m
    · change (c.inv.app 1 ≫ ω.hom.app 1) ≫ P.oneIso.hom = P.oneIso.hom ≫ (Iso.refl P.L).hom
      rw [h1, show c.inv.app 1 ≫ c.hom.app 1 = _ from (degreeOnePieceIso D r P c).inv_hom_id,
        Category.id_comp, Iso.refl_hom, Category.comp_id]
    · change (CategoryStruct.id ((laurent P.L).piece 1)) ≫ P.oneIso.hom =
        P.oneIso.hom ≫ (Iso.refl P.L).hom
      rw [Category.id_comp, Iso.refl_hom, Category.comp_id]
  calc ω.hom.app n
      = (c.hom.app n ≫ c.inv.app n) ≫ ω.hom.app n := by
        rw [show c.hom.app n ≫ c.inv.app n =
            CategoryStruct.id ((pullbackTwistVeronese D (d : ℤ) r).piece n) from
          congrArg (fun φ : pullbackTwistVeronese D (d : ℤ) r ⟶ pullbackTwistVeronese D (d : ℤ) r =>
            φ.app n) c.hom_inv_id, Category.id_comp]
    _ = c.hom.app n := (Category.assoc _ _ _).trans
        ((congrArg (c.hom.app n ≫ ·) (hω n)).trans (Category.comp_id _))

/-! ### The triangle from an arbitrary comparison -/

/-- **[Stacks, Tag 01O1]'s triangle commutes as soon as *some* isomorphism of sheaves of graded
algebras makes it commute.** The hypothesis
`...RelativeProjTwistChartBridge.TriangleCommutes` names the recognition comparison and quantifies
a degree-one datum; this produces both from any comparison `c` of the tag's source with
`⨁_{n ∈ ℤ} ℒ^{⊗ n}` solving the triangle, by
`gradedIso_app_eq_laurentComparisonOfDegreeOpen`.

This is the shape in which the triangle should be *proved*: it asks only for an isomorphism of
graded algebras carrying the tag's second leg to the quadruple's `ψ`, with no reference to the
inductive construction of the recognition comparison and no degree-one datum to exhibit. -/
theorem triangleCommutes_of_gradedIso
    (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
    (hr : r ≫ (relativeProj A).toBase = f)
    (c : pullbackTwistVeronese D (d : ℤ) r ≅ laurent P.L)
    (hc : ∀ n : ℤ, D.psiLegVeronese r hr (d : ℤ) n ≫ c.hom.app n = P.twisting.app n) :
    TriangleCommutes D d r hg hr P :=
  ⟨degreeOneDatum D r P c, fun n =>
    (congrArg (fun z => D.psiLegVeronese r hr (d : ℤ) (n : ℤ) ≫ z)
      (gradedIso_app_eq_laurentComparisonOfDegreeOpen D r P hg c (n : ℤ))).trans (hc (n : ℤ))⟩

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
