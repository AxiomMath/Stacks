module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge

/-!
# Tag 01O4: the multiplication maps between the twists on a relative `Proj` are isomorphisms

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra — Situation 01NN, in the sheaf-level form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` — and suppose that over every
affine open `U` of `S` the graded section ring `Γ(U, A)` is generated in degree one over its
degree-zero part. Tag 01O4 asserts three things about the relative homogeneous spectrum of `A`:
that it represents the functor `F_1`, that every twist `𝒪(n)` is invertible, and that the
multiplication maps induce isomorphisms `𝒪(n) ⊗ 𝒪(m) ≅ 𝒪(n + m)`.

The invertibility clause is
`Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible`. This file proves
the multiplication clause, in all integer degrees, for an arbitrary family of chart
identifications — Tag 01NR's `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` together
with the multiplicativity condition `IsGradedChartIso` — and hence in particular for any
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` and for the canonical twist datum.

## Main results

* `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrict_chart_mulSheaf_eq`: **the comparison
  square.** On an affine chart the multiplication of the glued graded algebra is, after the
  restriction of a tensor product is identified with the tensor product of the restrictions, the
  canonical multiplication map
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` of the absolute twists
  conjugated by the chart identifications.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_restrict_chart_mulSheaf`: hence that
  multiplication restricts to an isomorphism on every affine chart.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_piece`: **Tag 01O4's
  multiplication clause**, for a `ChartData` with `IsGradedChartIso`.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf`: the same for a
  `TwistData`. **This is the declaration the tag is attached to.**
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra` and
  `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible`: the two
  clauses at the canonical twist datum of Tag 01NR, so that both are available for *the* twists
  rather than only for an arbitrary datum.

## The route

Invertibility of a morphism of sheaves of modules is local
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`), the inverse images of the
affine opens of the base cover the relative `Proj`
(`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`), and on such an
inverse image the chart is an isomorphism over the relative `Proj`
(`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`), so the statement reduces to
the restriction along a chart. There the chart identifications turn the multiplication into the
absolute one, which degree-one generation makes an isomorphism by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin`.

The one step with content is the comparison square, because the chart condition
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso` is an identity of *local
sections* while what has to be transported is an isomorphism of *morphisms*. Both sides of the
square are morphisms out of a sheafified tensor product, so they agree as soon as they agree on
the images of the pure tensors of local sections
(`PresheafOfModules.tensorSheaf_hom_ext`), and on such an image each side is computed outright:
the glued side by `SheafOfModules.GradedAlgebra.mulSheaf_unit`, the absolute side by
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct`, and the identification of
the restricted tensor product with the tensor product of the restrictions by
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso_hom_unit_tmul`. That last lemma
is what makes the step affordable: it computes the comparison on a pure tensor over the *image*
open with no transport, which is exactly the shape in which
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection` reads a section of a
restriction.

## The spelling of the multiplication map

The multiplication of a `Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra` is
recorded by `SheafOfModules.GradedAlgebra.mul` as a `SheafOfModules.BilinearMap` on local
sections, which is a structure and not a morphism, so invertibility cannot be asserted of it.
The morphism it descends to is `SheafOfModules.GradedAlgebra.mulSheaf`, the morphism out of the
tensor product sheaf, and that is what the statements below are about. It is stated over
`CategoryTheory.Sheaf.toRingCat` of a sheaf of commutative rings rather than over the ring sheaf
of a ringed site, but the two are equal by `rfl` — this is
`Stacks.CategoryTheory.RingedSite.ringSheaf_ofScheme` and
`Stacks.TensorSheafWorld.structureSheaf_eq` — so `mulSheaf` applies to a
`SchemeGradedAlgebra` with no transport, and its source is on the nose the tensor product sheaf
`Stacks.RingedSpace.tensorSheaf` that the absolute multiplication map is stated over.

## Implementation notes

The chart's open-immersion instance is taken from `ChartData.chart_isOpenImmersion` into the
local context, the same way the fields of `ChartData` take it, so that `ChartData.chartIso` is
applied at the instance its own type was elaborated with.

Because the type of `ChartData.chartIso` carries that instance as a `let`, the instances
`CategoryTheory.Iso.isIso_hom` and `CategoryTheory.Iso.isIso_inv` are not found for its two
maps by instance search, and `CategoryTheory.IsIso.comp_isIso` is therefore not found either;
every invertibility of a composite below is assembled by hand from
`CategoryTheory.IsIso.comp_isIso'`.

No rewrite is performed on an equation between local sections: the sections of a restriction and
the sections over the image open are the same type only after unfolding
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and a `rw` across that boundary exhausts the
heartbeat budget. The proof of the comparison square is accordingly a chain of
`Eq.trans` and `congrArg`, with `AlgebraicGeometry.Scheme.Modules.restrictAppIso` — the identity
isomorphism — left implicit.

## References

* [Stacks Project, Lemma 27.15.6 (Tag 01O4)](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.AffineBaseChange
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjTwistQcoh
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RestrictionSections
open Stacks.RingedSpace
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistMapsInvertible

universe u u₁ v₁ w₁ t₁

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The inverse of an isomorphism of sheaves of modules undoes it on local sections. -/
private theorem inv_val_app_hom_val_app {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{w₁}}
    {M N : SheafOfModules.{t₁} R} (e : M ≅ N) (Z : Cᵒᵖ) (z : M.val.obj Z) :
    e.inv.val.app Z (e.hom.val.app Z z) = z :=
  congrArg (fun k : M ⟶ M => k.val.app Z z) e.hom_inv_id

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}
  {algebra : RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme}

/-- The multiplication of a graded algebra on a relative homogeneous spectrum, restricted to an
affine chart, is the canonical multiplication map of the absolute twists conjugated by the chart
identifications — once the restriction of the tensor product is identified with the tensor
product of the restrictions.

Both sides are morphisms out of a sheafified tensor product, so it suffices to compare them on
the image of a pure tensor of local sections, where the left side is the product of the glued
algebra and the right side is the canonical product of absolute twist sections; the chart
condition identifies the two. -/
theorem restrict_chart_mulSheaf_eq (D : RelativeProjTwists.ChartData A algebra)
    (hD : RelativeProjTwists.IsGradedChartIso D)
    (U : S.Opens) (hU : IsAffineOpen U) (n m : ℤ) :
    letI := D.chart_isOpenImmersion U hU
    (restrictTensorIso ((relativeProj A).chart U hU)
          (algebra.piece n) (algebra.piece m)).inv ≫
        (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
          (SheafOfModules.GradedAlgebra.mulSheaf algebra n m) =
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).presheaf,
            (((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).IsSheaf⟩))).mapIso
          (Iso.prod (D.chartIso U hU n) (D.chartIso U hU m))).hom ≫
        twistMultiplicationMap (A.grading U) n m ≫ (D.chartIso U hU (n + m)).inv := by
  have := D.chart_isOpenImmersion U hU
  refine PresheafOfModules.tensorSheaf_hom_ext
    (F := (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).obj (algebra.piece n))
    (G := (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).obj (algebra.piece m))
    fun V x y => ?_
  have hinv := Eq.trans
    (congrArg ((restrictTensorIso ((relativeProj A).chart U hU)
        (algebra.piece n) (algebra.piece m)).inv.val.app V)
      (restrictTensorIso_hom_unit_tmul ((relativeProj A).chart U hU)
        (algebra.piece n) (algebra.piece m) V.unop x y).symm)
    (inv_val_app_hom_val_app (restrictTensorIso ((relativeProj A).chart U hU)
      (algebra.piece n) (algebra.piece m)) V _)
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ V _) ?_
  refine Eq.trans (congrArg (((Scheme.Modules.restrictFunctor
      ((relativeProj A).chart U hU)).map
    (SheafOfModules.GradedAlgebra.mulSheaf algebra n m)).val.app V) hinv) ?_
  refine Eq.trans (SheafOfModules.GradedAlgebra.mulSheaf_unit algebra n m
    (op ((relativeProj A).chart U hU ''ᵁ V.unop)) x y) ?_
  refine Eq.symm (Eq.trans (SheafOfModules.comp_val_app_apply _ _ V _) ?_)
  refine Eq.trans (congrArg ((twistMultiplicationMap (A.grading U) n m ≫
    (D.chartIso U hU (n + m)).inv).val.app V)
    (tensorSheaf_map_unit_tmul (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace
      (D.chartIso U hU n).hom (D.chartIso U hU m).hom V x y)) ?_
  refine Eq.trans (hD.1 U hU n m V.unop ((D.chartIso U hU n).hom.val.app V x)
    ((D.chartIso U hU m).hom.val.app V y)) ?_
  exact congrArg₂ (fun p q => (algebra.mul n m).app
      (op ((relativeProj A).chart U hU ''ᵁ V.unop)) p q)
    (inv_val_app_hom_val_app (D.chartIso U hU n) V x)
    (inv_val_app_hom_val_app (D.chartIso U hU m) V y)

/-- The multiplication of a graded algebra on a relative homogeneous spectrum restricts to an
isomorphism on every affine chart, as soon as the graded section ring of `A` over every affine
open of the base is generated in degree one over its degree-zero part.

By the comparison square the restricted multiplication is the absolute multiplication map
conjugated by isomorphisms, and degree-one generation makes the absolute map an isomorphism. -/
theorem isIso_restrict_chart_mulSheaf (D : RelativeProjTwists.ChartData A algebra)
    (hD : RelativeProjTwists.IsGradedChartIso D)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (U : S.Opens) (hU : IsAffineOpen U) (n m : ℤ) :
    letI := D.chart_isOpenImmersion U hU
    IsIso ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.mulSheaf algebra n m)) := by
  have := D.chart_isOpenImmersion U hU
  have hcomp : IsIso ((restrictTensorIso ((relativeProj A).chart U hU)
      (algebra.piece n) (algebra.piece m)).inv ≫
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (SheafOfModules.GradedAlgebra.mulSheaf algebra n m)) := by
    rw [restrict_chart_mulSheaf_eq D hD U hU n m]
    exact IsIso.comp_isIso' (Iso.isIso_hom _)
      (IsIso.comp_isIso'
        (isIso_twistMultiplicationMap_of_adjoin (A.grading U) (hgen U hU) n m)
        (Iso.isIso_inv _))
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    (restrictTensorIso ((relativeProj A).chart U hU)
      (algebra.piece n) (algebra.piece m)).inv
    ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.mulSheaf algebra n m))
    (Iso.isIso_inv _) hcomp

/-- **Tag 01O4.** The multiplication maps of a graded algebra on the relative homogeneous
spectrum of `A` which carries Tag 01NR's chart identifications compatibly with the product are
isomorphisms `𝒪(n) ⊗ 𝒪(m) ≅ 𝒪(n + m)`, in all integer degrees, as soon as the graded section
ring of `A` over every affine open of the base is generated in degree one over its degree-zero
part.

Invertibility is local; the inverse images of the affine opens of the base cover the relative
`Proj` and are identified with the charts; on a chart the multiplication is the absolute
multiplication map, which degree-one generation makes an isomorphism. -/
theorem isIso_mulSheaf_piece (D : RelativeProjTwists.ChartData A algebra)
    (hD : RelativeProjTwists.IsGradedChartIso D)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf algebra n m) := by
  refine isIso_of_isIso_restrict (SheafOfModules.GradedAlgebra.mulSheaf algebra n m)
    (fun U : S.affineOpens => (relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens))
    (iSup_toBase_preimage_eq_top (relativeProj A)) ?_
  intro ⟨U, hU⟩
  have := D.chart_isOpenImmersion U hU
  have nat : Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU) ⋙
      Scheme.Modules.restrictFunctor (chartIsoPreimage (A := A) U hU).hom ≅
      Scheme.Modules.restrictFunctor ((relativeProj A).toBase ⁻¹ᵁ U).ι :=
    (Scheme.Modules.restrictFunctorComp (chartIsoPreimage (A := A) U hU).hom
      ((relativeProj A).chart U hU)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (chartIsoPreimage_hom_comp U hU)
  refine (NatIso.isIso_map_iff nat
    (SheafOfModules.GradedAlgebra.mulSheaf algebra n m)).mp ?_
  have := isIso_restrict_chart_mulSheaf D hD hgen U hU n m
  exact Functor.map_isIso
    (Scheme.Modules.restrictFunctor (chartIsoPreimage (A := A) U hU).hom) _

/-- **Tag 01O4.** The multiplication maps between the twists of the twist datum of Tag 01NR on
the relative homogeneous spectrum of a quasi-coherent graded algebra are isomorphisms
`𝒪(n) ⊗ 𝒪(m) ≅ 𝒪(n + m)`, in all integer degrees, when the algebra is generated in degree one
over its degree-zero part.

This is the multiplication clause of the tag; the invertibility clause is
`Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Also carried here: an arbitrary RelativeProjTwists.TwistData A rather than the canonical
--   one; at the canonical datum of Tag 01NR the same conclusion is
--   isIso_mulSheaf_twistDataOfGradedAlgebra, which carries the tag too.
--   Outside the scope of this declaration, but proved elsewhere in this library: the tag's MAIN
--   clause, that X = Proj_S(A) REPRESENTS the functor F_1 of pairs (L, psi) with f^*A_1 -> L
--   surjective, up to strict equivalence. Its carriers are
--   ProjRepresentsF1.pairClassifyingHom_bijective (ProjRepresentsF1/PairFromQuadruple.lean:604)
--   and ProjRepresentsF1.f1Bundle (ProjRepresentsF1/TensorPowerBridgeProof.lean:438), the latter
--   building the whole ProjRepresentsF1.F1Bundle from the degree-one generation alone. All three
--   of the tag's assertions are stated together in TwistMapsInvertible.f1Bundle_and_twists
--   (TwistMapsInvertible/RepresentsAndTwists.lean). The larger structure
--   ProjRepresentsF1.F1Representation (ProjRepresentsF1/Representation.lean) is still
--   unassembled; it adds the field universal_isCanonical identifying the universal pair with the
--   canonical twist pair of a twist datum, which is a pinning against Tag 01NR's twists rather
--   than one of the tag's assertions. The absolute universal property
--   ProjDegreeOneRepresents.existsUnique_classifies (Tag 01NA) is the input the representation
--   descends from.
theorem twistData_isIso_mulSheaf (D : RelativeProjTwists.TwistData A)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf D.algebra n m) :=
  isIso_mulSheaf_piece D.chartData D.isGradedChartIso hgen n m

/-- The multiplication clause of Tag 01O4 at **the** twists: the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which Tag 01NR's existence
assertion produces from the quasi-coherent graded algebra alone, so that no twist datum is
carried as a hypothesis. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Not covered by this carrier, but proved elsewhere in this library: the tag's MAIN clause, that
--   X = Proj_S(A) REPRESENTS the functor F_1 of pairs (L, psi) with f^*A_1 -> L surjective, up to
--   strict equivalence. Its carriers are ProjRepresentsF1.pairClassifyingHom_bijective
--   (ProjRepresentsF1/PairFromQuadruple.lean:604), the bijectivity of the classifying map from
--   strict isomorphism classes to morphisms T -> Proj_S(A) over S, and ProjRepresentsF1.f1Bundle
--   (ProjRepresentsF1/TensorPowerBridgeProof.lean:438), which builds the whole
--   ProjRepresentsF1.F1Bundle -- the universal pair, the representing bijections, their
--   normalisation at the identity, the pullback of classes and its naturality -- from the
--   degree-one generation alone. All three of the tag's assertions are stated together in
--   TwistMapsInvertible.f1Bundle_and_twists (TwistMapsInvertible/RepresentsAndTwists.lean). The
--   larger structure ProjRepresentsF1.F1Representation (ProjRepresentsF1/Representation.lean) is
--   still unassembled; it adds the field universal_isCanonical identifying the universal pair
--   with the canonical twist pair of a twist datum, which is a pinning against Tag 01NR's twists
--   rather than one of the tag's assertions. The absolute universal property
--   ProjDegreeOneRepresents.existsUnique_classifies (Tag 01NA) is the input the representation
--   descends from.
-- Also recorded here rather than in the attribute: The twist datum is not an argument: it is
-- the canonical one Tag 01NR produces from A alone.
theorem isIso_mulSheaf_twistDataOfGradedAlgebra
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf
      (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra n m) :=
  twistData_isIso_mulSheaf (GluedTwistAlgebra.twistDataOfGradedAlgebra A) hgen n m

/-- The invertibility clause of Tag 01O4 at **the** twists: every homogeneous piece of the twist
datum `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` is an invertible
`𝒪`-module, so that no twist datum is carried as a hypothesis. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Not covered by this carrier, but proved elsewhere in this library: the tag's MAIN clause, that
--   X = Proj_S(A) REPRESENTS the functor F_1 of pairs (L, psi) with f^*A_1 -> L surjective, up to
--   strict equivalence. Its carriers are ProjRepresentsF1.pairClassifyingHom_bijective
--   (ProjRepresentsF1/PairFromQuadruple.lean:604), the bijectivity of the classifying map from
--   strict isomorphism classes to morphisms T -> Proj_S(A) over S, and ProjRepresentsF1.f1Bundle
--   (ProjRepresentsF1/TensorPowerBridgeProof.lean:438), which builds the whole
--   ProjRepresentsF1.F1Bundle -- the universal pair, the representing bijections, their
--   normalisation at the identity, the pullback of classes and its naturality -- from the
--   degree-one generation alone. All three of the tag's assertions are stated together in
--   TwistMapsInvertible.f1Bundle_and_twists (TwistMapsInvertible/RepresentsAndTwists.lean). The
--   larger structure ProjRepresentsF1.F1Representation (ProjRepresentsF1/Representation.lean) is
--   still unassembled; it adds the field universal_isCanonical identifying the universal pair
--   with the canonical twist pair of a twist datum, which is a pinning against Tag 01NR's twists
--   rather than one of the tag's assertions. The absolute universal property
--   ProjDegreeOneRepresents.existsUnique_classifies (Tag 01NA) is the input the representation
--   descends from.
-- Also recorded here rather than in the attribute: The twist datum is not an argument: it is
-- the canonical one Tag 01NR produces from A alone.
theorem twistDataOfGradedAlgebra_isInvertible
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
      (relativeProj A).scheme.ringCatSheaf.2
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece n) :=
  twistData_isInvertible (GluedTwistAlgebra.twistDataOfGradedAlgebra A) hgen n

end Stacks.AlgebraicGeometry.TwistMapsInvertible

end
