module

public import StacksFrontier.AlgebraicGeometry.SegreChartProduct.TargetCover
public import StacksFrontier.AlgebraicGeometry.SegreGlue.Product

/-!
# The Segre projection to the product pulls the product cover back to the chart cover

`Stacks.AlgebraicGeometry.SegreGlue.segreProd` is the morphism Tag 01WD needs to be an
isomorphism.  This file computes its inverse images of the opens of the target that cover it,
namely the products `D₊(x_i) × D₊(y_j)` of standard opens of the two factors: each is pulled back
to the single standard chart `D₊(x_i y_j)` of the Segre product.

## Main results

* `Stacks.AlgebraicGeometry.SegreChartProduct.preimage_pullbackOpens_of_lift`: the generic
  statement, for any morphism into a fibre product of the two projective spaces whose two
  components are the glued Segre projections.

* `Stacks.AlgebraicGeometry.SegreChartProduct.segreProd_preimage_pullbackOpens`: the same for
  `Stacks.AlgebraicGeometry.SegreGlue.segreProd` itself.

## Implementation notes

`Stacks.AlgebraicGeometry.SegreGlue.segreProd` supplies the two gradings in its *body*, so its
type carries no local instance; a statement naming
`Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued` has to supply them again.  Here they are
supplied once and for all as file-local instances, which is legitimate because the two
`GradedAlgebra` definitions `MvPolynomial.gradedAlgebra` and
`Stacks.RingTheory.SegreProduct.gradingGradedAlgebra` are the only candidates for the gradings
concerned and are exactly the ones
`Stacks.AlgebraicGeometry.SegreGlue.segreProd` uses, so the instances found agree with the terms
in its body and `CategoryTheory.Limits.pullback.lift_fst` applies with no transport.

## What is not done

`IsIso (Stacks.AlgebraicGeometry.SegreGlue.segreProd n m)` is still open.  With the present file
and `StacksFrontier/AlgebraicGeometry/SegreChartProduct/Ring.lean` the two halves that
`StacksFrontier/AlgebraicGeometry/SegreGlue/Product.lean` lists are settled as *statements about
the pieces*; what remains is to assemble them, for which three things are still missing:

* that the opens `pullback.fst ⁻¹ᵁ D₊(x_i) ⊓ pullback.snd ⁻¹ᵁ D₊(y_j)` cover
  `AlgebraicGeometry.projectiveSpaceOver m (AlgebraicGeometry.projectiveSpaceAtUniverse n)`;
* that each of them is `Spec` of the tensor product of the two chart rings, which is
  `AlgebraicGeometry.pullbackSpecIso` applied to
  `Stacks.AlgebraicGeometry.SegreChartProduct.segreChartTensorIso_symm_tmul`, and that
  `Stacks.AlgebraicGeometry.SegreGlue.segreProd` restricted to `D₊(x_i y_j)` is the resulting
  isomorphism;
* `CategoryTheory.MorphismProperty.IsLocalAtTarget` for
  `CategoryTheory.MorphismProperty.isomorphisms`, which is
  `AlgebraicGeometry.Scheme.instIsLocalAtTargetIsomorphismsZariskiPrecoverage`.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.SegreProjection Stacks.AlgebraicGeometry.SegreGlue

namespace Stacks.AlgebraicGeometry.SegreChartProduct

universe u v

/-! ### The generic statement -/

section Generic

variable (R : Type u) [CommRing R] (X Y : Type v) [GradedAlgebra (grading R X Y)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)]

/-- **The product cover pulls back to the chart cover.**  If a morphism out of
`AlgebraicGeometry.Proj` of the Segre product into a fibre product of the two projective spaces
has the two glued Segre projections as its components, then the inverse image of the product open
`D₊(x_i) × D₊(y_j)` is the single standard chart `D₊(x_i y_j)`. -/
public theorem preimage_pullbackOpens_of_lift {T : Scheme.{max u v}}
    (a : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule X R) ⟶ T)
    (b : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule Y R) ⟶ T)
    (f : AlgebraicGeometry.Proj (grading R X Y) ⟶ pullback a b)
    (hfst : f ≫ pullback.fst a b = projLeftGlued R X Y)
    (hsnd : f ≫ pullback.snd a b = projRightGlued R X Y) (i : X) (j : Y) :
    f ⁻¹ᵁ ((pullback.fst a b ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule X R) (MvPolynomial.X i)) ⊓
        (pullback.snd a b ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule Y R) (MvPolynomial.X j))) =
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hfst,
    hsnd, preimage_inf_basicOpen_eq R X Y i j]

end Generic

/-! ### The statement for `segreProd` -/

section SegreProd

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.RingTheory.SegreProduct.gradingGradedAlgebra

variable (n m : ℕ)

/-- The first component of `Stacks.AlgebraicGeometry.SegreGlue.segreProd` is the glued Segre
projection to the first factor.  `StacksFrontier/AlgebraicGeometry/SegreGlue/Product.lean` does
not state this because its statement needs the gradings as instances; they are supplied here as
file-local instances. -/
public theorem segreProd_fst :
    segreProd.{u} n m ≫ pullback.fst _ _ =
      projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) :=
  pullback.lift_fst _ _ _

/-- The second component of `Stacks.AlgebraicGeometry.SegreGlue.segreProd` is the glued Segre
projection to the second factor. -/
public theorem segreProd_snd :
    segreProd.{u} n m ≫ pullback.snd _ _ =
      projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) :=
  pullback.lift_snd _ _ _

/-- **The product open of the target.**  The product `D₊(x_i) × D₊(y_j)` of a standard open of
each factor, as an open of the target of `Stacks.AlgebraicGeometry.SegreGlue.segreProd`. -/
public def segreProdTargetOpen (p : Fin (n + 1) × Fin (m + 1)) :
    (projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n)).Opens :=
  (pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
        (terminal.from (projectiveSpaceAtUniverse.{u} m)) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.1)) ⊓
    (pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
        (terminal.from (projectiveSpaceAtUniverse.{u} m)) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.2))

/-- **The product opens cover the target of the Segre projection.** -/
public theorem iSup_segreProdTargetOpen_eq_top :
    (⨆ p : Fin (n + 1) × Fin (m + 1), segreProdTargetOpen.{u} n m p) = ⊤ :=
  iSup_pullbackOpens_eq_top (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1))
    (terminal.from (projectiveSpaceAtUniverse.{u} n))
    (terminal.from (projectiveSpaceAtUniverse.{u} m))

/-- **The inverse image under the Segre projection of a product of standard opens.**  It is the
single standard chart `D₊(x_i y_j)` of the Segre product.  This is the cover-matching half of
`IsIso (Stacks.AlgebraicGeometry.SegreGlue.segreProd n m)`; the chart-level half is
`Stacks.AlgebraicGeometry.SegreChartProduct.segreChartTensorIso_symm_tmul`. -/
public theorem segreProd_preimage_segreProdTargetOpen (p : Fin (n + 1) × Fin (m + 1)) :
    segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p =
      AlgebraicGeometry.Proj.basicOpen (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
        (SegreCharts.genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p) :=
  preimage_pullbackOpens_of_lift (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) _ _
    (segreProd.{u} n m) (segreProd_fst n m) (segreProd_snd n m) p.1 p.2

/-- **Tag 01WD, reduced to a single chart-level statement.**  If the Segre projection restricted
to each product open `D₊(x_i) × D₊(y_j)` of the target is an isomorphism, then it is an
isomorphism, and hence by
`Stacks.AlgebraicGeometry.SegreGlue.exists_segreEmbedding_of_isIso_segreProd` Tag 01WD holds over
every base scheme.

Being an isomorphism is Zariski-local at the target
(`AlgebraicGeometry.Scheme.instIsLocalAtTargetIsomorphismsZariskiPrecoverage`), and the product
opens cover by `Stacks.AlgebraicGeometry.SegreChartProduct.iSup_segreProdTargetOpen_eq_top`.  The
source of the restricted morphism is the standard chart `D₊(x_i y_j)` by
`Stacks.AlgebraicGeometry.SegreChartProduct.segreProd_preimage_segreProdTargetOpen`. -/
public theorem isIso_segreProd_of_restrict
    (h : ∀ p : Fin (n + 1) × Fin (m + 1),
      IsIso (segreProd.{u} n m ∣_ segreProdTargetOpen.{u} n m p)) :
    IsIso (segreProd.{u} n m) :=
  IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (segreProdTargetOpen.{u} n m) (iSup_segreProdTargetOpen_eq_top n m) h

/-- **Tag 01WD from the chart-level statement.**  The composite of
`Stacks.AlgebraicGeometry.SegreChartProduct.isIso_segreProd_of_restrict` with
`Stacks.AlgebraicGeometry.SegreGlue.exists_segreEmbedding_of_isIso_segreProd`: the conclusion is
the statement of Tag 01WD, over an arbitrary base scheme. -/
public theorem exists_segreEmbedding_of_isIso_restrict (S : Scheme.{u})
    (h : ∀ p : Fin (n + 1) × Fin (m + 1),
      IsIso (segreProd.{u} n m ∣_ segreProdTargetOpen.{u} n m p)) :
    ∃ f : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion f ∧
        f ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
          pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
            ((projectiveSpaceOver n S) ↘ S) :=
  exists_segreEmbedding_of_isIso_segreProd n m S (isIso_segreProd_of_restrict n m h)

end SegreProd

end Stacks.AlgebraicGeometry.SegreChartProduct

end
