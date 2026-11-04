module

public import StacksFrontier.AlgebraicGeometry.SegreProdIso.ChartPullback
public import StacksFrontier.AlgebraicGeometry.SegreChartProduct.Prod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Segre projection to the product is an isomorphism, and Tag 01WD

This file closes Stacks Tag 01WD.  `StacksFrontier/AlgebraicGeometry/SegreChartProduct/Prod.lean`
reduced the tag to the single statement that the Segre projection
`Stacks.AlgebraicGeometry.SegreGlue.segreProd` is an isomorphism over each product open
`D₊(x_i) × D₊(y_j)` of the target; this file proves that statement.

The argument compares two fibre products of one cospan:

* the product open `D₊(x_i) × D₊(y_j)` of the target *is* the fibre product of `D₊(x_i)` and
  `D₊(y_j)`.  That is `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`: an open of a fibre product
  cut out by one open of each factor is the fibre product of those two opens.  The base of the
  given square is the terminal scheme and the open used there is the whole of it, so the cospan is
  the pair of structure morphisms restricted to the two standard opens.

* the standard chart `D₊(x_i y_j)` of the source, which is the inverse image of that product open
  by `Stacks.AlgebraicGeometry.SegreChartProduct.segreProd_preimage_segreProdTargetOpen`, is the
  same fibre product, with the two glued Segre projections as its projections.  That is
  `Stacks.AlgebraicGeometry.SegreProdIso.isPullback_chartProj`, transported to the preimage and to
  this cospan; the transport of the cospan is free because its target is terminal.

Two fibre products of the same cospan are canonically isomorphic, compatibly with the two
projections.  Composing with the open immersion of the product open into the target and applying
`CategoryTheory.Limits.pullback.hom_ext` identifies that canonical isomorphism with the restricted
Segre projection, which is therefore an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.SegreProdIso.isIso_segreProd_restrict`: the Segre projection restricted
  to a product open is an isomorphism.  This is the one statement
  `StacksFrontier/AlgebraicGeometry/SegreChartProduct/Prod.lean` was missing.

* `Stacks.AlgebraicGeometry.SegreProdIso.isIso_segreProd`: the Segre projection is an isomorphism.

* `Stacks.AlgebraicGeometry.SegreProdIso.absoluteSegre`: the absolute Segre embedding.

* `Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding`: **Stacks Tag 01WD** over an
  arbitrary base scheme.

## Implementation notes

The cospan is taken to be the two restrictions of the structure morphisms to
`(⊤ : (⊤_ Scheme).Opens).toScheme` rather than the morphisms to `⊤_ Scheme` itself, because that
is the form in which `AlgebraicGeometry.Scheme.Hom.isPullback_resLE` delivers it, and it costs
nothing: that open subscheme of the terminal scheme is itself terminal
(`Stacks.AlgebraicGeometry.SegreProdIso.isTerminal_topOpensTerminal`), so the two compatibility
conditions on the cospan that `CategoryTheory.IsPullback.of_iso` asks for are
`CategoryTheory.Limits.IsTerminal.hom_ext`.  No identification of structure morphisms is needed
anywhere, and in particular `AlgebraicGeometry.Proj.awayι_toSpecZero` is not used.

`Stacks.AlgebraicGeometry.SegreChartProduct.segreProdTargetOpen` is a semireducible definition, so
its unfolding is packaged once as
`Stacks.AlgebraicGeometry.SegreProdIso.segreProdTargetOpen_eq_inf` and never performed inside a
`rw`; unfolding it inside a rewrite leaves the goal not type-correct at `implicit` transparency and
every subsequent `rw` fails.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.SegreCharts Stacks.AlgebraicGeometry.SegreProjection
open Stacks.AlgebraicGeometry.SegreChartProduct Stacks.AlgebraicGeometry.SegreGlue

namespace Stacks.AlgebraicGeometry.SegreProdIso

universe u

section Main

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.RingTheory.SegreProduct.gradingGradedAlgebra

variable (n m : ℕ) (p : Fin (n + 1) × Fin (m + 1))

/-! ### The base of the cospan -/

/-- The whole of the terminal scheme, as an open subscheme of it, is terminal. -/
public def isTerminal_topOpensTerminal :
    IsTerminal ((⊤ : (⊤_ Scheme.{u}).Opens).toScheme) :=
  IsTerminal.ofIso terminalIsTerminal (Scheme.topIso (⊤_ Scheme.{u})).symm

/-- A standard open of the first factor lies over the whole of the terminal scheme. -/
public theorem le_preimage_top_left :
    AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.1) ≤
      terminal.from (projectiveSpaceAtUniverse.{u} n) ⁻¹ᵁ ⊤ :=
  le_top.trans_eq (Scheme.Hom.preimage_top _).symm

/-- A standard open of the second factor lies over the whole of the terminal scheme. -/
public theorem le_preimage_top_right :
    AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.2) ≤
      terminal.from (projectiveSpaceAtUniverse.{u} m) ⁻¹ᵁ ⊤ :=
  le_top.trans_eq (Scheme.Hom.preimage_top _).symm

/-- The left leg of the cospan: the structure morphism of the first factor, restricted to a
standard open. -/
public def baseLeft :
    (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.1)).toScheme ⟶ (⊤ : (⊤_ Scheme.{u}).Opens).toScheme :=
  (terminal.from (projectiveSpaceAtUniverse.{u} n)).resLE ⊤
    (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.1))
    (le_preimage_top_left.{u} n m p)

/-- The right leg of the cospan. -/
public def baseRight :
    (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.2)).toScheme ⟶ (⊤ : (⊤_ Scheme.{u}).Opens).toScheme :=
  (terminal.from (projectiveSpaceAtUniverse.{u} m)).resLE ⊤
    (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.2))
    (le_preimage_top_right.{u} n m p)

/-! ### The product open of the target is the fibre product -/

/-- `Stacks.AlgebraicGeometry.SegreChartProduct.segreProdTargetOpen` unfolded once, so that no
later rewrite has to unfold it. -/
public theorem segreProdTargetOpen_eq_inf :
    segreProdTargetOpen.{u} n m p =
      (pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
            (terminal.from (projectiveSpaceAtUniverse.{u} m)) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X p.1)) ⊓
        (pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
            (terminal.from (projectiveSpaceAtUniverse.{u} m)) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X p.2)) :=
  rfl

/-- The product open `D₊(x_i) × D₊(y_j)` of the target lies over `D₊(x_i)`. -/
public theorem targetOpen_le_preimage_left :
    segreProdTargetOpen.{u} n m p ≤
      pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
          (terminal.from (projectiveSpaceAtUniverse.{u} m)) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.1) :=
  (segreProdTargetOpen_eq_inf.{u} n m p).trans_le inf_le_left

/-- The product open `D₊(x_i) × D₊(y_j)` of the target lies over `D₊(y_j)`. -/
public theorem targetOpen_le_preimage_right :
    segreProdTargetOpen.{u} n m p ≤
      pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
          (terminal.from (projectiveSpaceAtUniverse.{u} m)) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.2) :=
  (segreProdTargetOpen_eq_inf.{u} n m p).trans_le inf_le_right

/-- The first projection of the product open `D₊(x_i) × D₊(y_j)` of the target. -/
public def targetProjLeft :
    (segreProdTargetOpen.{u} n m p).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.1)).toScheme :=
  (pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} m))).resLE
    (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.1))
    (segreProdTargetOpen.{u} n m p) (targetOpen_le_preimage_left.{u} n m p)

/-- The second projection of the product open `D₊(x_i) × D₊(y_j)` of the target. -/
public def targetProjRight :
    (segreProdTargetOpen.{u} n m p).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.2)).toScheme :=
  (pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} m))).resLE
    (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.2))
    (segreProdTargetOpen.{u} n m p) (targetOpen_le_preimage_right.{u} n m p)

/-- The first projection of the product open is the first projection of the target. -/
public theorem targetProjLeft_ι :
    targetProjLeft.{u} n m p ≫
        (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.1)).ι =
      (segreProdTargetOpen.{u} n m p).ι ≫
        pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
          (terminal.from (projectiveSpaceAtUniverse.{u} m)) :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The second projection of the product open is the second projection of the target. -/
public theorem targetProjRight_ι :
    targetProjRight.{u} n m p ≫
        (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.2)).ι =
      (segreProdTargetOpen.{u} n m p).ι ≫
        pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
          (terminal.from (projectiveSpaceAtUniverse.{u} m)) :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The product open of the target is the product of the two standard opens.** -/
public theorem isPullback_targetProj :
    IsPullback (targetProjLeft.{u} n m p) (targetProjRight.{u} n m p)
      (baseLeft.{u} n m p) (baseRight.{u} n m p) :=
  Scheme.Hom.isPullback_resLE
    (IsPullback.of_hasPullback (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} m)))
    (le_preimage_top_right.{u} n m p) (le_preimage_top_left.{u} n m p)
    (segreProdTargetOpen_eq_inf.{u} n m p)

/-! ### The inverse image of the product open is the fibre product -/

/-- The first glued Segre projection on the inverse image of the product open, which is the
standard chart `D₊(x_i y_j)`. -/
public def preimageProjLeft :
    (segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.1)).toScheme :=
  (Scheme.isoOfEq _ (segreProd_preimage_segreProdTargetOpen.{u} n m p)).hom ≫
    chartProjLeft.{u} n m p

/-- The second glued Segre projection on the inverse image of the product open. -/
public def preimageProjRight :
    (segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.2)).toScheme :=
  (Scheme.isoOfEq _ (segreProd_preimage_segreProdTargetOpen.{u} n m p)).hom ≫
    chartProjRight.{u} n m p

/-- The first projection on the inverse image of the product open is the glued Segre
projection. -/
public theorem preimageProjLeft_ι :
    preimageProjLeft.{u} n m p ≫
        (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.1)).ι =
      (segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p).ι ≫
        projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => (Scheme.isoOfEq _
            (segreProd_preimage_segreProdTargetOpen.{u} n m p)).hom ≫ k)
          (chartProjLeft_ι.{u} n m p)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
          (Scheme.isoOfEq_hom_ι _
            (segreProd_preimage_segreProdTargetOpen.{u} n m p)))))

/-- The second projection on the inverse image of the product open is the glued Segre
projection. -/
public theorem preimageProjRight_ι :
    preimageProjRight.{u} n m p ≫
        (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.2)).ι =
      (segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p).ι ≫
        projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => (Scheme.isoOfEq _
            (segreProd_preimage_segreProdTargetOpen.{u} n m p)).hom ≫ k)
          (chartProjRight_ι.{u} n m p)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
          (Scheme.isoOfEq_hom_ι _
            (segreProd_preimage_segreProdTargetOpen.{u} n m p)))))

/-- **The inverse image of the product open is the product of the two standard opens**, by
`Stacks.AlgebraicGeometry.SegreProdIso.isPullback_chartProj` transported along
`Stacks.AlgebraicGeometry.SegreChartProduct.segreProd_preimage_segreProdTargetOpen`. -/
public theorem isPullback_preimageProj :
    IsPullback (preimageProjLeft.{u} n m p) (preimageProjRight.{u} n m p)
      (baseLeft.{u} n m p) (baseRight.{u} n m p) :=
  (isPullback_chartProj.{u} n m p).of_iso
    (Scheme.isoOfEq _ (segreProd_preimage_segreProdTargetOpen.{u} n m p)).symm
    (Iso.refl _) (Iso.refl _) (Scheme.topIso (⊤_ Scheme.{u})).symm
    ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
    ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
    (isTerminal_topOpensTerminal.hom_ext _ _) (isTerminal_topOpensTerminal.hom_ext _ _)

/-! ### The restricted Segre projection is an isomorphism -/

/-- The canonical comparison of the two fibre-product descriptions: the inverse image of the
product open and the product open itself. -/
public def chartIsoTargetOpen :
    (segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p).toScheme ≅
      (segreProdTargetOpen.{u} n m p).toScheme :=
  IsPullback.isoIsPullback _ _ (isPullback_preimageProj.{u} n m p)
    (isPullback_targetProj.{u} n m p)

/-- The comparison isomorphism `chartIsoTargetOpen` followed by the first projection of the
product open is the first glued Segre projection. -/
public theorem chartIsoTargetOpen_hom_targetProjLeft :
    (chartIsoTargetOpen.{u} n m p).hom ≫ targetProjLeft.{u} n m p =
      preimageProjLeft.{u} n m p :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_preimageProj.{u} n m p)
    (isPullback_targetProj.{u} n m p)

/-- The comparison isomorphism `chartIsoTargetOpen` followed by the second projection of the
product open is the second glued Segre projection. -/
public theorem chartIsoTargetOpen_hom_targetProjRight :
    (chartIsoTargetOpen.{u} n m p).hom ≫ targetProjRight.{u} n m p =
      preimageProjRight.{u} n m p :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_preimageProj.{u} n m p)
    (isPullback_targetProj.{u} n m p)

/-- The comparison isomorphism is the Segre projection on the inverse image of the product
open. -/
public theorem chartIsoTargetOpen_hom_ι :
    (chartIsoTargetOpen.{u} n m p).hom ≫ (segreProdTargetOpen.{u} n m p).ι =
      (segreProd.{u} n m ⁻¹ᵁ segreProdTargetOpen.{u} n m p).ι ≫ segreProd.{u} n m := by
  refine pullback.hom_ext ?_ ?_
  · erw [Category.assoc, ← targetProjLeft_ι, ← Category.assoc,
      chartIsoTargetOpen_hom_targetProjLeft, preimageProjLeft_ι, Category.assoc, segreProd_fst]
    rfl
  · erw [Category.assoc, ← targetProjRight_ι, ← Category.assoc,
      chartIsoTargetOpen_hom_targetProjRight, preimageProjRight_ι, Category.assoc, segreProd_snd]
    rfl

/-- **The one statement Tag 01WD was missing.**  The Segre projection restricted to a product open
`D₊(x_i) × D₊(y_j)` of the target is an isomorphism.

Both the source and the target of the restricted morphism are the fibre product of `D₊(x_i)` and
`D₊(y_j)`, compatibly with the two projections, so the restricted morphism is the canonical
comparison of two fibre products of one cospan. -/
public theorem isIso_segreProd_restrict :
    IsIso (segreProd.{u} n m ∣_ segreProdTargetOpen.{u} n m p) := by
  have heq : segreProd.{u} n m ∣_ segreProdTargetOpen.{u} n m p =
      (chartIsoTargetOpen.{u} n m p).hom := by
    rw [← cancel_mono (segreProdTargetOpen.{u} n m p).ι, morphismRestrict_ι,
      chartIsoTargetOpen_hom_ι]
  rw [heq]
  infer_instance

/-! ### Tag 01WD -/

/-- **The Segre projection to the product is an isomorphism.** -/
public theorem isIso_segreProd : IsIso (segreProd.{u} n m) :=
  isIso_segreProd_of_restrict n m (isIso_segreProd_restrict.{u} n m)

/-- **The absolute Segre embedding.** -/
public theorem absoluteSegre : SegreEmbedding.AbsoluteSegre.{u} n m :=
  absoluteSegre_of_isIso_segreProd n m (isIso_segreProd.{u} n m)

/-- **Stacks Tag 01WD.**  Over an arbitrary base scheme `S` the product `ℙⁿ_S ×_S ℙᵐ_S` admits a
closed immersion into `ℙ^{nm+n+m}_S` over `S`. -/
@[stacks 01WD, ega "II 4.3.3"]
public theorem exists_segreEmbedding (S : Scheme.{u}) :
    ∃ f : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion f ∧
        f ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
          pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
            ((projectiveSpaceOver n S) ↘ S) :=
  exists_segreEmbedding_of_isIso_segreProd n m S (isIso_segreProd.{u} n m)

end Main

end Stacks.AlgebraicGeometry.SegreProdIso

end
