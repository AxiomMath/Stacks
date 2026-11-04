module

public import StacksFrontier.AlgebraicGeometry.SegreProdIso.AwayGeom
public import StacksFrontier.AlgebraicGeometry.SegreGlue.Glue
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The standard chart of the Segre product is the product of the two standard charts

On the chart `D₊(x_i y_j)` the two glued Segre projections land in the standard opens `D₊(x_i)`
and `D₊(y_j)` of the two factors.  This file produces those two factored morphisms and proves that
they exhibit `D₊(x_i y_j)` as the *product* of `D₊(x_i)` and `D₊(y_j)`, i.e. as the fibre product
over the terminal scheme.

That is the chart-level half of Stacks Tag 01WD.  Its content is entirely ring-theoretic and
already paid for: the three standard opens are affine, with coordinate rings the degree-zero
homogeneous localisations, and
`Stacks.AlgebraicGeometry.SegreChartProduct.segreChartTensorIso_chartMapLeft` together with its
mirror image says that the Segre chart ring is the tensor product of the two chart rings *with the
two chart maps as its structure maps*.  `AlgebraicGeometry.pullbackSpecIso` turns that tensor
product into a fibre product of affine schemes.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreProdIso.chartProjLeft` and
  `Stacks.AlgebraicGeometry.SegreProdIso.chartProjRight`: the two glued Segre projections on the
  chart `D₊(x_i y_j)`, factored through the standard opens of the two factors.

## Main results

* `Stacks.AlgebraicGeometry.SegreProdIso.chartProjLeft_ι` and
  `Stacks.AlgebraicGeometry.SegreProdIso.chartProjRight_ι`: those two morphisms really are the
  glued projections restricted to the chart.

* `Stacks.AlgebraicGeometry.SegreProdIso.isPullback_SpecMap_includeRingHom`:
  `AlgebraicGeometry.pullbackSpecIso` for the two chart rings, read as a pullback square.

* `Stacks.AlgebraicGeometry.SegreProdIso.isPullback_chartProj`: the chart is the product of the two
  standard opens.

## Implementation notes

The base of the fibre product is taken to be the terminal scheme `⊤_ Scheme`, not
`Spec (ULift ℤ)`.  The two are canonically isomorphic by
`AlgebraicGeometry.specULiftZIsTerminal`, and stating the result over `⊤_ Scheme` makes the two
compatibility conditions that `CategoryTheory.IsPullback.of_iso` asks about the *cospan* hold by
`CategoryTheory.Limits.terminal.hom_ext`, with no identification of structure morphisms to check.
In particular `AlgebraicGeometry.Proj.awayι_toSpecZero` is not needed: the degree-zero part of the
grading never has to be identified with the coefficient ring.

Everything is stated for the concrete coefficient ring `ULift ℤ` and the concrete index types
`Fin (n + 1)`, `Fin (m + 1)`, because `AlgebraicGeometry.pullbackSpecIso` needs its three rings in
one universe: at a general index type `X : Type v` the chart rings live in `Type (max u v)` while
the coefficient ring lives in `Type u`.

Both gradings are definitions rather than instances in this development; as in
`StacksFrontier/AlgebraicGeometry/SegreChartProduct/Prod.lean` they are supplied here as
file-local instances, which is legitimate because the two `GradedAlgebra` definitions concerned
are the only candidates and are the ones the glued projections use.

The standard opens are written out rather than abbreviated, because `rw` does not see through a
reducible definition and every step of the comparison is a `rw` against a Mathlib lemma stated
about `AlgebraicGeometry.Proj.basicOpen`.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open HomogeneousLocalization
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.SegreCharts Stacks.AlgebraicGeometry.SegreChartRing
open Stacks.AlgebraicGeometry.PolyChart Stacks.AlgebraicGeometry.SegreProjection
open Stacks.AlgebraicGeometry.SegreChartProduct Stacks.AlgebraicGeometry.SegreGlue

namespace Stacks.AlgebraicGeometry.SegreProdIso

universe u

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.RingTheory.SegreProduct.gradingGradedAlgebra

variable (n m : ℕ) (p : Fin (n + 1) × Fin (m + 1))

/-- **The projection to the first factor on a standard chart.**  The glued Segre projection
`Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued` carries `D₊(x_i y_j)` into `D₊(x_i)`; this is
that morphism of open subschemes, read through the two affine charts as `Spec` of
`Stacks.AlgebraicGeometry.SegreChartProduct.chartMapLeft`. -/
public def chartProjLeft :
    (AlgebraicGeometry.Proj.basicOpen (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
        (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.1)).toScheme :=
  (AlgebraicGeometry.Proj.basicOpenIsoSpec
      (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
      (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)
      (genSub_mem_grading_one (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p) one_pos).hom ≫
    Spec.map (CommRingCat.ofHom
      (chartMapLeft (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2)) ≫
    (AlgebraicGeometry.Proj.basicOpenIsoSpec
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.1)
      (X_mem (ULift.{u} ℤ) (Fin (n + 1)) p.1) one_pos).inv

/-- **The projection to the second factor on a standard chart**, the mirror image of
`Stacks.AlgebraicGeometry.SegreProdIso.chartProjLeft`. -/
public def chartProjRight :
    (AlgebraicGeometry.Proj.basicOpen (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
        (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.2)).toScheme :=
  (AlgebraicGeometry.Proj.basicOpenIsoSpec
      (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
      (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)
      (genSub_mem_grading_one (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p) one_pos).hom ≫
    Spec.map (CommRingCat.ofHom
      (chartMapRight (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2)) ≫
    (AlgebraicGeometry.Proj.basicOpenIsoSpec
      (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.2)
      (X_mem (ULift.{u} ℤ) (Fin (m + 1)) p.2) one_pos).inv

/-- The chart morphism `D₊(g) → Spec B_{(g)} → Spec A_{(f)} → D₊(f)` built from a graded ring
homomorphism `ψ` with `ψ f = g` is the glued morphism `G`, once `G` restricts to `mapAwayHom ψ`. -/
private theorem basicOpenIsoSpec_awayCongr_map_ι {A B : Type u} {σ τ : Type*}
    [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B]
    [AddSubgroupClass τ B] (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) {f : A} {g : B} (hf : f ∈ 𝒜 1) (hg : g ∈ ℬ 1) (hsub : ψ f = g)
    (G : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜)
    (hG : (AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)).ι ≫ G = mapAwayHom 𝒜 ℬ ψ one_pos hf) :
    (AlgebraicGeometry.Proj.basicOpenIsoSpec ℬ g hg one_pos).hom ≫
        Spec.map (CommRingCat.ofHom
          ((awayCongr ℬ hsub).toRingHom.comp (HomogeneousLocalization.Away.map ψ f))) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf one_pos).inv ≫
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι =
      (AlgebraicGeometry.Proj.basicOpen ℬ g).ι ≫ G := by
  have hR : (AlgebraicGeometry.Proj.basicOpen ℬ g).ι ≫ G =
      ((AlgebraicGeometry.Proj ℬ).isoOfEq
          (congrArg (AlgebraicGeometry.Proj.basicOpen ℬ) hsub.symm)).hom ≫
        mapAwayHom 𝒜 ℬ ψ one_pos hf := by
    rw [← hG, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, AlgebraicGeometry.Proj.basicOpenIsoSpec_hom]
  simp only [Category.assoc]
  rw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι, basicOpenToSpec_awayCongr_assoc ℬ hsub, hR,
    mapAwayHom]

/-- **`chartProjLeft` is the glued projection on the chart.** -/
public theorem chartProjLeft_ι :
    chartProjLeft.{u} n m p ≫
        (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.1)).ι =
      (AlgebraicGeometry.Proj.basicOpen (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
          (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)).ι ≫
        projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) :=
  basicOpenIsoSpec_awayCongr_map_ι _ _ _ _ _
    (substLeftGraded_X (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.2 p.1) _
    (ι_projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)

/-- **`chartProjRight` is the glued projection on the chart.** -/
public theorem chartProjRight_ι :
    chartProjRight.{u} n m p ≫
        (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X p.2)).ι =
      (AlgebraicGeometry.Proj.basicOpen (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
          (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)).ι ≫
        projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) :=
  basicOpenIsoSpec_awayCongr_map_ι _ _ _ _ _
    (substRightGraded_X (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2) _
    (ι_projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)

/-! ### The chart is the product of the two standard opens -/

/-- `Spec` of the tensor product of the two chart rings is the fibre product of their `Spec`s over
`Spec (ULift ℤ)`.  This is `AlgebraicGeometry.pullbackSpecIso` read as a pullback square; the
commutativity of the square is free because `Spec (ULift ℤ)` is terminal. -/
public theorem isPullback_SpecMap_includeRingHom :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ULift.{u} ℤ)
        (A := MvPolynomial {k : Fin (n + 1) // k ≠ p.1} (ULift.{u} ℤ))
        (B := MvPolynomial {l : Fin (m + 1) // l ≠ p.2} (ULift.{u} ℤ)))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ULift.{u} ℤ)
        (A := MvPolynomial {k : Fin (n + 1) // k ≠ p.1} (ULift.{u} ℤ))
        (B := MvPolynomial {l : Fin (m + 1) // l ≠ p.2} (ULift.{u} ℤ))).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ)
        (MvPolynomial {k : Fin (n + 1) // k ≠ p.1} (ULift.{u} ℤ)))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ)
        (MvPolynomial {l : Fin (m + 1) // l ≠ p.2} (ULift.{u} ℤ))))) :=
  IsPullback.of_iso_pullback ⟨specULiftZIsTerminal.hom_ext _ _⟩
    (AlgebraicGeometry.pullbackSpecIso (ULift.{u} ℤ)
      (MvPolynomial {k : Fin (n + 1) // k ≠ p.1} (ULift.{u} ℤ))
      (MvPolynomial {l : Fin (m + 1) // l ≠ p.2} (ULift.{u} ℤ))).symm
    (AlgebraicGeometry.pullbackSpecIso_inv_fst _ _ _)
    (AlgebraicGeometry.pullbackSpecIso_inv_snd _ _ _)

/-- **The standard chart of the Segre product is the product of the two standard opens.**  The two
morphisms `Stacks.AlgebraicGeometry.SegreProdIso.chartProjLeft` and
`Stacks.AlgebraicGeometry.SegreProdIso.chartProjRight` exhibit `D₊(x_i y_j)` as the fibre product
of `D₊(x_i)` and `D₊(y_j)` over the terminal scheme. -/
public theorem isPullback_chartProj :
    IsPullback (chartProjLeft.{u} n m p) (chartProjRight.{u} n m p)
      (terminal.from (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.1)).toScheme)
      (terminal.from (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X p.2)).toScheme) := by
  have hterm : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  have hringL : (Algebra.TensorProduct.includeLeftRingHom
        (R := ULift.{u} ℤ)
        (A := MvPolynomial {k : Fin (n + 1) // k ≠ p.1} (ULift.{u} ℤ))
        (B := MvPolynomial {l : Fin (m + 1) // l ≠ p.2} (ULift.{u} ℤ))).comp
        (chartIso (ULift.{u} ℤ) p.1).toRingHom =
      (segreChartTensorIso (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2).toRingHom.comp
        (chartMapLeft (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2) := by
    refine RingHom.ext fun z => ?_
    simpa using
      (segreChartTensorIso_chartMapLeft (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2 z).symm
  have hringR : (Algebra.TensorProduct.includeRight
        (R := ULift.{u} ℤ)
        (A := MvPolynomial {k : Fin (n + 1) // k ≠ p.1} (ULift.{u} ℤ))
        (B := MvPolynomial {l : Fin (m + 1) // l ≠ p.2} (ULift.{u} ℤ))).toRingHom.comp
        (chartIso (ULift.{u} ℤ) p.2).toRingHom =
      (segreChartTensorIso (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2).toRingHom.comp
        (chartMapRight (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2) := by
    refine RingHom.ext fun z => ?_
    simpa using
      (segreChartTensorIso_chartMapRight (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1))
        p.1 p.2 z).symm
  refine (isPullback_SpecMap_includeRingHom.{u} n m p).of_iso
    (specIsoOfRingEquiv (segreChartTensorIso (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p.1 p.2) ≪≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec
        (grading (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
        (genSub (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p)
        (genSub_mem_grading_one (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) p) one_pos).symm)
    (specIsoOfRingEquiv (chartIso (ULift.{u} ℤ) p.1) ≪≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.1)
        (X_mem (ULift.{u} ℤ) (Fin (n + 1)) p.1) one_pos).symm)
    (specIsoOfRingEquiv (chartIso (ULift.{u} ℤ) p.2) ≪≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X p.2)
        (X_mem (ULift.{u} ℤ) (Fin (m + 1)) p.2) one_pos).symm)
    (asIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))))) ?_ ?_
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  · simp only [Iso.trans_hom, Iso.symm_hom, specIsoOfRingEquiv_hom, chartProjLeft,
      Category.assoc, Iso.inv_hom_id_assoc]
    simp only [← Category.assoc]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hringL]
  · simp only [Iso.trans_hom, Iso.symm_hom, specIsoOfRingEquiv_hom, chartProjRight,
      Category.assoc, Iso.inv_hom_id_assoc]
    simp only [← Category.assoc]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hringR]

end Chart

end Stacks.AlgebraicGeometry.SegreProdIso

end
