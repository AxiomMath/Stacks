module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeronese
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison

/-!
# The bridge at Lemma 01O1's source, over an affine base

`StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison` proves [Stacks, Tag 01O1]'s
`θ`-assertion at the tag's own source `r^*(⨁_{n ∈ ℤ} 𝒪(nd))` over the degree-`d` locus, and its
`What is still carried` section names the three things that statement still demands of its caller:

1. that the morphism `r : T ⟶ Proj_S(𝒜)` lands in the **relative** degree-`d` locus,
2. the **degree-one datum** `α : (r^*(⨁_n 𝒪(nd)))_1 ≅ ℒ`, about the **relative** twist, and
3. the commutativity of the characterising triangle for the second leg `v`.

Over an affine base
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_hom_toDegreeOpen`
produces, from a quadruple, a morphism `φ : T ⟶ U_d ⊆ Proj Γ(⊤, 𝒜)` together with a degree-one
datum about the **absolute** twist. That is the wrong twist for (2), and `φ` goes to the wrong
scheme for (1). Both gaps close here: the morphism is `φ` followed by the chart over `⊤`, the
twist is converted by
`Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistDegreeOpenIso`, and the
locus condition follows from
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_image_degreeOpen_le`.

**This discharges (1) and (2) and not (3).** The commutativity of the triangle is left exactly
where `DegreeOpenTwistComparison` leaves it; see `What is NOT proved here` below. Nothing here
carries a tag.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackPieceCongr`: the crossing of the
  repository's two realizations of the inverse image of an `𝒪`-module, together with an equality
  of degrees, in one isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistVeronesePieceIso`: **the
  degree-`n` piece of Lemma 01O1's source is an absolute pullback twist**, over an affine base,
  for every `n : ℤ`; and `pullbackTwistVeronesePieceIso_one`, the degree-one case in the `1 * d`
  normalisation its consumer uses.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.mem_degreeOpen_toProj_topChart`: **the
  morphism the bridge builds lands in the relative degree-`d` locus**, with no hypothesis beyond
  `φ` factoring through the absolute `U_d`. This is input (1).
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.exists_hom_degreeOne_datum_of_isAffine`:
  **over an affine base, every quadruple yields a morphism to the relative `Proj` that lands in
  the relative degree-`d` locus and carries the relative degree-one datum.** Inputs (1) and (2)
  of Lemma 01O1's `θ`-assertion, assembled.

## What is NOT proved here

The commutativity of Lemma 01O1's triangle, item (3). `existsUnique_theta_of_degreeOpen` takes
the second leg `v` as an arbitrary degreewise family together with the hypothesis `hv` that the
triangle commutes for it, and nothing below constructs such a `v` from a quadruple's `ψ` or
proves `hv` for it. Note that defining `v` as `ψ` composed with the inverse of the comparison
would make `hv` hold by construction and the resulting statement vacuous; that is deliberately
not done.

The morphism is not shown here to lie over the base either, and that is a limitation of this
file and **not** of the repository: there is something to feed
`Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistIso_over_base`.
`MorphismToProjUniversal.IsCompatible`, the strict equivalence
`existsUnique_hom_toDegreeOpen` delivers, is indeed a condition on sections only and says nothing
about `φ` composed with the structure morphism; but
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.toProj_classifyingHom_comp_toSpecZero`
is the over-`S` identity for the classifying morphism, proved separately, and
`Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.classifyingHom_topChart_comp_toBase` of
`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.AffineOverBase` carries it along the
chart to `Proj_S(𝒜)`.
`...RelativeProjTwistChartBridge.exists_hom_overBase_degreeOne_datum_of_isAffine` there is
`exists_hom_degreeOne_datum_of_isAffine` below with that identity added.

## Implementation notes

`pullbackPieceCongr` is stated over an unapplied morphism on purpose. The two realizations of the
inverse image — Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback` and this repository's
`Stacks.RingedSpace.pullbackFunctor` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom` — are equal by `rfl`, but a goal
mixing them is not type-correct at the `implicit` transparency level, and crossing them at the
concrete morphism `toProj 𝒜 φ ≫ topChart A hS` exhausts the heartbeat budget. Proved once at a
bare morphism and specialised by application, the same step is immediate.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists
open Stacks.VeryAmpleAffineBase

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}

/-! ### Crossing the two realizations of the inverse image -/

/-- **The two realizations of the inverse image of an `𝒪`-module agree**, and a degree may be
rewritten at the same time: for `i = j`, the `Stacks.RingedSpace.pullbackFunctor` of the
underlying morphism of sheaves of rings applied to the twist in degree `i` is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback` applied to the twist in degree `j`.

Stated at an unapplied `g` deliberately — see the implementation notes. -/
def pullbackPieceCongr (D : TwistData A) {T : Scheme.{u}}
    (g : T ⟶ (relativeProj A).scheme) {i j : ℤ} (h : i = j) :
    (pullbackFunctor (ringedSpaceHom g)).obj (D.algebra.piece i) ≅
      (Scheme.Modules.pullback g).obj (D.algebra.piece j) := by
  subst h
  exact Iso.refl _

/-! ### The morphism the bridge builds lands in the relative degree-`d` locus -/

variable {T : Scheme.{u}} (hS : IsAffineOpen (⊤ : S.Opens)) {d : ℕ}

/-- **Input (1) of Lemma 01O1's `θ`-assertion, over an affine base.** A morphism `φ` through the
absolute degree-`d` open of `Proj Γ(⊤, 𝒜)`, followed by the chart over `⊤`, lands in the relative
degree-`d` locus of `Proj_S(𝒜)`.

The relative locus is by definition the supremum of the chart images of the absolute ones
(`...RelativeProj.RelativeProjData.chart_image_degreeOpen_le`), so this needs only that `φ` goes
where it says it does. -/
theorem mem_degreeOpen_toProj_topChart
    (φ : T ⟶ (degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme) (t : T) :
    (toProj (A.grading (⊤ : S.Opens)) φ ≫ topChart A hS).base t ∈
      (relativeProj A).degreeOpen d := by
  refine (relativeProj A).chart_image_degreeOpen_le (⊤ : S.Opens) hS d ?_
  exact ⟨(φ.base t).1, (φ.base t).2, rfl⟩

/-! ### The degree-one datum, absolute to relative -/

/-- **The degree-`n` piece of Lemma 01O1's source is an absolute pullback twist**, over an affine
base: for a morphism `φ` through the absolute degree-`d` open, the degree-`n` piece of
`r^*(⨁_m 𝒪(md))` at `r = toProj φ ≫ topChart` is the pullback along `φ` of the absolute twist
`𝒪(nd)` of `Proj Γ(⊤, 𝒜)`.

This holds for every `n : ℤ`. The glued twist becomes the absolute one by
`Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistDegreeOpenIso`; the only
other content is the crossing of the two inverse-image realizations, since
`...RelativeVeroneseTwists.pullbackTwistVeronese_piece` is `rfl`. -/
def pullbackTwistVeronesePieceIso (D : TwistData A)
    (φ : T ⟶ (degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme) (n : ℤ) :
    (pullbackTwistVeronese D (d : ℤ)
        (toProj (A.grading (⊤ : S.Opens)) φ ≫ topChart A hS)).piece n ≅
      pullbackTwist (A.grading (⊤ : S.Opens)) φ (n * (d : ℤ)) :=
  pullbackPieceCongr D _ rfl ≪≫ (pullbackTwistDegreeOpenIso hS D φ (n * (d : ℤ))).symm

/-- **The degree-one case**, in the `1 * d` normalisation that
`...RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen` asks its degree-one datum in: the
degree-one piece of Lemma 01O1's source is the pullback along `φ` of the absolute twist `𝒪(d)`. -/
def pullbackTwistVeronesePieceIso_one (D : TwistData A)
    (φ : T ⟶ (degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme) :
    (pullbackTwistVeronese D (d : ℤ)
        (toProj (A.grading (⊤ : S.Opens)) φ ≫ topChart A hS)).piece 1 ≅
      pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) :=
  pullbackPieceCongr D _ (one_mul (d : ℤ)) ≪≫
    (pullbackTwistDegreeOpenIso hS D φ (d : ℤ)).symm

/-! ### Inputs (1) and (2) of Lemma 01O1's `θ`-assertion, over an affine base -/

variable {f : T ⟶ S}

/-- **Over an affine base, every quadruple yields a morphism to the relative `Proj` that lands in
the relative degree-`d` locus and carries the relative degree-one datum.** These are inputs (1)
and (2) that `...RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen` demands of its caller,
for the morphism `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.`
`Quadruple.existsUnique_hom_toDegreeOpen` attaches to the quadruple.

Its third demand, the commutativity of the characterising triangle, is **not** discharged; nor is
the morphism shown to lie over the base. See the module docstring. -/
theorem exists_hom_degreeOne_datum_of_isAffine [IsAffine S] (hd : 0 < d)
    (B : SheafGradedAlgebra.{u} S) (D : TwistData B)
    (P : Quadruple f (situationAlgebra B) (d : ℤ)) :
    ∃ r : T ⟶ (relativeProj B).scheme,
      (∀ t : T, r.base t ∈ (relativeProj B).degreeOpen d) ∧
        Nonempty ((pullbackTwistVeronese D (d : ℤ) r).piece 1 ≅ P.L) := by
  obtain ⟨φ, ⟨α, -⟩, -⟩ :=
    Quadruple.existsUnique_hom_toDegreeOpen hd (fun n => B.isQuasicoherent n) P
  exact ⟨toProj (B.grading (⊤ : S.Opens)) φ ≫ topChart B (isAffineOpen_top S),
    mem_degreeOpen_toProj_topChart (isAffineOpen_top S) φ,
    ⟨pullbackTwistVeronesePieceIso_one (isAffineOpen_top S) D φ ≪≫ α⟩⟩

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
