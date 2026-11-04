module

public import StacksFrontier.AlgebraicGeometry.TwistDataFromChart.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent

/-!
# Two more fields of Tag 01NR's twist data are consequences of the chart description of `ψ`

`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` has nine fields.
`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.isQuasicoherent_piece` discharged
`isQuasicoherent` and `Stacks.AlgebraicGeometry.TwistDataFromChart.mul_comm_of_isGradedChartIso`
discharged `mul_comm`, leaving the seven that
`Stacks.AlgebraicGeometry.TwistDataFromChart.mk` asks for. Two of those seven — `ψ_one` and
`ψ_mul`, the statements that the homogeneous-section map preserves the unit and the product — ask
for nothing that is not already determined by the other fields: `ψ_chart` says what `ψ` is on an
affine open of the base, and over such an open the unit and the product of the glued algebra are
the unit and the product of the absolute twists, which is `isGradedChartIso`.

This file carries out that reduction, so a construction of the twists owes five fields rather
than seven.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.PsiChart`: the `ψ_chart` field of a twist datum as a
  proposition about a bare `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` together with a
  candidate section map, which is what a *construction* of the twists has available.
* `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.mk`: **the twist datum assembled from five fields**
  instead of seven.

## Main results

* `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.psi_one`: **the homogeneous-section map preserves the
  unit**, over every open of the base, as the `ψ_one` field asks.
* `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.psi_mul_eq` and `psi_mul`: **the homogeneous-section
  map preserves the product**, over every open of the base and in every pair of degrees, as the
  `ψ_mul` field asks — first as an equation between sections of one piece and then in the
  heterogeneous form the field states.
* `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.psi_one_affine` and `psi_mul_affine`: the same two
  statements over an affine open of the base, where they are the chart-level identities.

## The route, in two halves

Over an **affine** open `U` of the base both statements are three equations composed.
`ψ_chart` identifies the chart comparison of the homogeneous section attached to a local section
`a` with `ψ(a)` transported along the equality of the chart's image with the inverse image of `U`;
`Stacks.AlgebraicGeometry.TwistDataFromChart.absoluteTwistUnit_top` and
`absoluteTwistProduct_degreeSection` say that the unit and the product of the absolute twists are
the homogeneous sections attached to `1` and to the product; and `isGradedChartIso` carries those
to the unit and the product of the glued algebra. Composing them leaves the field's equation
transported along the chart's image, and the transport is undone by one injectivity step.

For a **general** open the two sides are sections of a sheaf on the relative Proj over the inverse
image of that open, and the affine opens of the base below it cover it — `preimage` commutes with
`iSup`, so their inverse images cover the inverse image. Over each member the restriction of each
side is its value there, by the naturality of `ψ`, of the two multiplications and of the unit,
which is the affine case. `AlgebraicGeometry.iSup_affineOpens_subtype_eq` is the covering and
`TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf` the separation half of the sheaf axiom.

## Implementation notes

The transport along the equality `chart ''ᵁ ⊤ = toBase ⁻¹ᵁ U` of opens cannot be avoided, because
`ψ_chart` is stated with it; but it is confined to three lemmas — `heq_of_eq_eqRec_symm`,
`heq_piece_of_eq` and `mul_app_eqRec` — together with `eqRec_symm_inj`, each of which has the two
opens as *variables* and is therefore proved by substituting the equality away. Stating them with
a variable family instead, as `{P : α → Sort*}`, does not work: the section `ψ(a)` has the type of
a section of a pushforward over `U` rather than of the piece over `toBase ⁻¹ᵁ U`, the two being
definitionally equal but not syntactically so, and the higher-order unification against `?P
(toBase ⁻¹ᵁ U)` then has no pattern to match. With the opens fixed by the equality there is
nothing to solve and the definitional unfolding happens where it should.

The transports along `Int.natCast_add n m`, by contrast, are **free**: `((n + m : ℕ) : ℤ)` and
`(n : ℤ) + (m : ℤ)` are definitionally equal, so by proof irrelevance that equality is `rfl` and
the transport reduces away. `natCast_add_eqRec_id` records this, and it is why `psi_mul_eq` can be
stated as an honest equation while the field it discharges is heterogeneous.

## What is not done here

**No `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed.** `mk` still asks for
the graded algebra, its chart identifications, the condition that those respect the product and
the unit, the section map, and the section map's chart description — and all five need the
transition comparisons of Tag 01NO between two charts, which a `ChartData` does not carry. In
particular nothing here constructs the multiplication or the unit of a glued graded algebra, and
nothing here proves
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`.

No `stacks` attribute is attached. Tag 01NR's first label asks for the complete structure and is
earned only by a term of `TwistData`; a reduction of two more of its fields is not a covering set
for it.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.TwistDataFromChart

namespace Stacks.AlgebraicGeometry.Tag01NRPsiCompat

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}
  {algebra : SchemeGradedAlgebra (relativeProj A).scheme}

/-! ### The transport along an equality of opens

Each lemma has the two opens as variables, so each is proved by substituting the equality away.
-/

/-- An equation modulo the transport along an equality of opens is a heterogeneous equation. -/
public theorem heq_of_eq_eqRec_symm {n : ℤ} {W₁ W₂ : (relativeProj A).scheme.Opens}
    (e : W₁ = W₂) {x : (algebra.piece n).val.obj (op W₁)}
    {y : (algebra.piece n).val.obj (op W₂)} (h : x = e.symm ▸ y) : HEq x y := by
  cases e
  exact heq_of_eq h

/-- A family of sections indexed by the opens takes heterogeneously equal values at two equal
opens. -/
public theorem heq_piece_of_eq {n : ℤ} {W₁ W₂ : (relativeProj A).scheme.Opens} (e : W₁ = W₂)
    (f : (W : (relativeProj A).scheme.Opens) → (algebra.piece n).val.obj (op W)) :
    HEq (f W₁) (f W₂) := by
  cases e
  rfl

/-- The product of two transported sections is the transported product. -/
public theorem mul_app_eqRec {i j : ℤ} {W₁ W₂ : (relativeProj A).scheme.Opens} (e : W₁ = W₂)
    (x : (algebra.piece i).val.obj (op W₂)) (y : (algebra.piece j).val.obj (op W₂)) :
    (algebra.mul i j).app (op W₁)
        (e.symm ▸ x : (algebra.piece i).val.obj (op W₁))
        (e.symm ▸ y : (algebra.piece j).val.obj (op W₁)) =
      (e.symm ▸ (algebra.mul i j).app (op W₂) x y :
        (algebra.piece (i + j)).val.obj (op W₁)) := by
  cases e
  rfl

/-- Transport along an equality of opens is injective. -/
public theorem eqRec_symm_inj {i : ℤ} {W₁ W₂ : (relativeProj A).scheme.Opens} (e : W₁ = W₂)
    {x y : (algebra.piece i).val.obj (op W₂)}
    (h : (e.symm ▸ x : (algebra.piece i).val.obj (op W₁)) =
      (e.symm ▸ y : (algebra.piece i).val.obj (op W₁))) : x = y := by
  cases e
  exact h

/-- **The transport along `Int.natCast_add` is the identity.** The two degree indices are
definitionally equal, so that equality is `rfl` by proof irrelevance and the transport reduces
away. This is why the heterogeneous `ψ_mul` field is an honest equation. -/
public theorem natCast_add_eqRec_id (n m : ℕ) {V : (relativeProj A).scheme.Opensᵒᵖ}
    (x : (algebra.piece ((n + m : ℕ) : ℤ)).val.obj V) :
    (Int.natCast_add n m ▸ x : (algebra.piece ((n : ℤ) + (m : ℤ))).val.obj V) = x := rfl

/-! ### The chart description of the section map -/

variable (D : ChartData A algebra)

/-- **The `ψ_chart` field of a twist datum, as a condition on a chart datum and a candidate
section map.** Over an affine open `U` of the base the chart comparison carries the homogeneous
section attached to a local section `a` of the base algebra to `ψ(a)`, transported along the
equality of the chart's image with the inverse image of `U`. -/
public def PsiChart
    (psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ))) : Prop :=
  ∀ (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) (a : A.sectionPieces U n),
    letI := D.chart_isOpenImmersion U hU
    D.mapSection U hU (n : ℤ) ⊤
      (degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) =
      (D.chart_range U hU).symm ▸ ((psi n).val.app (op U) a)

variable {D}
  {psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
    (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ))}

/-- The inverse images of the affine opens of the base below `U` cover the inverse image of `U`. -/
private theorem preimage_le_iSup_affineOpens (U : S.Opens) :
    (relativeProj A).toBase ⁻¹ᵁ U ≤ ⨆ i : {V : S.affineOpens // V.1 ≤ U},
      (relativeProj A).toBase ⁻¹ᵁ (i.1.1 : S.Opens) :=
  le_of_eq <| (congrArg ((relativeProj A).toBase ⁻¹ᵁ ·)
    (iSup_affineOpens_subtype_eq U).symm).trans (Scheme.Hom.preimage_iSup _ _)

/-! ### The unit -/

/-- **The section map preserves the unit over an affine open of the base.** The unit of the
absolute twists on the whole chart is the homogeneous section attached to `1`, which `ψ_chart`
sends to `ψ(1)` and `isGradedChartIso` to the unit of the glued algebra. -/
public theorem psi_one_affine (hD : IsGradedChartIso D) (hpsi : PsiChart D psi) (U : S.Opens)
    (hU : IsAffineOpen U) :
    (psi 0).val.app (op U) (A.one U) =
      algebra.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U)) := by
  let := D.chart_isOpenImmersion U hU
  have h1 : HEq (D.mapSection U hU ((0 : ℕ) : ℤ) ⊤
      (degreeSection (A.grading U) 0
        ⟨DirectSum.of (A.sectionPieces U) 0 (A.one U), A.of_mem_grading U (A.one U)⟩))
      ((psi 0).val.app (op U) (A.one U)) :=
    heq_of_eq_eqRec_symm (D.chart_range U hU) (hpsi U hU 0 (A.one U))
  have h2 : D.mapSection U hU ((0 : ℕ) : ℤ) ⊤
      (degreeSection (A.grading U) 0
        ⟨DirectSum.of (A.sectionPieces U) 0 (A.one U), A.of_mem_grading U (A.one U)⟩) =
      algebra.one.eval (op ((relativeProj A).chart U hU ''ᵁ ⊤)) := by
    refine Eq.trans ?_ (hD.2 U hU ⊤)
    exact congrArg (D.mapSection U hU ((0 : ℕ) : ℤ) ⊤)
      (absoluteTwistUnit_top (A.grading U)).symm
  have h3 : HEq (algebra.one.eval (op ((relativeProj A).chart U hU ''ᵁ ⊤)))
      (algebra.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U))) :=
    heq_piece_of_eq (D.chart_range U hU) fun W => algebra.one.eval (op W)
  exact eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))

/-- **The section map preserves the unit**, over every open of the base: this is the `ψ_one` field
of a twist datum. Both sides are sections over the inverse image of the open, and the inverse
images of the affine opens of the base below it cover that, so the affine case suffices. -/
public theorem psi_one (hD : IsGradedChartIso D) (hpsi : PsiChart D psi) (U : S.Opens) :
    (psi 0).val.app (op U) (A.one U) =
      algebra.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U)) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (algebra.piece ((0 : ℕ) : ℤ)).isSheaf
    (fun i : {V : S.affineOpens // V.1 ≤ U} => (relativeProj A).toBase ⁻¹ᵁ (i.1.1 : S.Opens))
    (fun i => Scheme.Hom.preimage_mono _ i.2) ?_ fun i => ?_
  · exact preimage_le_iSup_affineOpens U
  · refine Eq.trans ?_ (PresheafOfModules.sections_property algebra.one
      (homOfLE (Scheme.Hom.preimage_mono (relativeProj A).toBase i.2)).op).symm
    refine Eq.trans ?_ (psi_one_affine hD hpsi (i.1.1 : S.Opens) i.1.2)
    refine Eq.trans ?_ (congrArg ((psi 0).val.app (op (i.1.1 : S.Opens))) (A.one_res i.2))
    exact (PresheafOfModules.app_resLE (psi 0).val i.2 (A.one U)).symm

/-! ### The product -/

/-- **The section map preserves the product over an affine open of the base.** The canonical
product of the two homogeneous sections attached to `a` and `b` is the homogeneous section
attached to their product, which `ψ_chart` sends to `ψ(ab)`, while `isGradedChartIso` sends it to
the product of `ψ(a)` and `ψ(b)` in the glued algebra. -/
public theorem psi_mul_affine (hD : IsGradedChartIso D) (hpsi : PsiChart D psi) (U : S.Opens)
    (hU : IsAffineOpen U) (n m : ℕ) (a : A.sectionPieces U n) (b : A.sectionPieces U m) :
    (psi (n + m)).val.app (op U)
        ((Int.natCast_add n m).symm ▸ (A.mul (n : ℤ) (m : ℤ)).app U a b) =
      (algebra.mul (n : ℤ) (m : ℤ)).app (op ((relativeProj A).toBase ⁻¹ᵁ U))
        ((psi n).val.app (op U) a) ((psi m).val.app (op U) b) := by
  let := D.chart_isOpenImmersion U hU
  refine eqRec_symm_inj (D.chart_range U hU) ?_
  refine Eq.trans (hpsi U hU (n + m) ((A.mul (n : ℤ) (m : ℤ)).app U a b)).symm ?_
  refine Eq.trans ?_ (mul_app_eqRec (D.chart_range U hU)
    ((psi n).val.app (op U) a :
      (algebra.piece (n : ℤ)).val.obj (op ((relativeProj A).toBase ⁻¹ᵁ U)))
    ((psi m).val.app (op U) b :
      (algebra.piece (m : ℤ)).val.obj (op ((relativeProj A).toBase ⁻¹ᵁ U))))
  refine Eq.trans ?_ (TwistRigidity.mul_app_congr algebra (n : ℤ) (m : ℤ)
    (op ((relativeProj A).chart U hU ''ᵁ ⊤)) (hpsi U hU n a) (hpsi U hU m b))
  refine Eq.trans ?_ (hD.1 U hU (n : ℤ) (m : ℤ) ⊤ _ _)
  refine congrArg (D.mapSection U hU ((n : ℤ) + (m : ℤ)) ⊤) ?_
  refine Eq.trans ?_ (absoluteTwistProduct_degreeSection (A.grading U) n m _ _).symm
  exact congrArg (degreeSection (A.grading U) (n + m))
    (Subtype.ext (DirectSum.of_mul_of a b).symm)

/-- **The section map preserves the product**, over every open of the base and in every pair of
degrees, as an equation between sections of one homogeneous piece. The two sides are sections over
the inverse image of the open and the affine case applies over each member of the covering. -/
public theorem psi_mul_eq (hD : IsGradedChartIso D) (hpsi : PsiChart D psi) (U : S.Opens)
    (n m : ℕ) (a : A.sectionPieces U n) (b : A.sectionPieces U m) :
    (psi (n + m)).val.app (op U)
        ((Int.natCast_add n m).symm ▸ (A.mul (n : ℤ) (m : ℤ)).app U a b) =
      (algebra.mul (n : ℤ) (m : ℤ)).app (op ((relativeProj A).toBase ⁻¹ᵁ U))
        ((psi n).val.app (op U) a) ((psi m).val.app (op U) b) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf
    (algebra.piece ((n : ℤ) + (m : ℤ))).isSheaf
    (fun i : {V : S.affineOpens // V.1 ≤ U} => (relativeProj A).toBase ⁻¹ᵁ (i.1.1 : S.Opens))
    (fun i => Scheme.Hom.preimage_mono _ i.2) ?_ fun i => ?_
  · exact preimage_le_iSup_affineOpens U
  · refine Eq.trans (PresheafOfModules.app_resLE (psi (n + m)).val i.2 _).symm ?_
    refine Eq.trans (congrArg ((psi (n + m)).val.app (op (i.1.1 : S.Opens)))
      ((A.mul (n : ℤ) (m : ℤ)).naturality i.2 a b)) ?_
    refine Eq.trans (psi_mul_affine hD hpsi (i.1.1 : S.Opens) i.1.2 n m _ _) ?_
    refine Eq.trans (TwistRigidity.mul_app_congr algebra (n : ℤ) (m : ℤ)
      (op ((relativeProj A).toBase ⁻¹ᵁ (i.1.1 : S.Opens)))
      (PresheafOfModules.app_resLE (psi n).val i.2 a)
      (PresheafOfModules.app_resLE (psi m).val i.2 b)) ?_
    exact ((algebra.mul (n : ℤ) (m : ℤ)).naturality
      (homOfLE (Scheme.Hom.preimage_mono (relativeProj A).toBase i.2)).op _ _).symm

/-- **The section map preserves the product**, in the heterogeneous form the `ψ_mul` field of a
twist datum states: the two sides lie in the pieces indexed by the natural-number sum and by the
integer sum of the degrees. Those indices are definitionally equal, so this is `psi_mul_eq`. -/
public theorem psi_mul (hD : IsGradedChartIso D) (hpsi : PsiChart D psi) (U : S.Opens)
    (n m : ℕ) (a : A.sectionPieces U n) (b : A.sectionPieces U m) :
    HEq
      ((psi (n + m)).val.app (op U)
        ((Int.natCast_add n m).symm ▸ (A.mul (n : ℤ) (m : ℤ)).app U a b))
      ((algebra.mul (n : ℤ) (m : ℤ)).app (op ((relativeProj A).toBase ⁻¹ᵁ U))
        ((psi n).val.app (op U) a) ((psi m).val.app (op U) b)) :=
  heq_of_eq (psi_mul_eq hD hpsi U n m a b)

/-! ### The reduced constructor -/

/-- **Tag 01NR's twist datum, assembled from five fields instead of seven.** On top of the two
fields `Stacks.AlgebraicGeometry.TwistDataFromChart.mk` already supplies, `ψ_one` is
`Stacks.AlgebraicGeometry.Tag01NRPsiCompat.psi_one` and `ψ_mul` is
`Stacks.AlgebraicGeometry.Tag01NRPsiCompat.psi_mul`, both consequences of `isGradedChartIso`
together with the chart description of the section map.

The five remaining fields are stated here exactly as
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` states them. -/
public def mk (B : SchemeGradedAlgebra (relativeProj A).scheme) (D : ChartData A B)
    (hD : IsGradedChartIso D)
    (psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (B.piece (n : ℤ)))
    (hpsi : PsiChart D psi) : TwistData A :=
  TwistDataFromChart.mk B D hD psi (fun U => psi_one hD hpsi U)
    (fun U n m a b => psi_mul hD hpsi U n m a b) hpsi

/-- **Faithfulness of `PsiChart`**: the proposition is literally the `ψ_chart` field of a twist
datum, so a twist datum satisfies it with nothing added. -/
public theorem psiChart_of_twistData (E : TwistData A) : PsiChart E.chartData E.ψ :=
  E.ψ_chart

end Stacks.AlgebraicGeometry.Tag01NRPsiCompat

end
