module

public import StacksFrontier.AlgebraicGeometry.Conormal.ChartGradedAlgebra

/-!
# A common chart basis for two immersions out of the same source

Let `j : F ⟶ X` and `j' : F ⟶ X'` be immersions out of the *same* source into two *unrelated*
ambient schemes. Each of them has its own basis of charts on `F` — the preimages of the affine
opens of its ambient over which it restricts to a closed immersion,
`Stacks.Conormal.conormalChart_isBasis` — and the two bases have no member in common for
trivial reasons.

A comparison of the conormal algebras of `j` and of `j'`, however, has to be given over a
*single* basis, over whose members both affine presentations are available: this is the shape of
`Stacks.Conormal.gradedAlgebraIsoOfChartIso`, and it is what the comparison of Stacks 0CAY
needs, where `X = Y ×_T W` and `X' = Y ×_T W'` are two base changes of one morphism and `F` is
the fibre `Y_t` sitting in both. The intersections `j ⁻¹ᵁ V ⊓ j' ⁻¹ᵁ V'` of two charts do form a
basis, but such an intersection need not be a chart of either immersion, so no affine
presentation is available over it.

This file produces the common basis. The point is that the preimage of a chart is an affine open
of `F` whose *basic* opens are again preimages of charts — `exists_chart_basicOpen`, by
surjectivity of the map on sections over a chart — and that two affine opens of a scheme have a
common basic open around any point of their intersection,
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`. Shrinking a chart of `j` and a chart of
`j'` to a common basic open of their preimages therefore produces one open of `F` which is the
preimage of a chart on *both* sides.

## Main definitions

* `Stacks.Conormal.CommonChart`: a chart of `j` and a chart of `j'` whose preimages in `F` are
  **equal**, and `Stacks.Conormal.commonChartOpens`, the family of those common preimages.

## Main results

* `Stacks.Conormal.isAffineOpen_preimage_of_closedRestriction`: the preimage of a chart is an
  affine open.
* `Stacks.Conormal.exists_chart_basicOpen`: a basic open of the preimage of a chart is the
  preimage of a chart.
* `Stacks.Conormal.exists_commonChart_of_charts`: a chart of each immersion around a point is
  refined by a common chart around that point, and
  `Stacks.Conormal.exists_commonChart_near` is its reading over an open of `F`.
* `Stacks.Conormal.exists_commonChart_refine`: two common charts around a point are refined by a
  third, with the containments in the two ambients that the naturality of the chart-local
  presentations needs.
* `Stacks.Conormal.commonChart_isBasis`: **the opens of the common charts form a basis of the
  topology of `F`.** They are preimages of charts of `j` by definition and preimages of charts
  of `j'` by `Stacks.Conormal.commonChartOpens_eq_right`, so the chart-local data of both
  immersions is available over each of them.
* `Stacks.Conormal.gradedAlgebraIsoOfCommonChartIso`: an isomorphism of sheaves of graded
  algebras on `F` assembled from isomorphisms over the members of a family of common charts whose
  opens form a basis, with `gradedAlgebraIsoOfCommonChartIso_hom_app_app` and
  `gradedAlgebraIsoOfCommonChartIso_inv_app_app` its components.
* `Stacks.Conormal.nonempty_conormalAlgebra_iso_of_commonChartIso`: its reading for the two
  conormal algebras, which is the conclusion
  `Stacks.ConormalApproximation.HasConormalIso` asks for.

## Implementation notes

`CommonChart` asks for an equality of the two preimages, not an inclusion of one in the other.
An inclusion would be cheaper to produce and useless: the data over a member of the basis would
then be available on one side only, and restricting the other side's affine presentation along a
non-identity inclusion is exactly the step that is not available.

The basis is not asked to be affine, nor to be finite: the assembly
`Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis` requires neither. Every member is
affine all the same, being the preimage of a chart, and that is what makes the two affine
presentations available over it.

The assembly is stated for an arbitrary *sub-family* `𝒞 : ι → CommonChart j j'` whose opens form
a basis, and not for the family of all common charts, even though `commonChart_isBasis` says the
latter is a basis. The reason is that the chart-local comparisons being glued are produced by a
geometric construction which applies only to specially chosen charts: in Stacks 0CAY only the
charts of `Y ×_T W` of the form `pr₁⁻¹U ⊓ pr₂⁻¹W₀`, for `U` an affine open of `Y`, have sections
`Γ(W, W₀) ⊗_{Γ(T, T₀)} Γ(Y, U)`, and an arbitrary affine open of `Y ×_T W` is not of that form.
`Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis` is already polymorphic in the index
type, so nothing is lost: taking `𝒞 = id` with `commonChart_isBasis` recovers the full family.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

namespace Stacks.Conormal

variable {F X X' : Scheme.{u}}

/-! ### Basic opens of a chart are charts -/

/-- **Over an affine open on which an immersion restricts to a closed immersion, the preimage is
an affine open of the source**, a closed immersion being an affine morphism. The hypothesis is
the one the charts of an immersion provide, by
`AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange`; it is the same hypothesis as in
`AlgebraicGeometry.app_surjective_of_closedRestriction`. -/
theorem isAffineOpen_preimage_of_closedRestriction (i : F ⟶ X) [IsImmersion i]
    (V : X.affineOpens) (hcl : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) :
    IsAffineOpen (i ⁻¹ᵁ V.1) := by
  let _ : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl) := hcl
  exact isAffine_of_isAffineHom (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)

/-- **A basic open of the preimage of a chart is the preimage of a chart.** The map on sections
over a chart is surjective, so a section of the source over the chart's preimage is the
restriction of a section upstairs, and the preimage of the basic open of the latter is the basic
open of the former. -/
theorem exists_chart_basicOpen (i : F ⟶ X) [IsImmersion i] (U : ConormalChart i)
    (f : Γ(F, i ⁻¹ᵁ U.1.1)) :
    ∃ V : ConormalChart i, i ⁻¹ᵁ V.1.1 = F.basicOpen f ∧ V.1.1 ≤ U.1.1 := by
  obtain ⟨a, ha⟩ := AlgebraicGeometry.app_surjective_of_closedRestriction i U.1
    (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2) f
  refine ⟨⟨⟨X.basicOpen a, U.1.2.basicOpen a⟩, (X.basicOpen_le a).trans U.2⟩, ?_,
    X.basicOpen_le a⟩
  calc i ⁻¹ᵁ X.basicOpen a = F.basicOpen ((i.app U.1.1) a) := Scheme.preimage_basicOpen i a
    _ = F.basicOpen f := congrArg F.basicOpen ha

/-- The preimage of a chart is an affine open of the source. -/
private theorem isAffineOpen_preimage_chart (i : F ⟶ X) [IsImmersion i] (U : ConormalChart i) :
    IsAffineOpen (i ⁻¹ᵁ U.1.1) :=
  isAffineOpen_preimage_of_closedRestriction i U.1
    (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2)

/-- Two charts containing the image of a point have a chart around it inside both. -/
private theorem exists_chart_le_inf (i : F ⟶ X) [IsImmersion i] (C D : ConormalChart i) (x : F)
    (hxC : x ∈ i ⁻¹ᵁ C.1.1) (hxD : x ∈ i ⁻¹ᵁ D.1.1) :
    ∃ U : ConormalChart i, x ∈ i ⁻¹ᵁ U.1.1 ∧ U.1.1 ≤ C.1.1 ∧ U.1.1 ≤ D.1.1 := by
  obtain ⟨U, hUa, hxU, hU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show i x ∈ C.1.1 ⊓ D.1.1 ⊓ i.coborderRange from ⟨⟨hxC, hxD⟩, C.2 hxC⟩)
  exact ⟨⟨⟨U, hUa⟩, hU.trans inf_le_right⟩, hxU, hU.trans (inf_le_left.trans inf_le_left),
    hU.trans (inf_le_left.trans inf_le_right)⟩

/-! ### The common charts of two immersions -/

/-- A chart of `j : F ⟶ X` together with a chart of `j' : F ⟶ X'` whose preimages in the common
source `F` are equal: one open of `F` over which the chart-local data of *both* immersions is
available. -/
structure CommonChart (j : F ⟶ X) (j' : F ⟶ X') [IsImmersion j] [IsImmersion j'] where
  /-- The chart of the first immersion. -/
  left : ConormalChart j
  /-- The chart of the second immersion. -/
  right : ConormalChart j'
  /-- The two charts have the same preimage in the source. -/
  preimage_eq : j ⁻¹ᵁ left.1.1 = j' ⁻¹ᵁ right.1.1

variable (j : F ⟶ X) (j' : F ⟶ X') [IsImmersion j] [IsImmersion j']

/-- The family of opens of the source cut out by the common charts of two immersions. -/
def commonChartOpens (C : CommonChart j j') : F.Opens :=
  j ⁻¹ᵁ C.left.1.1

/-- The open of a common chart is the preimage of a chart of the first immersion, so it is one of
the opens of `Stacks.Conormal.conormalChartFunctor` for `j`. -/
theorem commonChartOpens_eq_left (C : CommonChart j j') :
    commonChartOpens j j' C = (conormalChartFunctor j).obj C.left :=
  rfl

/-- The open of a common chart is the preimage of a chart of the second immersion, so it is one
of the opens of `Stacks.Conormal.conormalChartFunctor` for `j'`. -/
theorem commonChartOpens_eq_right (C : CommonChart j j') :
    commonChartOpens j j' C = (conormalChartFunctor j').obj C.right :=
  C.preimage_eq

/-- The first immersion restricts to a closed immersion over the chart on its side of a common
chart, that chart lying in the coborder of its range. -/
theorem isClosedImmersion_commonChart_left (C : CommonChart j j') :
    IsClosedImmersion (j.resLE C.left.1.1 (j ⁻¹ᵁ C.left.1.1) le_rfl) :=
  isClosedImmersion_resLE_of_le_coborderRange j C.left.1.1 C.left.2

/-- The second immersion restricts to a closed immersion over the chart on its side of a common
chart. -/
theorem isClosedImmersion_commonChart_right (C : CommonChart j j') :
    IsClosedImmersion (j'.resLE C.right.1.1 (j' ⁻¹ᵁ C.right.1.1) le_rfl) :=
  isClosedImmersion_resLE_of_le_coborderRange j' C.right.1.1 C.right.2

/-- The open of a common chart is affine, being the preimage of a chart. -/
theorem isAffineOpen_commonChartOpens (C : CommonChart j j') :
    IsAffineOpen (commonChartOpens j j' C) :=
  isAffineOpen_preimage_chart j C.left

/-- **A chart of each immersion around a point is refined by a common chart around that point.**
The two preimages are affine opens of the source, so they have a common basic open around the
point, and a basic open of the preimage of a chart is again the preimage of a chart — of a chart
contained in the given one, on either side. This is the content of the file: everything else is
an application of it. -/
theorem exists_commonChart_of_charts (U : ConormalChart j) (U' : ConormalChart j') (x : F)
    (hx : x ∈ j ⁻¹ᵁ U.1.1) (hx' : x ∈ j' ⁻¹ᵁ U'.1.1) :
    ∃ C : CommonChart j j', x ∈ commonChartOpens j j' C ∧
      C.left.1.1 ≤ U.1.1 ∧ C.right.1.1 ≤ U'.1.1 := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter
      (isAffineOpen_preimage_chart j U) (isAffineOpen_preimage_chart j' U') x ⟨hx, hx'⟩
  obtain ⟨V, hV, hVU⟩ := exists_chart_basicOpen j U f
  obtain ⟨V', hV', hV'U'⟩ := exists_chart_basicOpen j' U' g
  refine ⟨⟨V, V', hV.trans (hfg.trans hV'.symm)⟩, ?_, hVU, hV'U'⟩
  show x ∈ j ⁻¹ᵁ V.1.1
  rw [hV]
  exact hxf

/-- **Every point of an open of the source has a common chart around it inside that open.**
Both immersions have a chart around the point whose preimage is inside the given open, by
`exists_chart_near`, and `exists_commonChart_of_charts` refines the two to a common chart. -/
theorem exists_commonChart_near (W : F.Opens) (x : F) (hx : x ∈ W) :
    ∃ C : CommonChart j j', x ∈ commonChartOpens j j' C ∧ commonChartOpens j j' C ≤ W := by
  obtain ⟨U, hxU, hUW, hUcob⟩ := exists_chart_near j W x hx
  obtain ⟨U', hxU', -, hU'cob⟩ := exists_chart_near j' W x hx
  obtain ⟨C, hxC, hCU, -⟩ :=
    exists_commonChart_of_charts j j' ⟨U, hUcob⟩ ⟨U', hU'cob⟩ x hxU hxU'
  exact ⟨C, hxC, (j.preimage_mono hCU).trans hUW⟩

/-- **Two common charts around a point are refined by a third**, whose chart on each side is
contained in the charts of the two given ones on that side. The containments are containments in
the *ambient* schemes, which is what the naturality of the chart-local presentations of the two
conormal algebras — `Stacks.Conormal.ConormalAlgebraData.localMap_naturality` — asks for, and
which a containment of the opens in the source does not give. -/
theorem exists_commonChart_refine (C D : CommonChart j j') (x : F)
    (hxC : x ∈ commonChartOpens j j' C) (hxD : x ∈ commonChartOpens j j' D) :
    ∃ E : CommonChart j j', x ∈ commonChartOpens j j' E ∧
      E.left.1.1 ≤ C.left.1.1 ∧ E.left.1.1 ≤ D.left.1.1 ∧
      E.right.1.1 ≤ C.right.1.1 ∧ E.right.1.1 ≤ D.right.1.1 := by
  have hxC' : x ∈ commonChartOpens j j' C := hxC
  have hxD' : x ∈ commonChartOpens j j' D := hxD
  rw [commonChartOpens_eq_right] at hxC' hxD'
  obtain ⟨U, hxU, hUC, hUD⟩ := exists_chart_le_inf j C.left D.left x hxC hxD
  obtain ⟨U', hxU', hU'C, hU'D⟩ := exists_chart_le_inf j' C.right D.right x hxC' hxD'
  obtain ⟨E, hxE, hEU, hEU'⟩ := exists_commonChart_of_charts j j' U U' x hxU hxU'
  exact ⟨E, hxE, hEU.trans hUC, hEU.trans hUD, hEU'.trans hU'C, hEU'.trans hU'D⟩

/-- **The opens of the common charts of two immersions out of the same source form a basis of the
topology of that source.** Every point of an open has a common chart around it inside that open,
by `exists_commonChart_near`. -/
theorem commonChart_isBasis : Opens.IsBasis (Set.range (commonChartOpens j j')) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨C, hxC, hCW⟩ := exists_commonChart_near j j' W x hx
  exact ⟨commonChartOpens j j' C, ⟨C, rfl⟩, hxC, hCW⟩

/-! ### The assembly over the common charts -/

section GradedAlgebra

variable (A B : SheafOfModules.GradedAlgebra.{u, u} F.ringCatSheaf)
  {ι : Type v} (𝒞 : ι → CommonChart j j')
  (e : ∀ (n : ℤ) (a : ι),
    (A.piece n).val.obj (op (commonChartOpens j j' (𝒞 a))) ≅
      (B.piece n).val.obj (op (commonChartOpens j j' (𝒞 a))))
  (hbasis : Opens.IsBasis (Set.range fun a => commonChartOpens j j' (𝒞 a)))

/-- **An isomorphism of sheaves of graded algebras on the common source of two immersions,
assembled from isomorphisms over the members of a family of common charts whose opens form a
basis.** Over each member both immersions have their chart-local presentation, by
`commonChartOpens_eq_left` and `commonChartOpens_eq_right`.

The family is an arbitrary `𝒞 : ι → CommonChart j j'`, not the family of *all* common charts:
the chart-local presentations a geometric situation supplies are available only for specially
chosen charts — in Stacks 0CAY only for the charts of `Y ×_T W` that are base changes of an
affine open of `Y` — while `Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis` needs
nothing of the family beyond `hbasis`. Taking `𝒞 = id` and `commonChart_isBasis` recovers the
full family. -/
noncomputable def gradedAlgebraIsoOfCommonChartIso
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (fun a => commonChartOpens j j' (𝒞 a)) fun a => (e n a).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (fun a => commonChartOpens j j' (𝒞 a)) fun n a => (e n a).hom) : A ≅ B :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis A B
    (fun a => commonChartOpens j j' (𝒞 a)) e hbasis hcomp hmul

/-- The assembled isomorphism has the given isomorphism as its degree-`n` component over each
member of the family. -/
theorem gradedAlgebraIsoOfCommonChartIso_hom_app_app
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (fun a => commonChartOpens j j' (𝒞 a)) fun a => (e n a).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (fun a => commonChartOpens j j' (𝒞 a)) fun n a => (e n a).hom) (n : ℤ) (a : ι) :
    ((gradedAlgebraIsoOfCommonChartIso j j' A B 𝒞 e hbasis hcomp hmul).hom.app n).val.app
        (op (commonChartOpens j j' (𝒞 a))) = (e n a).hom :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis_hom_app_app A B
    (fun a => commonChartOpens j j' (𝒞 a)) e hbasis hcomp hmul n a

/-- The inverse of the assembled isomorphism has the inverse of the given isomorphism as its
degree-`n` component over each member of the family. -/
theorem gradedAlgebraIsoOfCommonChartIso_inv_app_app
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (fun a => commonChartOpens j j' (𝒞 a)) fun a => (e n a).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (fun a => commonChartOpens j j' (𝒞 a)) fun n a => (e n a).hom) (n : ℤ) (a : ι) :
    ((gradedAlgebraIsoOfCommonChartIso j j' A B 𝒞 e hbasis hcomp hmul).inv.app n).val.app
        (op (commonChartOpens j j' (𝒞 a))) = (e n a).inv :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis_inv_app_app A B
    (fun a => commonChartOpens j j' (𝒞 a)) e hbasis hcomp hmul n a

end GradedAlgebra

/-! ### The conormal algebras of two immersions out of one source -/

/-- **The conormal algebras of two immersions out of the same source are isomorphic as soon as
their degree-`n` sections are isomorphic over the members of a family of common charts whose
opens form a basis**, compatibly with the restrictions between those members and
multiplicatively. This is the conclusion asked for by
`Stacks.ConormalApproximation.HasConormalIso`, where the two immersions are the closed
immersions of the fibre `Y_t` into two base changes of `Y ⟶ T`; the chart-local presentations of
the two conormal algebras over a common chart are
`Stacks.Conormal.ConormalAlgebraData.localMap` at `(𝒞 a).left` and at `(𝒞 a).right`, which are
available by `commonChartOpens_eq_left` and `commonChartOpens_eq_right`. -/
theorem nonempty_conormalAlgebra_iso_of_commonChartIso
    {ι : Type v} (𝒞 : ι → CommonChart j j')
    (e : ∀ (n : ℤ) (a : ι),
      ((conormalAlgebra j).algebra.piece n).val.obj (op (commonChartOpens j j' (𝒞 a))) ≅
        ((conormalAlgebra j').algebra.piece n).val.obj (op (commonChartOpens j j' (𝒞 a))))
    (hbasis : Opens.IsBasis (Set.range fun a => commonChartOpens j j' (𝒞 a)))
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis
      ((conormalAlgebra j).algebra.piece n) ((conormalAlgebra j').algebra.piece n)
      (fun a => commonChartOpens j j' (𝒞 a)) fun a => (e n a).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis
      (conormalAlgebra j).algebra (conormalAlgebra j').algebra
      (fun a => commonChartOpens j j' (𝒞 a)) fun n a => (e n a).hom) :
    Nonempty ((conormalAlgebra j).algebra ≅ (conormalAlgebra j').algebra) :=
  ⟨gradedAlgebraIsoOfCommonChartIso j j' _ _ 𝒞 e hbasis hcomp hmul⟩

end Stacks.Conormal

end
