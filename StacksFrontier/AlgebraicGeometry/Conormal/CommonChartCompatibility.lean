module

public import StacksFrontier.AlgebraicGeometry.Conormal.ChartAssociatedGraded
public import StacksFrontier.AlgebraicGeometry.Conormal.CommonCharts

/-!
# Gluing the chart-local comparisons of two conormal algebras over the common charts

Let `j : F ⟶ X` and `j' : F ⟶ X'` be immersions out of the same source. Over a common chart
`C` — a chart of `j` and a chart of `j'` with the same preimage in `F`, as produced by
`StacksFrontier/AlgebraicGeometry/Conormal/CommonCharts.lean` — a comparison of the associated
graded algebras of the two kernel ideals gives a comparison of the sections of the two conormal
algebras in every degree, `Stacks.Conormal.chartSectionsIsoInt`. The common charts form a basis
of `F`, so such a family glues to an isomorphism of the two conormal algebras — provided the
family commutes with the restriction maps between the members of the basis, which is
`Stacks.BasisRestriction.IsCompatibleOnBasis`.

This file supplies that compatibility. The input is a family of chart-local comparisons indexed by
an arbitrary `𝒞 : ι → CommonChart j j'` whose opens form a basis, which is compatible with
restriction in the sense of `Stacks.Conormal.IsChartRestriction` *at a refining member*: any two
members and a point of both of their opens admit a member refining both in both ambients, over
which the comparison is the restriction of the comparison over each. This is a condition on the
family and not a consequence of the fields of its members, since a single
`Stacks.Conormal.ChartAssociatedGradedEquiv` is data on one pair of charts and says nothing about
any other pair.

## Main definitions

* `Stacks.Conormal.CommonChartAssociatedGradedEquiv`: a comparison of the associated graded
  algebras over the members of a family of common charts whose opens form a basis, compatible
  with restriction at a refining member.
* `Stacks.Conormal.CommonChartAssociatedGradedEquiv.ofAllCharts`: the full family, with the
  compatibility for *every* nested pair of common charts, is such a comparison, so nothing
  giveable in the stronger shape is lost; and
  `Stacks.Conormal.CommonChartAssociatedGradedEquiv.diagonal`: the comparison of one immersion
  with itself, over the diagonal family of its own charts, which is the check that the data is
  available at all.
* `Stacks.Conormal.commonChartSectionsIso`: the resulting degreewise family of comparisons of the
  sections of the two conormal algebras over the members of the family.
* `Stacks.Conormal.commonChartAssociatedGradedEquivOfPresentations`: such a comparison built from
  a presentation of each chart ring as a concrete quotient of an ambient ring, together with a
  comparison of the associated graded algebras of the quotients over each member and, for two
  members and a point of both of their opens, a refining member with a comparison of the ambient
  presentations to each of the two. The ambient ring may vary from member to member, as it does
  in Stacks 0CAY.

## Main results

* `Stacks.Conormal.commonChartSectionsIso_isCompatibleOnBasis`: **the family commutes with the
  restriction maps between the members**, which is the one nontrivial step. Containment of the
  two *opens* of `F` cut out by two common charts says nothing about their charts in the two
  ambient schemes, and the chart-local presentations restrict only along a containment upstairs.
  The two sections being compared are therefore compared locally: around each point of the
  smaller open the `restrict` field produces a member of the family refining both *in both
  ambients*, and there the comparison is `Stacks.Conormal.chartSectionsIsoInt_restrict`. Those
  refinements cover the smaller open, so separatedness of the target finishes it —
  `Stacks.BasisRestriction.moduleSheafSection_ext_of_cover`.
* `Stacks.Conormal.commonChartSectionsIso_isMultiplicativeOnBasis`: the family is multiplicative
  over each member, which is `Stacks.Conormal.chartSectionsIsoInt_mul` at that chart.
* `Stacks.Conormal.nonempty_conormalAlgebra_iso_of_commonChartAssociatedGradedEquiv`: **the two
  conormal algebras are isomorphic.** This is the conclusion asked for by
  `Stacks.ConormalApproximation.HasConormalIso`.

## Implementation notes

Neither the family of all common charts nor the compatibility for every nested pair of members is
asked for, because neither is available in Stacks 0CAY. The chart-local comparison there rests on
a presentation of the chart ring as a quotient of a polynomial ring, which
`Stacks.ConormalApproximation.chartQuotientPresentationOfPullbackChart` supplies only for the
charts of `Y ×_T W` of the form `pr₁⁻¹U ⊓ pr₂⁻¹W₀` with `U` an affine open of `Y`; an arbitrary
affine open of `Y ×_T W` is not a base change of one, so its sections are not
`Γ(W, W₀) ⊗_{Γ(T, T₀)} Γ(Y, U)` for any `U`. And the comparison of the presentations of two
nested charts is a renaming of the finitely many variables of the larger one among those of the
smaller one, `Stacks.ConormalApproximation.chartQuotientPresentationHomOfRename`, whose
hypothesis is a condition on the *pair*; a chart has infinitely many charts of the family below
it, whose generators would all have to appear among the finitely many variables of one
presentation, so no family of presentations can satisfy it for all nested pairs at once.

Both weakenings are free. The assembly
`Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis` is polymorphic in the index type
and asks only `Opens.IsBasis` of the range, so the sub-family costs nothing; and
`commonChartSectionsIso_isCompatibleOnBasis` refines around each point in any case, so the
compatibility between arbitrary nested members would be used nowhere. The conclusions of every
consumer are unchanged, and `CommonChartAssociatedGradedEquiv.ofAllCharts` recovers the structure
from the stronger data.

The compatibility is *not* proved by quantifying a rigidity hypothesis over every object of the
site: a degree-`n` section of a conormal algebra over a general open is only locally a sum of
products of degree-one sections, so no such hypothesis is available here. What is used is only
separatedness of the target, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedAlgebraOnBasis.lean`.

The refining member the `restrict` field provides is required to be contained in the two given
ones on *both* sides, and that is exactly what
`Stacks.Conormal.chartSectionsIsoInt_restrict` needs; a refinement with containment only in the
source `F` would not do, which is why that lemma is stated the way it is. For the full family
such a refinement exists unconditionally, by `Stacks.Conormal.exists_commonChart_refine`.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v w

namespace Stacks.Conormal

variable {F X X' : Scheme.{u}} (j : F ⟶ X) (j' : F ⟶ X') [IsImmersion j] [IsImmersion j']

/-- **A comparison of the associated graded algebras of two immersions out of one source, over
the members of a family of common charts whose opens form a basis, locally compatible with
restriction.** The second field is the chart-local datum of
`Stacks.Conormal.ChartAssociatedGradedEquiv` over each member of the family; the third says that
two members and a point in both of their opens admit a third member refining both *in both
ambient schemes* over which the comparison is the restriction of the comparison over each.

Neither the family of all common charts nor the compatibility for every nested pair of members is
asked for, and neither is available where this is used. In Stacks 0CAY the chart-local comparison
exists only for the charts of `Y ×_T W` which are base changes of an affine open of `Y`; and the
comparison of two nested chart presentations is a renaming of finitely many variables
(`Stacks.ConormalApproximation.chartQuotientPresentationHomOfRename`), so a single chart, having
infinitely many members of the family below it, cannot be compared with all of them at once. What
the gluing uses is only the local form — see
`Stacks.Conormal.commonChartSectionsIso_isCompatibleOnBasis`, which refines around each point
anyway, the containment of two opens of `F` giving no containment of the charts upstairs.

`Stacks.Conormal.CommonChartAssociatedGradedEquiv.ofAllCharts` builds this from the full family
with the compatibility for every nested pair, so nothing that could be given in the stronger
shape is lost. -/
structure CommonChartAssociatedGradedEquiv {ι : Type w} (𝒞 : ι → CommonChart j j') where
  /-- The opens of the family form a basis of the topology of the source. -/
  isBasis : Opens.IsBasis (Set.range fun a => commonChartOpens j j' (𝒞 a))
  /-- The comparison of associated graded algebras over each member of the family. -/
  chart (a : ι) :
    ChartAssociatedGradedEquiv j j' (𝒞 a).left.1 (𝒞 a).right.1 (𝒞 a).preimage_eq.symm
  /-- Two members and a point of both of their opens admit a member refining both in both ambient
  schemes, over which the comparison is the restriction of the comparison over each of the two. -/
  restrict (a b : ι) (x : F) (hxa : x ∈ commonChartOpens j j' (𝒞 a))
      (hxb : x ∈ commonChartOpens j j' (𝒞 b)) :
    ∃ (k : ι) (_ : x ∈ commonChartOpens j j' (𝒞 k))
      (hka : (𝒞 k).left.1.1 ≤ (𝒞 a).left.1.1) (hka' : (𝒞 k).right.1.1 ≤ (𝒞 a).right.1.1)
      (hkb : (𝒞 k).left.1.1 ≤ (𝒞 b).left.1.1) (hkb' : (𝒞 k).right.1.1 ≤ (𝒞 b).right.1.1),
      IsChartRestriction j j' (𝒞 a).left.1 (𝒞 k).left.1 (𝒞 a).right.1 (𝒞 k).right.1
          (chart a) (chart k) hka hka' ∧
        IsChartRestriction j j' (𝒞 b).left.1 (𝒞 k).left.1 (𝒞 b).right.1 (𝒞 k).right.1
          (chart b) (chart k) hkb hkb'

/-- **The family of all common charts, with the comparison compatible with restriction between
every nested pair, is such a comparison.** The basis is `commonChart_isBasis` and the refining
member is produced by `Stacks.Conormal.exists_commonChart_refine`, the two restriction conditions
being instances of the hypothesis. The hypothesis is strictly stronger than the `restrict` field,
so this is the statement that nothing giveable in the stronger shape is lost; for the data being
available at all see `Stacks.Conormal.CommonChartAssociatedGradedEquiv.diagonal`. -/
def CommonChartAssociatedGradedEquiv.ofAllCharts
    (ch : ∀ C : CommonChart j j',
      ChartAssociatedGradedEquiv j j' C.left.1 C.right.1 C.preimage_eq.symm)
    (hres : ∀ (C D : CommonChart j j') (hleft : D.left.1.1 ≤ C.left.1.1)
        (hright : D.right.1.1 ≤ C.right.1.1),
      IsChartRestriction j j' C.left.1 D.left.1 C.right.1 D.right.1 (ch C) (ch D)
        hleft hright) :
    CommonChartAssociatedGradedEquiv j j' (id : CommonChart j j' → CommonChart j j') where
  isBasis := commonChart_isBasis j j'
  chart := ch
  restrict C D x hxC hxD := by
    obtain ⟨E, hxE, hEC, hED, hEC', hED'⟩ := exists_commonChart_refine j j' C D x hxC hxD
    exact ⟨E, hxE, hEC, hEC', hED, hED', hres C E hEC hEC', hres D E hED hED'⟩

/-- **The comparison of the conormal algebra of one immersion with itself.** The family is the
diagonal one: a chart of `i`, taken as a common chart of `i` with itself, and the identity
comparison `Stacks.Conormal.ChartAssociatedGradedEquiv.refl` over it. The preimages of the charts
form a basis by `Stacks.Conormal.conormalChart_isBasis`, and a refining member around a point of
two charts is an affine open of the ambient inside both and inside the coborder of the range, the
restriction condition being `Stacks.Conormal.isChartRestriction_refl`.

This is the check that the data of a `CommonChartAssociatedGradedEquiv` is available at all. It
cannot be read off the family of *all* common charts of `i` with itself: such a chart is a pair of
charts with the same preimage, not one chart, and the identity comparison says nothing about a
pair of distinct ambient charts. -/
def CommonChartAssociatedGradedEquiv.diagonal (i : F ⟶ X) [IsImmersion i] :
    CommonChartAssociatedGradedEquiv i i fun V : ConormalChart i => ⟨V, V, rfl⟩ where
  isBasis := conormalChart_isBasis i
  chart V := ChartAssociatedGradedEquiv.refl i V.1
  restrict V W x hxV hxW := by
    obtain ⟨E, hEa, hxE, hE⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show i x ∈ V.1.1 ⊓ W.1.1 ⊓ i.coborderRange from ⟨⟨hxV, hxW⟩, V.2 hxV⟩)
    refine ⟨⟨⟨E, hEa⟩, hE.trans inf_le_right⟩, hxE,
      hE.trans (inf_le_left.trans inf_le_left), hE.trans (inf_le_left.trans inf_le_left),
      hE.trans (inf_le_left.trans inf_le_right), hE.trans (inf_le_left.trans inf_le_right),
      isChartRestriction_refl i V.1 ⟨E, hEa⟩ _, isChartRestriction_refl i W.1 ⟨E, hEa⟩ _⟩

/-- **The concrete identification of the chart rings of the members of the family with quotients
of ambient rings produces the whole comparison.** Over each member the data is: an ambient ring
with an ideal `J` for the filtration, a presentation of each of the two chart rings as a quotient
of it carrying the kernel ideal to the ideal `J` generates, a comparison of the associated graded
algebras of the two quotients which is induced by the identity of the ambient ring, and the
compatibility that the two presentations present the same open of the source. For two members and
a point of both of their opens the data is a refining member together with a comparison of the
ambient presentations with each of the two, `Stacks.Conormal.ChartQuotientPresentationHom`; only
its existence is used, so it is asked for as a `Nonempty`.

The ambient ring may differ from member to member, which is what Stacks 0CAY needs: there it is a
polynomial ring over `𝒪^∧_{S,s}` in as many variables as the chosen presentation of that chart of
`Y` has generators. That is also why the comparison of two presentations is asked for only at a
refining member: it is a renaming of finitely many variables, and the variables of a presentation
of one chart cannot contain those of all the charts below it. -/
noncomputable def commonChartAssociatedGradedEquivOfPresentations
    {ι : Type w} (𝒞 : ι → CommonChart j j')
    (hbasis : Opens.IsBasis (Set.range fun a => commonChartOpens j j' (𝒞 a)))
    (A : ι → Type v) [∀ a, CommRing (A a)]
    (J R R' : ∀ a : ι, Ideal (A a))
    (pL : ∀ a : ι, ChartQuotientPresentation j (𝒞 a).left.1 (J a) (R a))
    (pR : ∀ a : ι, ChartQuotientPresentation j' (𝒞 a).right.1 (J a) (R' a))
    (e : ∀ a : ι, AssociatedGraded.GradedAlgEquiv (J a) (A a ⧸ R a) (A a ⧸ R' a))
    (hind : ∀ a : ι, (e a).IsInducedByIdentity)
    (hcompat : ∀ (a : ι) (z : A a),
      (AddEquiv.cast (M := fun T : F.Opens => Γ(F, T)) (𝒞 a).preimage_eq.symm)
          ((pR a).toSourceHom z) = (pL a).toSourceHom z)
    (phi : ∀ (a b : ι) (x : F), x ∈ commonChartOpens j j' (𝒞 a) →
      x ∈ commonChartOpens j j' (𝒞 b) →
      ∃ (k : ι) (_ : x ∈ commonChartOpens j j' (𝒞 k))
        (hka : (𝒞 k).left.1.1 ≤ (𝒞 a).left.1.1) (hka' : (𝒞 k).right.1.1 ≤ (𝒞 a).right.1.1)
        (hkb : (𝒞 k).left.1.1 ≤ (𝒞 b).left.1.1) (hkb' : (𝒞 k).right.1.1 ≤ (𝒞 b).right.1.1),
        Nonempty (ChartQuotientPresentationHom hka hka' (pL a) (pR a) (pL k) (pR k)) ∧
          Nonempty (ChartQuotientPresentationHom hkb hkb' (pL b) (pR b) (pL k) (pR k))) :
    CommonChartAssociatedGradedEquiv j j' 𝒞 where
  isBasis := hbasis
  chart a := ChartAssociatedGradedEquiv.ofQuotientPresentation (pL a) (pR a) (e a) (hcompat a)
  restrict a b x hxa hxb := by
    obtain ⟨k, hxk, hka, hka', hkb, hkb', ⟨phia⟩, ⟨phib⟩⟩ := phi a b x hxa hxb
    exact ⟨k, hxk, hka, hka', hkb, hkb',
      isChartRestriction_ofQuotientPresentation (hind a) (hind k) phia (hcompat a) (hcompat k),
      isChartRestriction_ofQuotientPresentation (hind b) (hind k) phib (hcompat b) (hcompat k)⟩

variable {ι : Type w} {𝒞 : ι → CommonChart j j'} (c : CommonChartAssociatedGradedEquiv j j' 𝒞)

/-- **The degreewise comparison of the sections of the two conormal algebras over a member of the
family**, built from the comparison of associated graded algebras over that member by
`Stacks.Conormal.chartSectionsIsoInt`; both chart-local presentations are available over the
open of a common chart, by `Stacks.Conormal.commonChartOpens_eq_left` and
`Stacks.Conormal.commonChartOpens_eq_right`. -/
def commonChartSectionsIso (n : ℤ) (a : ι) :
    ((conormalAlgebra j).algebra.piece n).val.obj (op (commonChartOpens j j' (𝒞 a))) ≅
      ((conormalAlgebra j').algebra.piece n).val.obj (op (commonChartOpens j j' (𝒞 a))) :=
  chartSectionsIsoInt j j' (𝒞 a).left.1 (𝒞 a).right.1
    (isClosedImmersion_commonChart_left j j' (𝒞 a))
    (isClosedImmersion_commonChart_right j j' (𝒞 a)) (c.chart a) n

/-- **The comparison over a member of the family contained in another one in both ambients
commutes with the restriction between the two.** This is
`Stacks.Conormal.chartSectionsIsoInt_restrict` for the two pairs of charts, the containments in
the two ambients and the restriction condition being the hypotheses. The latter is a hypothesis
and not a field of `c`: the structure provides it only at a refining member, which is all the
gluing needs. -/
theorem commonChartSectionsIso_restrict (a b : ι)
    (hleft : (𝒞 b).left.1.1 ≤ (𝒞 a).left.1.1) (hright : (𝒞 b).right.1.1 ≤ (𝒞 a).right.1.1)
    (hres : IsChartRestriction j j' (𝒞 a).left.1 (𝒞 b).left.1 (𝒞 a).right.1 (𝒞 b).right.1
      (c.chart a) (c.chart b) hleft hright) (n : ℤ)
    (hW : commonChartOpens j j' (𝒞 b) ≤ commonChartOpens j j' (𝒞 a))
    (z : ((conormalAlgebra j).algebra.piece n).val.obj (op (commonChartOpens j j' (𝒞 a)))) :
    (commonChartSectionsIso j j' c n b).hom
        (((conormalAlgebra j).algebra.piece n).val.map (homOfLE hW).op z) =
      ((conormalAlgebra j').algebra.piece n).val.map (homOfLE hW).op
        ((commonChartSectionsIso j j' c n a).hom z) :=
  chartSectionsIsoInt_restrict j j' (𝒞 a).left.1 (𝒞 b).left.1 (𝒞 a).right.1 (𝒞 b).right.1
    (isClosedImmersion_commonChart_left j j' (𝒞 a))
    (isClosedImmersion_commonChart_left j j' (𝒞 b))
    (isClosedImmersion_commonChart_right j j' (𝒞 a))
    (isClosedImmersion_commonChart_right j j' (𝒞 b))
    (c.chart a) (c.chart b) hleft hright hres hW n z

/-- **The degreewise family of comparisons over the members of the family commutes with the
restriction maps between them.** The containment of the two opens of `F` gives no containment of
the charts in the two ambient schemes, so the two sections are compared locally: around each
point of the smaller open the `restrict` field of `c` produces a member refining both in both
ambients, and there `commonChartSectionsIso_restrict` applies twice. Those refinements cover the
smaller open, and the target is a sheaf.

This is why `restrict` is asked for only at a refining member: the proof refines around each
point in any case, so the compatibility for every nested pair of members would be used nowhere.
-/
theorem commonChartSectionsIso_isCompatibleOnBasis (n : ℤ) :
    Stacks.BasisRestriction.IsCompatibleOnBasis
      ((conormalAlgebra j).algebra.piece n) ((conormalAlgebra j').algebra.piece n)
      (fun a => commonChartOpens j j' (𝒞 a))
      fun a => (commonChartSectionsIso j j' c n a).hom := by
  intro a b hba s
  set P : ι → Prop := fun k =>
    ∃ (hka : (𝒞 k).left.1.1 ≤ (𝒞 a).left.1.1) (hka' : (𝒞 k).right.1.1 ≤ (𝒞 a).right.1.1)
      (hkb : (𝒞 k).left.1.1 ≤ (𝒞 b).left.1.1) (hkb' : (𝒞 k).right.1.1 ≤ (𝒞 b).right.1.1),
      IsChartRestriction j j' (𝒞 a).left.1 (𝒞 k).left.1 (𝒞 a).right.1 (𝒞 k).right.1
          (c.chart a) (c.chart k) hka hka' ∧
        IsChartRestriction j j' (𝒞 b).left.1 (𝒞 k).left.1 (𝒞 b).right.1 (𝒞 k).right.1
          (c.chart b) (c.chart k) hkb hkb'
  have hle : ∀ k : { k : ι // P k },
      commonChartOpens j j' (𝒞 k.1) ≤ commonChartOpens j j' (𝒞 b) := by
    intro k
    obtain ⟨-, -, hkb, -, -, -⟩ := k.2
    exact j.preimage_mono hkb
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover
    ((conormalAlgebra j').algebra.piece n)
    (fun k : { k : ι // P k } => commonChartOpens j j' (𝒞 k.1)) hle (fun x hx => ?_) _ _
    fun k => ?_
  · obtain ⟨k, hxk, hka, hka', hkb, hkb', hresa, hresb⟩ := c.restrict a b x (hba hx) hx
    exact ⟨⟨k, hka, hka', hkb, hkb', hresa, hresb⟩, hxk⟩
  · obtain ⟨hka, hka', hkb, hkb', hresa, hresb⟩ := k.2
    have hka'' : commonChartOpens j j' (𝒞 k.1) ≤ commonChartOpens j j' (𝒞 a) :=
      (hle k).trans hba
    have hsmall := commonChartSectionsIso_restrict j j' c b k.1 hkb hkb' hresb n (hle k)
      (((conormalAlgebra j).algebra.piece n).val.map (homOfLE hba).op s)
    have hbig := commonChartSectionsIso_restrict j j' c a k.1 hka hka' hresa n hka'' s
    change ((conormalAlgebra j').algebra.piece n).val.map (homOfLE (hle k)).op
          ((commonChartSectionsIso j j' c n b).hom
            (((conormalAlgebra j).algebra.piece n).val.map (homOfLE hba).op s)) =
        ((conormalAlgebra j').algebra.piece n).val.map (homOfLE (hle k)).op
          (((conormalAlgebra j').algebra.piece n).val.map (homOfLE hba).op
            ((commonChartSectionsIso j j' c n a).hom s))
    rw [← hsmall, ← ((conormalAlgebra j).algebra.piece n).val.map_comp_apply,
      ← ((conormalAlgebra j').algebra.piece n).val.map_comp_apply]
    exact hbig

/-- **The degreewise family of comparisons over the members of the family is multiplicative over
each member**, which is `Stacks.Conormal.chartSectionsIsoInt_mul` at that chart. -/
theorem commonChartSectionsIso_isMultiplicativeOnBasis :
    Stacks.BasisRestriction.IsMultiplicativeOnBasis
      (conormalAlgebra j).algebra (conormalAlgebra j').algebra
      (fun a => commonChartOpens j j' (𝒞 a))
      fun n a => (commonChartSectionsIso j j' c n a).hom :=
  fun p q a x y =>
    chartSectionsIsoInt_mul j j' (𝒞 a).left.1 (𝒞 a).right.1
      (isClosedImmersion_commonChart_left j j' (𝒞 a))
      (isClosedImmersion_commonChart_right j j' (𝒞 a)) (c.chart a) p q x y

include c in
/-- **The conormal algebras of two immersions out of one source are isomorphic as soon as their
associated graded algebras are compared over a family of common charts whose opens form a basis,
compatibly with restriction at a refining member.** This is the conclusion
`Stacks.ConormalApproximation.HasConormalIso` asks for. -/
theorem nonempty_conormalAlgebra_iso_of_commonChartAssociatedGradedEquiv :
    Nonempty ((conormalAlgebra j).algebra ≅ (conormalAlgebra j').algebra) :=
  nonempty_conormalAlgebra_iso_of_commonChartIso j j' 𝒞 (commonChartSectionsIso j j' c) c.isBasis
    (commonChartSectionsIso_isCompatibleOnBasis j j' c)
    (commonChartSectionsIso_isMultiplicativeOnBasis j j' c)

end Stacks.Conormal

end
