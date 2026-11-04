module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality

/-!
# The affine charts of an immersion

Let `i : Z ⟶ X` be an immersion of schemes. The affine opens `U` of `X` contained in
`i.coborderRange` are exactly those over which `i` restricts to a closed immersion
(`AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange`), and they are the opens over
which the conormal sheaf and the conormal algebra of `i` have their affine-local descriptions by
the powers of a kernel ideal. For such a description to determine a morphism of sheaves on `Z`
the preimages `i ⁻¹ᵁ U` must cover `Z` finely enough, and they do: they form a *basis* of the
topology of `Z`.

## Main definitions

* `Stacks.Conormal.ConormalChart`: the affine opens of `X` contained in `i.coborderRange`, and
  `Stacks.Conormal.conormalChartFunctor`, their preimages in `Z`.

## Main results

* `Stacks.Conormal.exists_chart_near`: every point of an open of `Z` has a chart of `i` around
  it whose preimage is contained in that open.
* `Stacks.Conormal.conormalChart_isBasis`: **the preimages of the charts form a basis of the
  topology of `Z`.**

## Implementation notes

The charts are indexed by the subtype `ConormalChart i` rather than by a predicate on
`X.affineOpens`, so that the family of their preimages is a function out of a type and can be fed
to the basis API, which works with `Set.range`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-- Every point of an open of the source has an affine chart of the ambient scheme around it
whose preimage is contained in that open. -/
theorem exists_chart_near (i : Z ⟶ X) [IsImmersion i] (V : Z.Opens) (x : Z)
    (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ i ⁻¹ᵁ U.1 ∧ i ⁻¹ᵁ U.1 ≤ V ∧ U.1 ≤ i.coborderRange := by
  obtain ⟨O, hO, hpre⟩ := i.isEmbedding.isInducing.isOpen_iff.mp V.2
  have hxO : i x ∈ O := show x ∈ i ⁻¹' O by rw [hpre]; exact hx
  have hxW : i x ∈ i.coborderRange := subset_coborder (⟨x, rfl⟩ : i x ∈ Set.range i)
  obtain ⟨W, ⟨A, hA, rfl⟩, hxA, hWA⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show i x ∈ O ∩ i.coborderRange from ⟨hxO, hxW⟩)
      (hO.inter i.coborderRange.2)
  refine ⟨⟨A, hA⟩, hxA, fun y hy ↦ ?_, hWA.trans inf_le_right⟩
  simpa [hpre] using (show y ∈ i ⁻¹' O from (hWA hy).1)

/-- The affine opens of the ambient scheme contained in the coborder of the range, which is
exactly the set of affine opens over which the immersion restricts to a closed immersion. -/
abbrev ConormalChart (i : Z ⟶ X) [IsImmersion i] :=
  { U : X.affineOpens // U.1 ≤ i.coborderRange }

/-- **For a closed immersion the coborder of the range is everything**, the range being closed. -/
theorem coborderRange_eq_top (i : Z ⟶ X) [IsClosedImmersion i] : i.coborderRange = ⊤ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  show x ∈ coborder (Set.range i.base)
  rw [IsClosed.coborder_eq i.isClosedEmbedding.isClosed_range]
  trivial

/-- **Every affine open of the ambient scheme is a chart of a closed immersion.** -/
def conormalChartOfIsClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i] (V : X.affineOpens) :
    ConormalChart i :=
  ⟨V, by rw [coborderRange_eq_top i]; exact le_top⟩

/-- The affine open underlying `conormalChartOfIsClosedImmersion i V` is `V`. -/
@[simp]
theorem conormalChartOfIsClosedImmersion_coe (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens) : (conormalChartOfIsClosedImmersion i V).1 = V :=
  rfl

/-- The preimage of a chart, as a functor from the charts to the opens of the source. -/
def conormalChartFunctor (i : Z ⟶ X) [IsImmersion i] : ConormalChart i ⥤ Z.Opens where
  obj U := i ⁻¹ᵁ U.1.1
  map f := homOfLE (i.preimage_mono f.le)

/-- **The preimages of the charts form a basis of the topology of the source.** -/
theorem conormalChart_isBasis (i : Z ⟶ X) [IsImmersion i] :
    Opens.IsBasis (Set.range (conormalChartFunctor i).obj) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨U, hxU, hUV, hUW⟩ := exists_chart_near i V x hx
  exact ⟨i ⁻¹ᵁ U.1, ⟨⟨U, hUW⟩, rfl⟩, hxU, hUV⟩

end Stacks.Conormal

end
