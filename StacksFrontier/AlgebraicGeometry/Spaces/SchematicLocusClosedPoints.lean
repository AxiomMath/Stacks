module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPointSpaceSober
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection

/-!
# An algebraic space whose closed points lie in the schematic locus is a scheme

Let `X` be an algebraic space over a scheme `S` whose space of points `|X|` is quasi-compact and
Kolmogorov.  The schematic locus of `X` (Stacks 03JH) is an open subspace, so its point set is an
open subset of `|X|` (Stacks 03BZ).  An open subset of a quasi-compact Kolmogorov space which
contains every closed point is the whole space, since a nonempty closed subset of such a space
contains a closed point.  Hence if every closed point of `|X|` lies in the schematic locus, the
inclusion of the schematic locus is surjective on points, and `X` is a scheme.

For a Noetherian algebraic space `|X|` is a sober Noetherian topological space (Stacks 04ZG), so
the hypotheses on `|X|` hold.

## Main results

* `AlgebraicGeometry.Space.surjective_pointsMap_schematicLocus_of_isClosed_mem`: the point set
  of the schematic locus is everything as soon as it contains every closed point, on a
  quasi-compact Kolmogorov space of points.
* `AlgebraicGeometry.Space.isRepresentable_of_isClosed_mem_range_schematicLocus`: an algebraic
  space with quasi-compact Kolmogorov space of points whose closed points lie in the schematic
  locus is a scheme.
* `AlgebraicGeometry.Space.isRepresentable_of_isNoetherian_of_isClosed_mem_range`: a Noetherian
  algebraic space each of whose closed points lies in a representable open subspace is a scheme.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04ZG](https://stacks.math.columbia.edu/tag/04ZG)
* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The point set of the schematic locus is everything once it contains the closed points.**
On a quasi-compact Kolmogorov space of points, the open point set of the schematic locus
(Stacks 03JH, Stacks 03BZ) has closed complement, and a nonempty closed subset of a
quasi-compact Kolmogorov space contains a closed point. -/
theorem surjective_pointsMap_schematicLocus_of_isClosed_mem
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    [CompactSpace (points B S hS F)] [T0Space (points B S hS F)]
    (h : ∀ x : points B S hS F, IsClosed ({x} : Set (points B S hS F)) →
      x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
        (schematicLocus B S hS F).ι)) :
    Function.Surjective (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) := by
  have hopen : IsOpen (Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).1.2
  intro y
  by_contra hy
  obtain ⟨x, hx, hxc⟩ := hopen.isClosed_compl.exists_closed_singleton ⟨y, hy⟩
  exact hx (h x hxc)

/-- **An algebraic space whose closed points lie in the schematic locus is a scheme**, provided
its space of points is quasi-compact and Kolmogorov. -/
theorem isRepresentable_of_isClosed_mem_range_schematicLocus
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    [CompactSpace (points B S hS F)] [T0Space (points B S hS F)]
    (h : ∀ x : points B S hS F, IsClosed ({x} : Set (points B S hS F)) →
      x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
        (schematicLocus B S hS F).ι)) :
    F.IsRepresentable :=
  isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hF
    (surjective_pointsMap_schematicLocus_of_isClosed_mem B S hS hF h)

/-- A point lying on a representable open subspace lies in the schematic locus: the open
subspace is contained in the schematic locus (Stacks 03JH, maximality), and its inclusion
factors through that of the schematic locus. -/
theorem mem_range_pointsMap_schematicLocus_of_mem_range
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) (hG : IsOpenSubspace B S hS G)
    (hGrep : G.toFunctor.IsRepresentable) {x : points B S hS F}
    (hx : x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) := by
  obtain ⟨y, rfl⟩ := hx
  have hle := le_schematicLocus B S hS F G hG hGrep
  refine ⟨pointsMap B S hS G.toFunctor (Subfunctor.homOfLe hle) y, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS _ (schematicLocus B S hS F).ι),
    ← pointsMap_comp, Subfunctor.homOfLe_ι]

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A Noetherian algebraic space each of whose closed points lies on a representable open
subspace is a scheme.**  The space of points of a Noetherian algebraic space is a sober
Noetherian topological space (Stacks 04ZG), in particular quasi-compact and Kolmogorov, so
`AlgebraicGeometry.Space.isRepresentable_of_isClosed_mem_range_schematicLocus` applies. -/
theorem isRepresentable_of_isNoetherian_of_isClosed_mem_range
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hN : IsNoetherian B S hS hZ F)
    (h : ∀ x : points B S hS F, IsClosed ({x} : Set (points B S hS F)) →
      ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
        x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    F.IsRepresentable := by
  obtain ⟨hsober, hnoeth⟩ := stacksSober_and_noetherianSpace_points_of_isNoetherian B S hS hZ hF hN
  have : T0Space (points B S hS F) := (stacksSober_iff_t0_and_quasiSober.1 hsober).1
  refine isRepresentable_of_isClosed_mem_range_schematicLocus B S hS hF fun x hx => ?_
  obtain ⟨G, hG, hGrep, hxG⟩ := h x hx
  exact mem_range_pointsMap_schematicLocus_of_mem_range B S hS G hG hGrep hxG

end AlgebraicGeometry.Space

end
