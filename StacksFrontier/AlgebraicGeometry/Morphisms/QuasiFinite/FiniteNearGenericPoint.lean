module

public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteOverDenseOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of a quasi-finite morphism near a generic point

A quasi-finite morphism is finite over a dense open subscheme of its target. When the target has
finitely many irreducible components, a dense open contains every generic point of an
irreducible component, so such a morphism is finite over an affine open neighbourhood of every
generic point.

## Main results

* `AlgebraicGeometry.genericPoints_subset_of_dense_isOpen`: a dense open subset of a space with
  finitely many irreducible components contains every generic point.
* `AlgebraicGeometry.exists_affineOpen_mem_isFinite_restrict_of_isFinite_restrict`: finiteness
  over an open subscheme passes to an affine open neighbourhood of any of its points.
* `AlgebraicGeometry.exists_affineOpen_mem_isFinite_restrict_of_quasiFinite`: a quasi-finite
  morphism whose target has finitely many irreducible components is finite over an affine open
  neighbourhood of every generic point of the target.

## Implementation notes

The third result takes the route that [Stacks Project, Tag 03HZ] advertises as an alternative to
[Stacks Project, Tag 02NW]: it reaches the conclusion of part (4) of that lemma -- finiteness
over an affine open neighbourhood of a generic point -- from finiteness over a dense open,
which is [Stacks Project, Tag 03I1], rather than from the chart-by-chart argument of Tag 02NW.
Because of that, it does not need Tag 02NW's quasi-separatedness hypothesis; in exchange it
needs the target to have finitely many irreducible components, which is what makes a dense open
reach every generic point. Tag 03HZ itself asserts no more than the statement of Tag 03I1, so it
is registered there, on `AlgebraicGeometry.exists_dense_open_isFinite_of_quasiFinite`, and not on
this corollary.

In this development a quasi-finite morphism is the unbundled conjunction of
`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.LocallyQuasiFinite` and
`AlgebraicGeometry.QuasiCompact`, as explained in
`StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs`.

For a generic point `x`, the complement of the union of the irreducible components other than
`closure {x}` is open, and is nonempty precisely because `closure {x}` is not covered by the
others -- this is where finiteness of the set of components enters. A dense open therefore meets
it, and any point it meets it in specializes from `x`, so the open contains `x`.

## References

* [Stacks Project, Tag 03HZ](https://stacks.math.columbia.edu/tag/03HZ)
* [Stacks Project, Tag 03I1](https://stacks.math.columbia.edu/tag/03I1)
* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.Morphisms.isFinite_respectsIso

/-- A dense open subset of a space with finitely many irreducible components contains every
generic point of an irreducible component. -/
theorem genericPoints_subset_of_dense_isOpen {T : Type*} [TopologicalSpace T]
    (hfin : (irreducibleComponents T).Finite) {U : Set T} (hU : IsOpen U) (hd : Dense U) :
    genericPoints T ⊆ U := by
  intro x hx
  have hZ : closure ({x} : Set T) ∈ irreducibleComponents T := hx
  obtain ⟨z, hzU, hzO⟩ := hd.exists_mem_open
    (hfin.sdiff.isClosed_sUnion fun W hW ↦
      isClosed_of_mem_irreducibleComponents W hW.1).isOpen_compl
    (by
      rw [← closure_nonempty_iff,
        closure_sUnion_irreducibleComponents_sdiff_singleton hfin _ hZ]
      exact hZ.1.nonempty)
  have hzZ : z ∈ closure ({x} : Set T) := by
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton hfin _ hZ]
    exact subset_closure hzO
  exact (specializes_iff_forall_open.mp (specializes_iff_mem_closure.mpr hzZ)) U hU hzU

/-- Finiteness over an open subscheme is inherited by an affine open neighbourhood of any of its
points: shrink the open to an affine one from the basis of affine opens, and restrict. -/
theorem exists_affineOpen_mem_isFinite_restrict_of_isFinite_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hUfin : IsFinite (f ∣_ U))
    {η : Y} (hηU : η ∈ U) :
    ∃ V : Y.affineOpens, η ∈ V.1 ∧ IsFinite (f ∣_ V.1) := by
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hηV₀, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hηU U.isOpen
  refine ⟨⟨V₀, hV₀⟩, hηV₀, ?_⟩
  have : IsFinite (f ∣_ U) := hUfin
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ V₀) = V₀ := by
    ext y
    refine ⟨?_, fun hy => ⟨⟨y, hVU hy⟩, hy, rfl⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact hz
  have hrestrict : IsFinite ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V₀)) := inferInstance
  have hone := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V₀))).mp hrestrict
  rwa [himg] at hone

/-- A quasi-finite morphism whose target has finitely many irreducible components is finite over
an affine open neighbourhood of every generic point of an irreducible component of the target.
This reaches the conclusion of part (4) of [Stacks Project, Tag 02NW] along the route that
[Stacks Project, Tag 03HZ] advertises, that is from finiteness over a dense open
([Stacks Project, Tag 03I1]) and without assuming the morphism quasi-separated. -/
theorem exists_affineOpen_mem_isFinite_restrict_of_quasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f]
    [Finite (irreducibleComponents Y)] (η : Y) (hη : η ∈ genericPoints Y) :
    ∃ V : Y.affineOpens, η ∈ V.1 ∧ IsFinite (f ∣_ V.1) := by
  obtain ⟨U, hUdense, hUfin⟩ := exists_dense_open_isFinite_of_quasiFinite f
  exact exists_affineOpen_mem_isFinite_restrict_of_isFinite_restrict f hUfin
    (genericPoints_subset_of_dense_isOpen (Set.toFinite _) U.isOpen hUdense hη)

end AlgebraicGeometry

end
