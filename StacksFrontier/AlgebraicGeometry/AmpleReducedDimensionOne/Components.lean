module

public import StacksFrontier.AlgebraicGeometry.ComponentIntersectionDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.ReducedCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The irreducible components of a one-dimensional scheme as a closed cover

The proof of [Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) begins with the
irreducible components `Z₁, …, Z_n` of a Noetherian scheme `X`, viewed as *reduced* closed
subschemes, and with the set `T = ⋃_{i ≠ j} Z_i ∩ Z_j` of points lying on more than one of them.
Everything downstream — the glueing of [Tag 09NE](https://stacks.math.columbia.edu/tag/09NE), the
affineness criterion of [Tag 09NL](https://stacks.math.columbia.edu/tag/09NL) — consumes that data
as a *family* `Z : ι → Scheme` together with closed immersions `Z i ⟶ X`, a surjectivity statement
and a discreteness statement about the pairwise intersections.  This file packages it.

The components are indexed by themselves: `ι` is the subtype `irreducibleComponents ↥X`, which is
finite because `X` is Noetherian.  No enumeration has to be chosen, and `Subtype.val_injective`
discharges the injectivity that the topological statements of
`StacksDraft.AlgebraicGeometry.F3b.ComponentIntersectionDimensionOne.Basic` ask for.

## Main definitions

* `Stacks.AmpleReducedDimensionOne.componentScheme`: an irreducible component with its reduced
  induced scheme structure, `(vanishingIdeal Z).subscheme`.
* `Stacks.AmpleReducedDimensionOne.componentι`: its closed immersion into `X`.
* `Stacks.AmpleReducedDimensionOne.componentOverlap`: the set `T`.

## Main results

* `Stacks.AmpleReducedDimensionOne.range_componentι`: the range of `componentι` is the component.
* `Stacks.AmpleReducedDimensionOne.exists_componentι_eq`: the components cover `X`, in the
  surjectivity form Tag 09NE asks for.
* `Stacks.AmpleReducedDimensionOne.discreteTopology_range_inter_componentι`: two distinct
  components meet in a discrete subspace, which is hypothesis (3) of Tag 09NE.
* `Stacks.AmpleReducedDimensionOne.finite_componentOverlap`: `T` is finite.
* `Stacks.AmpleReducedDimensionOne.mem_componentOverlap_of_mem_range`: a point of one component
  lying on another lies in `T`.
* `Stacks.AmpleReducedDimensionOne.existsUnique_mem_of_notMem_componentOverlap`: a point outside
  `T` lies on exactly one component.

## Implementation notes

`componentScheme` and `componentι` are `abbrev`s rather than `def`s.  As `def`s they would hide
`(vanishingIdeal _).subscheme` from instance search, and the closed-immersion, reducedness and
Noetherianness instances the library states for `subschemeι` and `subscheme` would all have to be
re-declared; reducible, they transfer with nothing supplied.  The same transparency is what lets
`StacksTag09NX.exists_isAmple_subscheme_vanishingIdeal_irreducibleComponent`, which is stated at
the raw spelling, be applied at `componentScheme` directly.

The closedness proof inside the `TopologicalSpace.Closeds` bundle is a `Prop` field, so two
spellings of it give the same term and `componentScheme` is well defined up to nothing at all.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Topology.Irreducible

universe u

namespace Stacks.AmpleReducedDimensionOne

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]

/-! ### The components as a family of closed subschemes -/

/-- An irreducible component of `X` with its reduced induced closed subscheme structure.  This is
the object the proof of Tag 09NX means by "we view these as reduced closed subschemes". -/
@[ega "IV 13.1.2" "partial"]
abbrev componentScheme (C : irreducibleComponents (X : Type u)) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩ : Closeds (X : Type u))).subscheme

/-- The closed immersion of an irreducible component, with its reduced induced structure,
into `X`. -/
abbrev componentι (C : irreducibleComponents (X : Type u)) : componentScheme X C ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩ : Closeds (X : Type u))).subschemeι

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **The range of the inclusion of a component is that component.**  The support of a vanishing
ideal sheaf is the closed set it vanishes on, and the range of `subschemeι` is the support. -/
theorem range_componentι (C : irreducibleComponents (X : Type u)) :
    Set.range (componentι X C).base = (C : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Stacks.AffineClosedUnion.support_vanishingIdeal]
  rfl

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **The components cover `X`**, in the form `∀ x, ∃ i z, f i z = x` in which Tag 09NE and the
reduced case of Tag 09NL ask for a closed cover.  No finiteness is used: every point of any
topological space lies on some irreducible component. -/
theorem exists_componentι_eq (x : X) :
    ∃ (C : irreducibleComponents (X : Type u)) (z : componentScheme X C),
      (componentι X C) z = x := by
  obtain ⟨C, hC, hx⟩ := Set.mem_sUnion.mp
    (sUnion_irreducibleComponents (X := (X : Type u)) ▸ Set.mem_univ x)
  obtain ⟨z, hz⟩ := (range_componentι X ⟨C, hC⟩).ge hx
  exact ⟨⟨C, hC⟩, z, hz⟩

/-- **Two distinct components meet in a discrete subspace**, stated for the ranges of the closed
immersions, which is hypothesis (3) of Tag 09NE verbatim. -/
theorem discreteTopology_range_inter_componentι
    (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    (C D : irreducibleComponents (X : Type u)) (h : C ≠ D) :
    DiscreteTopology
      ↥(Set.range (componentι X C).base ∩ Set.range (componentι X D).base) := by
  rw [range_componentι, range_componentι]
  exact StacksTag09NX.discreteTopology_inter_irreducibleComponents X hdim C.2 D.2
    (Subtype.coe_ne_coe.mpr h)

/-! ### The overlap set `T` -/

/-- The set `T = ⋃_{i ≠ j} Z_i ∩ Z_j` of points of `X` lying on more than one irreducible
component: the complement of the locus where the components are disjoint. -/
def componentOverlap : Set X :=
  (disjointLocus (Subtype.val : irreducibleComponents (X : Type u) → Set X))ᶜ

/-- **`T` is finite**, which is the second sentence of the proof of Tag 09NX. -/
theorem finite_componentOverlap (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    (componentOverlap X).Finite :=
  StacksTag09NX.finite_compl_disjointLocus_irreducibleComponents X hdim

/-- **The part of `T` visible inside one component is finite.**  A closed immersion is injective,
so the preimage of a finite set under it is finite; this is the set `E` with which Tag 09NV is
applied to the component. -/
theorem finite_preimage_componentOverlap (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    (C : irreducibleComponents (X : Type u)) :
    ((componentι X C).base ⁻¹' componentOverlap X).Finite :=
  (finite_componentOverlap X hdim).preimage (componentι X C).isClosedEmbedding.injective.injOn

/-- A point in the image of the inclusion of a component lies in that component. -/
private theorem componentι_mem {X : Scheme.{u}} {C : irreducibleComponents (X : Type u)}
    (z : componentScheme X C) : (componentι X C) z ∈ (C : Set X) :=
  (range_componentι X C).le ⟨z, rfl⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **A point of one component that lies on another lies in `T`.**  This is what turns the
conclusion of Tag 09NV — a section nonvanishing on `E` — into the hypothesis `hs` of Tag 09NE,
which asks for nonvanishing at the points of one component met by another. -/
theorem mem_componentOverlap_of_mem_range {C D : irreducibleComponents (X : Type u)}
    (h : C ≠ D) (z : componentScheme X C)
    (hz : (componentι X C) z ∈ Set.range (componentι X D).base) :
    (componentι X C) z ∈ componentOverlap X := fun hmem =>
  hmem C D h ⟨componentι_mem z, (range_componentι X D).le hz⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **A point outside `T` lies on exactly one irreducible component.**  This is the sentence
"since `x ∉ T` we see that `x ∈ Z_i` for some unique `i`" of the proof of Tag 09NX, and it is the
first thing its last paragraph uses.  Existence is `exists_componentι_eq` and uniqueness is the
definition of the disjointness locus unwound. -/
theorem existsUnique_mem_of_notMem_componentOverlap {x : X} (hx : x ∉ componentOverlap X) :
    ∃! C : irreducibleComponents (X : Type u), x ∈ (C : Set X) := by
  have hdis : x ∈ disjointLocus (Subtype.val : irreducibleComponents (X : Type u) → Set X) :=
    not_not.mp hx
  obtain ⟨C, z, hz⟩ := exists_componentι_eq X x
  have hC : x ∈ (C : Set X) := hz ▸ componentι_mem z
  exact ⟨C, hC, fun D hD => by_contra fun hne => hdis D C hne ⟨hD, hC⟩⟩

end Stacks.AmpleReducedDimensionOne

end
