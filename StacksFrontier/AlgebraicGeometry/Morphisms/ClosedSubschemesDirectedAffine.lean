module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Directed families of closed subsets landing in an open, and affineness

Let `X` be a quasi-compact scheme and `(Z α)` a family of closed subsets of `X` which is
directed downwards (any two members contain a third).  If the intersection of the family lies
in an open subset `U`, then already one member lies in `U`.  This is the compactness argument
of EGA I 7.2.5 in the form needed for stabilisers of rational functions: the complement of `U`
is closed, hence quasi-compact, and it is covered by the open complements of the `Z α`.

As a consequence, a closed subscheme of `X` (more generally, any `Z` with an affine morphism to
`X`) whose underlying set lies in an affine open `U` is affine: its preimage of `U` is affine
and is all of `Z`.

## Main results

* `AlgebraicGeometry.Scheme.exists_subset_of_directed_iInter_subset`: a downward directed family
  of closed subsets whose intersection lies in an open `U` has a member lying in `U`.
* `AlgebraicGeometry.isAffine_of_range_subset_isAffineOpen`: if `i : Z ⟶ X` is affine and
  its image lies in an affine open of `X`, then `Z` is affine; in particular for a closed
  immersion.
* `AlgebraicGeometry.Scheme.exists_isAffine_of_directed`: the two together — for a downward
  directed family of closed immersions into `X` whose images meet in a subset of an affine
  open, some member is affine.

## Implementation notes

Neither quasi-separatedness of `X` nor separatedness is needed: the first statement uses only
that `X` is quasi-compact (`IsClosed.isCompact`), and the second only that the open is affine
and the morphism affine (`AlgebraicGeometry.IsAffineOpen.preimage`).
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A downward directed family of closed subsets whose intersection lies in an open set has a
member lying in that open set**, in a quasi-compact space. -/
@[ega "0 2.1.3" "partial"]
theorem _root_.CompactSpace.exists_subset_of_directed_iInter_subset {T : Type*}
    [TopologicalSpace T] [CompactSpace T] {ι : Type*} [Nonempty ι] (Z : ι → Set T)
    (hZ : ∀ i, IsClosed (Z i)) (hdir : Directed (· ⊇ ·) Z) {U : Set T} (hU : IsOpen U)
    (h : ⋂ i, Z i ⊆ U) : ∃ i, Z i ⊆ U := by
  obtain ⟨i, hi⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed Z hZ
    (Set.disjoint_compl_left_iff_subset.mpr h) hdir
  exact ⟨i, Set.disjoint_compl_left_iff_subset.mp hi⟩

/-- **EGA I 7.2.5, the compactness step.**  For a quasi-compact scheme `X`, a downward directed
family of closed subsets whose intersection lies in an open `U` has a member lying in `U`. -/
theorem Scheme.exists_subset_of_directed_iInter_subset (X : Scheme.{u}) [CompactSpace X]
    {ι : Type*} [Nonempty ι] (Z : ι → Set X) (hZ : ∀ i, IsClosed (Z i))
    (hdir : Directed (· ⊇ ·) Z) (U : X.Opens) (h : ⋂ i, Z i ⊆ U) : ∃ i, Z i ⊆ U :=
  CompactSpace.exists_subset_of_directed_iInter_subset Z hZ hdir U.isOpen h

/-- **A scheme with an affine morphism to `X` landing in an affine open of `X` is affine.**  In
particular a closed subscheme of `X` whose underlying set lies in an affine open is affine. -/
theorem isAffine_of_range_subset_isAffineOpen {Z X : Scheme.{u}} (i : Z ⟶ X) [IsAffineHom i]
    {U : X.Opens} (hU : IsAffineOpen U) (h : Set.range i.base ⊆ U) : IsAffine Z := by
  have hpre : i ⁻¹ᵁ U = ⊤ := eq_top_iff.mpr fun z _ ↦ h ⟨z, rfl⟩
  have htop : IsAffineOpen (⊤ : Z.Opens) := hpre ▸ hU.preimage i
  have : IsAffine (⊤ : Z.Opens).toScheme := htop
  exact IsAffine.of_isIso Z.topIso.inv

/-- **A downward directed family of closed subschemes meeting inside an affine open has an affine
member.**  For a quasi-compact scheme `X` and closed immersions `i a : Z a ⟶ X` whose images
form a downward directed family with intersection inside an affine open `U`, some `Z a` is
affine. -/
theorem Scheme.exists_isAffine_of_directed (X : Scheme.{u}) [CompactSpace X] {ι : Type*}
    [Nonempty ι] {Z : ι → Scheme.{u}} (i : ∀ a, Z a ⟶ X) [∀ a, IsClosedImmersion (i a)]
    (hdir : Directed (· ⊇ ·) fun a ↦ Set.range (i a).base) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⋂ a, Set.range (i a).base ⊆ U) : ∃ a, IsAffine (Z a) := by
  obtain ⟨a, ha⟩ := X.exists_subset_of_directed_iInter_subset _
    (fun a ↦ (i a).isClosedEmbedding.isClosed_range) hdir U h
  exact ⟨a, isAffine_of_range_subset_isAffineOpen (i a) hU ha⟩

end AlgebraicGeometry

end
