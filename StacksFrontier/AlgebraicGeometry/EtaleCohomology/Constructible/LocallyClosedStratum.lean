module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.LocallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally closed subschemes and constructible stratifications

A `AlgebraicGeometry.ConstructibleStratification` records a finite partition of an open subscheme
by locally closed subschemes with constructible image, each presented as an object of a big étale
site together with an immersion. This file supplies the constructor: a finite family of pairwise
disjoint locally closed subsets covering the open subscheme, with constructible images, *is* such
a stratification.

The geometric input is the reduced induced subscheme structure on a locally closed subset, which
is assembled here from Mathlib's ideal sheaves. For a closed subset `Z` of a scheme `X`, the
quotient of `X` by the largest ideal sheaf with support `Z` is a closed subscheme of `X` whose
topological image is exactly `Z`. A locally closed subset `L` is closed inside its coborder
`coborder L`, which is open precisely because `L` is locally closed, so the closed construction
carried out inside that open subscheme yields a scheme immersed in `X` with image `L`. Its size
is bounded by that of `X`, which is what places it in the big étale site.

Separately, the file records the topological fact that makes refinements of a constructible cover
admissible input to the constructor: in a finite family of pairwise disjoint sets indexed by a
partial order, if the closure of each member meets only the members at or below its index, then
every member is locally closed.

## Main definitions

* `AlgebraicGeometry.Scheme.closedSubscheme`, `AlgebraicGeometry.Scheme.closedSubschemeι` — the
  reduced induced closed subscheme on a closed subset, and its closed immersion.
* `AlgebraicGeometry.Scheme.coborderOpens` — the coborder of a locally closed subset, as an open
  subscheme.
* `AlgebraicGeometry.Scheme.locallyClosedSubscheme`,
  `AlgebraicGeometry.Scheme.locallyClosedSubschemeι` — the reduced induced subscheme on a locally
  closed subset, and its immersion.
* `AlgebraicGeometry.BigEtaleSite.locallyClosedObj`,
  `AlgebraicGeometry.BigEtaleSite.locallyClosedHom` — that subscheme as an object of a big étale
  site, with its structure morphism.

## Main results

* `isLocallyClosed_of_closure_subset_biUnion_le` — every member of such a finite family is
  locally closed.
* `AlgebraicGeometry.Scheme.range_locallyClosedSubschemeι` — the immersion has image exactly the
  given locally closed subset.
* `AlgebraicGeometry.Scheme.size_locallyClosedSubscheme_lt` — the subscheme stays below every
  cardinal bound the ambient scheme is below.
* `AlgebraicGeometry.BigEtaleSite.range_locallyClosedHom` — the structure morphism of that object
  of the site has image exactly the given locally closed subset, which is what lets
  `AlgebraicGeometry.ConstructibleStratification.ofPartition` read a finite constructible
  partition by locally closed subsets as a constructible stratification.

## Implementation notes

The subscheme layer is spelled with `abbrev`s so that Mathlib's `IsPreimmersion`, `QuasiCompact`
and `IsClosedImmersion` instances for
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` keep applying unchanged: with a `def` the
source of the immersion acquires a second spelling and instance search no longer reaches those
instances.

## References

* [Stacks Project, Tag 01QW](https://stacks.math.columbia.edu/tag/01QW)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

/-! ### Local closedness of the strata of a finite stratification -/

/-- In a finite family of pairwise disjoint subsets indexed by a partial order, if the closure of
each member meets only the members at or below its own index, then every member is locally closed.

Writing `Zᵢ = ⋃_{k ≤ i} Sₖ`, the hypothesis makes `Zᵢ` equal to the union of the closures of its
members, hence closed, and disjointness identifies `Sⱼ` with `Zⱼ` minus the closed set
`⋃_{i < j} Zᵢ`. -/
public theorem isLocallyClosed_of_closure_subset_biUnion_le {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Finite ι] [PartialOrder ι] (S : ι → Set X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hclosure : ∀ j, closure (S j) ⊆ ⋃ i ∈ {i | i ≤ j}, S i) (j : ι) :
    IsLocallyClosed (S j) := by
  classical
  set Z : ι → Set X := fun i => ⋃ k ∈ {k | k ≤ i}, S k with hZdef
  have hZmem (i : ι) (x : X) : x ∈ Z i ↔ ∃ k ≤ i, x ∈ S k := by
    simp only [hZdef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  have hcl (k : ι) (x : X) (hx : x ∈ closure (S k)) : ∃ l ≤ k, x ∈ S l := by
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hclosure k hx
  have hZclosed (i : ι) : IsClosed (Z i) := by
    have hle : Z i = ⋃ k ∈ {k | k ≤ i}, closure (S k) := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨k, hk, hxk⟩ := (hZmem i x).mp hx
        exact Set.mem_biUnion (t := fun k => closure (S k)) hk (subset_closure hxk)
      · simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hx
        obtain ⟨k, hk, hxk⟩ := hx
        obtain ⟨l, hl, hxl⟩ := hcl k x hxk
        exact (hZmem i x).mpr ⟨l, hl.trans hk, hxl⟩
    rw [hle]
    exact (Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure
  have hkey : S j = (⋃ i ∈ {i | i < j}, Z i)ᶜ ∩ Z j := by
    refine Set.Subset.antisymm (fun x hx => ⟨?_, (hZmem j x).mpr ⟨j, le_refl j, hx⟩⟩)
      (fun x hx => ?_)
    · intro hxU
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hxU
      obtain ⟨i, hij, hxi⟩ := hxU
      obtain ⟨k, hki, hxk⟩ := (hZmem i x).mp hxi
      exact Set.disjoint_left.mp (hdisj j k (ne_of_gt (lt_of_le_of_lt hki hij))) hx hxk
    · obtain ⟨k, hkj, hxk⟩ := (hZmem j x).mp hx.2
      rcases eq_or_lt_of_le hkj with rfl | hlt
      · exact hxk
      · refine absurd (Set.mem_biUnion (s := {i | i < j}) (t := Z)
          (show k ∈ {i | i < j} from hlt) ((hZmem k x).mpr ⟨k, le_refl k, hxk⟩)) hx.1
  exact ⟨_, _, ((Set.toFinite _).isClosed_biUnion fun i _ => hZclosed i).isOpen_compl,
    hZclosed j, hkey⟩

namespace AlgebraicGeometry

namespace Scheme

/-! ### The reduced induced subscheme on a closed subset -/

/-- The reduced induced closed subscheme structure on a closed subset of a scheme: the quotient
of `X` by the largest ideal sheaf whose support is `Z`. -/
@[ega "I 5.2.1", ega "IV 4.9.4", sga "3 XV 3.2" "special case"]
public abbrev closedSubscheme (X : Scheme.{u}) (Z : Closeds X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal Z).subscheme

/-- The closed immersion of the reduced induced closed subscheme on a closed subset. -/
@[ega "I 5.2.1", ega "I 5.5.4"]
public abbrev closedSubschemeι (X : Scheme.{u}) (Z : Closeds X) : X.closedSubscheme Z ⟶ X :=
  (IdealSheafData.vanishingIdeal Z).subschemeι

/-- The reduced induced closed subscheme on `Z` has topological image exactly `Z`. -/
public theorem range_closedSubschemeι (X : Scheme.{u}) (Z : Closeds X) :
    Set.range (X.closedSubschemeι Z).base = (Z : Set X) := by
  rw [IdealSheafData.range_subschemeι]
  exact IdealSheafData.coe_support_vanishingIdeal Z

/-! ### The reduced induced subscheme on a locally closed subset -/

variable {X : Scheme.{u}}

/-- The coborder of a locally closed subset, as an open subscheme of the ambient scheme. The
coborder is open exactly because the subset is locally closed, and the subset is closed inside
it. -/
public def coborderOpens {L : Set X} (hL : IsLocallyClosed L) : X.Opens :=
  ⟨coborder L, hL.isOpen_coborder⟩

/-- A locally closed subset is a closed subset of its coborder. -/
public theorem isClosed_preimage_coborderOpens {L : Set X} (hL : IsLocallyClosed L) :
    IsClosed ((coborderOpens hL).ι.base ⁻¹' L) :=
  isClosed_preimage_val_coborder

/-- The largest ideal sheaf on the coborder of `L` with support `L`; its quotient is the reduced
induced subscheme structure on `L`. -/
public abbrev locallyClosedIdeal {L : Set X} (hL : IsLocallyClosed L) :
    IdealSheafData (coborderOpens hL).toScheme :=
  IdealSheafData.vanishingIdeal ⟨_, isClosed_preimage_coborderOpens hL⟩

/-- The reduced induced subscheme structure on a locally closed subset of a scheme: the reduced
induced closed subscheme of the open subscheme `coborder L`, inside which `L` is closed. -/
@[ega "I 5.2.1", ega "I 5.5.4" "more general", sga "3 XV 3.2"]
public abbrev locallyClosedSubscheme {L : Set X} (hL : IsLocallyClosed L) : Scheme.{u} :=
  (locallyClosedIdeal hL).subscheme

/-- The immersion of the reduced induced subscheme on a locally closed subset: a closed immersion
into the open subscheme `coborder L`, followed by that open immersion. -/
@[ega "I 5.2.1", ega "I 5.5.4" "more general", sga "3 XV 3.9" "more general"]
public abbrev locallyClosedSubschemeι {L : Set X} (hL : IsLocallyClosed L) :
    locallyClosedSubscheme hL ⟶ X :=
  (locallyClosedIdeal hL).subschemeι ≫ (coborderOpens hL).ι

/-- The reduced induced subscheme on a locally closed subset is immersed in the ambient
scheme. -/
@[ega "I 4.2.1" "special case", ega "I 5.2.1" "existence", sga "3 XV 3.2" "partial"]
public theorem isImmersion_locallyClosedSubschemeι {L : Set X} (hL : IsLocallyClosed L) :
    IsImmersion (locallyClosedSubschemeι hL) :=
  inferInstance

/-- The reduced induced subscheme on a locally closed subset `L` has topological image exactly
`L`. -/
@[ega "I 5.2.1" "existence"]
public theorem range_locallyClosedSubschemeι {L : Set X} (hL : IsLocallyClosed L) :
    Set.range (locallyClosedSubschemeι hL).base = L := by
  have hfun : ⇑(locallyClosedSubschemeι hL) =
      (coborderOpens hL).ι.base ∘ (locallyClosedIdeal hL).subschemeι.base := rfl
  rw [show (locallyClosedSubschemeι hL).base = ⇑(locallyClosedSubschemeι hL) from rfl, hfun,
    Set.range_comp, IdealSheafData.range_subschemeι,
    IdealSheafData.coe_support_vanishingIdeal]
  show ⇑(coborderOpens hL).ι '' (⇑(coborderOpens hL).ι ⁻¹' L) = L
  rw [Set.image_preimage_eq_inter_range, (coborderOpens hL).range_ι]
  exact Set.inter_eq_left.mpr subset_coborder

/-- The reduced induced subscheme on a locally closed subset is below every cardinal bound the
ambient scheme is below: it is a closed subscheme of an open subscheme of `X`. -/
public theorem size_locallyClosedSubscheme_lt {L : Set X} (hL : IsLocallyClosed L)
    {κ : Cardinal.{u}} (h : X.size < κ) : (locallyClosedSubscheme hL).size < κ :=
  size_lt_of_isClosedImmersion (locallyClosedIdeal hL).subschemeι
    (size_lt_of_isOpenImmersion (coborderOpens hL).ι h)

end Scheme

/-! ### Locally closed subschemes as objects of a big étale site -/

namespace BigEtaleSite

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- A locally closed subset of an object of a big étale site, with its reduced induced subscheme
structure, as an object of that site. -/
public def locallyClosedObj {L : Set X.obj} (hL : IsLocallyClosed L) : B.Scheme :=
  ⟨Scheme.locallyClosedSubscheme hL, Scheme.size_locallyClosedSubscheme_lt hL X.property⟩

/-- The structure morphism of a locally closed subset of an object of a big étale site. -/
public def locallyClosedHom {L : Set X.obj} (hL : IsLocallyClosed L) :
    B.locallyClosedObj X hL ⟶ X :=
  B.inclusion.preimage (Scheme.locallyClosedSubschemeι hL)

/-- The structure morphism of `AlgebraicGeometry.BigEtaleSite.locallyClosedObj` is the immersion
of the reduced induced subscheme. -/
public theorem map_locallyClosedHom {L : Set X.obj} (hL : IsLocallyClosed L) :
    B.inclusion.map (B.locallyClosedHom X hL) = Scheme.locallyClosedSubschemeι hL :=
  B.inclusion.map_preimage _

/-- The structure morphism of `AlgebraicGeometry.BigEtaleSite.locallyClosedObj` is an
immersion. -/
public theorem isImmersion_map_locallyClosedHom {L : Set X.obj} (hL : IsLocallyClosed L) :
    IsImmersion (B.inclusion.map (B.locallyClosedHom X hL)) := by
  rw [B.map_locallyClosedHom X hL]
  exact Scheme.isImmersion_locallyClosedSubschemeι hL

/-- The structure morphism of `AlgebraicGeometry.BigEtaleSite.locallyClosedObj` has image exactly
the given locally closed subset. -/
public theorem range_locallyClosedHom {L : Set X.obj} (hL : IsLocallyClosed L) :
    Set.range (B.inclusion.map (B.locallyClosedHom X hL)).base = L := by
  rw [B.map_locallyClosedHom X hL]
  exact Scheme.range_locallyClosedSubschemeι hL

end BigEtaleSite

end AlgebraicGeometry

end
