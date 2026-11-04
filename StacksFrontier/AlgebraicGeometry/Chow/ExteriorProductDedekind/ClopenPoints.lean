module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.BaseGeometry

/-!
# The zero-dimensional components of a Dedekind base

Let `(S, δ)` be as in Stacks section 42.63. The scheme `S` is normal, hence a disjoint union of
integral schemes (Algebra, Lemma 034X; Properties, Lemma 033N), and Mathlib's Dedekind domains
include fields, so some of these integral pieces may be spectra of fields. Such a piece is a single
point which is both open and closed in `S`, and `δ` vanishes there; the other pieces are curves.

This file isolates the union `S₀` of the zero-dimensional pieces as an open and closed subscheme.

## Main definitions

* `Stacks.Chow.clopenPoints` — the open subscheme `S₀` of the points `s` with `{s}` open and
  closed.

## Main results

* `Stacks.Chow.IsDedekindChowBase.isClosed_clopenPoints` — `S₀` is closed.
* `Stacks.Chow.IsDedekindChowBase.mem_clopenPoints_of_isClosed` — a closed point which is the
  generic point of an irreducible component lies in `S₀`.
* `Stacks.Chow.IsDedekindChowBase.dimensionFunction_eq_one_of_not_mem_clopenPoints` — the
  generic point of an irreducible component outside `S₀` has `δ = 1`.
* `Stacks.Chow.IsDedekindChowBase.isField_stalk_of_mem_clopenPoints` — the local rings of `S`
  at the points of `S₀` are fields.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}}

/-- The open subscheme `S₀` of a base situation consisting of the points `s` for which `{s}` is
both open and closed. Over a Dedekind base these are the zero-dimensional irreducible
components. -/
def clopenPoints (C : ChowSituation.{u}) : C.S.Opens where
  carrier := {s | IsOpen ({s} : Set C.S) ∧ IsClosed ({s} : Set C.S)}
  is_open' := isOpen_iff_forall_mem_open.mpr fun s hs ↦
    ⟨{s}, Set.singleton_subset_iff.mpr hs, hs.1, rfl⟩

/-- A point `s` lies in `S₀` if and only if `{s}` is open and closed. -/
theorem mem_clopenPoints_iff {s : C.S} :
    s ∈ clopenPoints C ↔ IsOpen ({s} : Set C.S) ∧ IsClosed ({s} : Set C.S) :=
  Iff.rfl

/-- A preirreducible set containing a point `s` with `{s}` clopen contains no other point. -/
private theorem eq_of_isPreirreducible_of_isClopen_singleton {X : Type*} [TopologicalSpace X]
    {Z : Set X} {s t : X} (hZ : IsPreirreducible Z) (hs : IsOpen ({s} : Set X))
    (hcl : IsClosed ({s} : Set X)) (hsZ : s ∈ Z) (htZ : t ∈ Z) : t = s := by
  by_contra hts
  obtain ⟨w, -, hw1, hw2⟩ := hZ {s} ({s}ᶜ) hs hcl.isOpen_compl ⟨s, hsZ, rfl⟩ ⟨t, htZ, hts⟩
  exact hw2 hw1

/-- A point of `S₀` is the generic point of an irreducible component. -/
theorem closure_mem_irreducibleComponents_of_mem_clopenPoints {s : C.S}
    (hs : s ∈ clopenPoints C) : closure ({s} : Set C.S) ∈ irreducibleComponents C.S := by
  rw [hs.2.closure_eq]
  refine ⟨isIrreducible_singleton, fun Z hZ hsub t ht ↦ ?_⟩
  exact eq_of_isPreirreducible_of_isClopen_singleton hZ.2 hs.1 hs.2 (hsub rfl) ht

/-- The points of `S₀` specialize only to themselves. -/
theorem eq_of_specializes_of_mem_clopenPoints {s t : C.S} (hs : s ∈ clopenPoints C)
    (h : s ⤳ t) : t = s := by
  rwa [specializes_iff_mem_closure, hs.2.closure_eq] at h

/-- A point generalizing to a point of `S₀` lies in `S₀`. -/
theorem mem_clopenPoints_of_specializes {s t : C.S} (h : s ⤳ t) (ht : t ∈ clopenPoints C) :
    s ∈ clopenPoints C := by
  rwa [Set.mem_singleton_iff.mp (h.mem_open ht.1 rfl)]

variable (hC : IsDedekindChowBase C)
include hC

/-- Every point of a Dedekind base has an irreducible open neighbourhood. -/
theorem IsDedekindChowBase.exists_isIrreducible_nhds (s : C.S) :
    ∃ U : C.S.Opens, s ∈ U ∧ IsIrreducible (U : Set C.S) := by
  obtain ⟨U, hsU, hU, hD⟩ := hC.1 s
  refine ⟨U, hsU, ?_⟩
  have : Nonempty U.toScheme := ⟨⟨s, hsU⟩⟩
  have : IsDomain Γ(C.S, U) := hD.toIsDomain
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion hU.isoSpec.hom
  have h := (IrreducibleSpace.isIrreducible_univ U.toScheme).image U.ι.base
    U.ι.base.hom.continuous.continuousOn
  rwa [Set.image_univ, Scheme.Opens.range_ι] at h

/-- Over a Dedekind base, `S₀` is closed. -/
theorem IsDedekindChowBase.isClosed_clopenPoints :
    IsClosed (clopenPoints C : Set C.S) := by
  refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun t ht ↦ ?_)
  obtain ⟨U, htU, hU⟩ := hC.exists_isIrreducible_nhds t
  refine ⟨U, fun s hsU hs ↦ ht ?_, U.isOpen, htU⟩
  exact eq_of_isPreirreducible_of_isClopen_singleton hU.2 hs.1 hs.2 hsU htU ▸ hs

/-- A closed point of a Dedekind base which is the generic point of an irreducible component lies
in `S₀`. -/
theorem IsDedekindChowBase.mem_clopenPoints_of_isClosed {s : C.S}
    (hcl : IsClosed ({s} : Set C.S)) (hη : closure ({s} : Set C.S) ∈ irreducibleComponents C.S) :
    s ∈ clopenPoints C := by
  refine ⟨?_, hcl⟩
  obtain ⟨U, hsU, hU⟩ := hC.exists_isIrreducible_nhds s
  rw [hcl.closure_eq] at hη
  have heq := hη.2 hU.closure (Set.singleton_subset_iff.mpr (subset_closure hsU))
  have hUs : (U : Set C.S) = {s} :=
    Set.Subset.antisymm (subset_closure.trans heq) (Set.singleton_subset_iff.mpr hsU)
  exact hUs ▸ U.isOpen

/-- Over a Dedekind base, `δ = 1` at the generic points of the irreducible components outside
`S₀`. -/
theorem IsDedekindChowBase.dimensionFunction_eq_one_of_not_mem_clopenPoints {s : C.S}
    (hη : closure ({s} : Set C.S) ∈ irreducibleComponents C.S) (hs : s ∉ clopenPoints C) :
    C.dimensionFunction s = 1 :=
  hC.2.2 s fun hcl ↦ hs (hC.mem_clopenPoints_of_isClosed hcl hη)

/-- Over a Dedekind base, `δ = 0` on `S₀`. -/
theorem IsDedekindChowBase.dimensionFunction_eq_zero_of_mem_clopenPoints {s : C.S}
    (hs : s ∈ clopenPoints C) : C.dimensionFunction s = 0 :=
  hC.2.1 s hs.2

/-- Over a Dedekind base, the local rings at the points of `S₀` are fields. -/
theorem IsDedekindChowBase.isField_stalk_of_mem_clopenPoints {s : C.S}
    (hs : s ∈ clopenPoints C) : IsField (C.S.presheaf.stalk s) :=
  hC.isField_stalk_of_mem (closure_mem_irreducibleComponents_of_mem_clopenPoints hs)

end Stacks.Chow

end
