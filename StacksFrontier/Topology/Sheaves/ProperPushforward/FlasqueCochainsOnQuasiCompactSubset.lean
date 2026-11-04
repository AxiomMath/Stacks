module

public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.Topology.Compact.RefineCover
public import StacksFrontier.Topology.Sheaves.ProperPushforward.SectionsOnQuasiCompactSubset

/-!
# Families of sections on a quasi-compact separated subset, and their refinements

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points
of which can be separated by disjoint opens *of `X`*, and let `F` be a sheaf on `X`.  Write
`F|_Z` for the germ model `GermPullback.sheaf` of the inverse image of `F` on `Z` with its
subspace topology, as in
`StacksFrontier.Topology.Sheaves.ProperPushforward.SectionsOnQuasiCompactSubset`.

This file proves two refinement statements about a family of sections indexed by the `(p+1)`-tuples
of an open cover of `Z`, that is, a Čech `p`-cochain for the induced cover of `Z`, from the
positive-degree part of [Stacks, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3).

Given an open cover `U : ι → Opens X` of `Z` and, for each `τ : Fin (p+1) → ι`, a section
`ξ τ` of `F|_Z` over the trace of `⨅ k, U (τ k)` on `Z`:

* `exists_refinement_sections_of_isFlasque`: if `F` is flasque, then after replacing the cover
  by a refinement, **each `ξ τ` is the family of germs of a single section of `F` over the
  corresponding open of `X`**.
* `exists_refinement_eq_of_germ_eq`: if two families of sections of `F` over the opens
  `⨅ k, U (τ k)` have the same germs at every point of `Z`, then after shrinking the cover they
  **agree on the nose**.

Alongside these, `exists_global_restrictToSubset_eq_of_isFlasque` records that for a flasque `F`
a section of `F|_Z` is the germ family of a *global* section of `F`, which is the softness of
`F|_Z` on the compact Hausdorff space `Z`.

Both are generalisations to families of the degree-zero statements of
`SectionsOnQuasiCompactSubset`: `exists_refinement_sections_of_isFlasque` for a one-element
index type and `p = 0` is the surjectivity assertion there (up to flasqueness, which replaces
the gluing), and `exists_refinement_eq_of_germ_eq` for a one-element index type is its
injectivity assertion.

## Main definitions

* `Stacks.Topology.SectionsOnQuasiCompactSubset.subspaceInclusionHom`: the inclusion of a
  subset with its subspace topology, as a bundled continuous map.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.traceOpen`: the trace `Z ∩ U` of an open `U` of
  `X` on `Z`, as an open subset of `Z`.

## Main results

* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_traceOpen_le_apply_eq_germ`: a section of
  `F|_Z` over *any* open of `Z` is, near each of its points, the family of germs of a section of
  `F` over an open of `X` whose trace on `Z` is contained in the given open (Stacks 09V3).
* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_refinement_eq_of_germ_eq`: the shrinking
  step above (Stacks 09V3, positive degrees).
* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_refinement_sections_of_isFlasque`: the
  representability step above (Stacks 09V3, positive degrees).
* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_global_restrictToSubset_eq_of_isFlasque`:
  for a flasque `F`, every section of `F|_Z` is the family of germs of a *global* section of
  `F`, so `F|_Z` is soft (Stacks 09V3 for a flasque sheaf).

## Implementation notes

`traceOpen` is `Opens.comap` along the subspace inclusion; the trace of a finite infimum is the
infimum of the traces only up to `Opens.coe_iInf`, so the families below are indexed by the
*infimum of the traces* `⨅ k, traceOpen Z (U (τ k))`, which is the spelling that matches the
`⋂ k, U (σ k)` of Stacks 0CY5 and Stacks 09UW on the nose.

Stacks 09UW is stated for a compact Hausdorff *space*; the subspace `Z` is one, the instances
being produced inside `exists_refinement_sections_of_isFlasque` from `IsCompact Z` and from the
separation hypothesis.  The cover it returns is indexed by a new type `J` together with a map
`α : J → ι`, which is why the conclusion re-indexes rather than shrinking `U` in place; the
shrinking lemma Stacks 0CY5 used by `exists_refinement_eq_of_germ_eq` keeps the index type, so
that statement does shrink in place.

The hypothesis `Nonempty (F.presheaf.obj (op ⊤))` of
`exists_refinement_sections_of_isFlasque` cannot be dropped for a sheaf of sets: a tuple `τ`
whose opens meet `Z` in the empty set imposes no condition on `s τ`, but `s τ` must still
exist.  It is automatic for a sheaf of abelian groups, which is the case Stacks 09V3 is about,
and for a flasque `F` it is equivalent to every `F(V)` being nonempty.

## References

* [Stacks, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks, Tag 09UW](https://stacks.math.columbia.edu/tag/09UW)
* [Stacks, Tag 09SX](https://stacks.math.columbia.edu/tag/09SX)
* [Stacks, Tag 0CY5](https://stacks.math.columbia.edu/tag/0CY5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat Opposite

universe u

noncomputable section

namespace Stacks.Topology.SectionsOnQuasiCompactSubset

variable {X : TopCat.{u}}

/-! ### The trace of an open on a subset -/

/-- The inclusion of a subset `Z ⊆ X` with its subspace topology, as a bundled continuous map. -/
def subspaceInclusionHom (Z : Set X) : C(↥(TopCat.of Z), ↥X) :=
  ⟨subspaceInclusion Z, continuous_subspaceInclusion Z⟩

/-- The trace `Z ∩ U` of an open subset `U` of `X` on a subset `Z`, as an open subset of `Z`
with its subspace topology. -/
def traceOpen (Z : Set X) (U : Opens X) : Opens (TopCat.of Z) :=
  Opens.comap (subspaceInclusionHom Z) U

/-- A point of `Z` lies in the trace of `U` exactly when it lies in `U`. -/
@[simp]
lemma mem_traceOpen {Z : Set X} {U : Opens X} {z : ↥(TopCat.of Z)} :
    z ∈ traceOpen Z U ↔ (z.1 : ↥X) ∈ U := Iff.rfl

/-- The underlying set of the trace of `U` on `Z` is the preimage of `U`. -/
lemma coe_traceOpen (Z : Set X) (U : Opens X) :
    ((traceOpen Z U : Opens (TopCat.of Z)) : Set ↥(TopCat.of Z))
      = Subtype.val ⁻¹' ((U : Opens X) : Set ↥X) := rfl

/-- Membership in a finite infimum of opens is membership in every member. -/
private lemma mem_iInf_opens {Y : TopCat.{u}} {ι : Type*} [Finite ι] (U : ι → Opens Y)
    (x : ↥Y) : x ∈ (⨅ i, U i) ↔ ∀ i, x ∈ U i := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact forall_congr' fun _ ↦ Iff.rfl

/-- On a flasque presheaf, every section over an open extends to a global section. -/
private lemma exists_map_top_eq_of_isFlasque (F : X.Presheaf (Type u)) [F.IsFlasque]
    {U : Opens X} (t : F.obj (op U)) : ∃ g : F.obj (op ⊤), F.map (homOfLE le_top).op g = t :=
  (CategoryTheory.epi_iff_surjective _).mp
    (TopCat.Presheaf.IsFlasque.epi (F := F) (homOfLE (le_top : U ≤ ⊤)).op) t

/-! ### Local representability over an arbitrary open of `Z` -/

/-- A section `σ` of `F|_Z` over an open `W` of `Z` is, near each point `z` of `W`, the family of
germs of a single section of `F`: there are an open `A ∋ z` of `X` whose trace on `Z` is contained
in `W` and a section `t` of `F` over `A` such that `σ` and the germs of `t` agree at every point of
`Z ∩ A`. -/
lemma exists_traceOpen_le_apply_eq_germ (F : X.Presheaf (Type u)) {Z : Set X}
    {W : Opens (TopCat.of Z)}
    (σ : (GermPullback.sheaf (subspaceInclusion Z) F).presheaf.obj (op W))
    {z : ↥(TopCat.of Z)} (hz : z ∈ W) :
    ∃ (A : Opens X) (_ : (z.1 : ↥X) ∈ A) (_ : traceOpen Z A ≤ W) (t : F.obj (op A)),
      ∀ (w : ↥(TopCat.of Z)) (hwW : w ∈ W) (hwA : (w.1 : ↥X) ∈ A),
        σ.1 ⟨w, hwW⟩ = ⟨(w.1 : ↥X), F.germ A (w.1 : ↥X) hwA t⟩ := by
  obtain ⟨W₀, hzW₀, i, V, hV, t, ht⟩ := GermPullback.exists_repr σ hz
  obtain ⟨A₀, hA₀open, hA₀W₀⟩ := isOpen_induced_iff.mp W₀.isOpen
  have hmemW₀ : ∀ (w : ↥(TopCat.of Z)), (w.1 : ↥X) ∈ A₀ ↔ w ∈ W₀ := Set.ext_iff.1 hA₀W₀
  refine ⟨(⟨A₀, hA₀open⟩ : Opens X) ⊓ V, ⟨(hmemW₀ z).2 hzW₀, hV ⟨z, hzW₀⟩⟩, ?_,
    F.map (homOfLE (inf_le_right : (⟨A₀, hA₀open⟩ ⊓ V : Opens X) ≤ V)).op t, ?_⟩
  · intro w hw
    exact i.le ((hmemW₀ w).1 hw.1)
  · intro w hwW hwA
    rw [F.germ_res_apply (homOfLE (inf_le_right : (⟨A₀, hA₀open⟩ ⊓ V : Opens X) ≤ V))
      (w.1 : ↥X) hwA t]
    exact ht ⟨w, (hmemW₀ w).1 hwA.1⟩

/-! ### Shrinking a cover so that germwise equal families become equal -/

/-- Let `F` be a sheaf on `X`, let `Z` be a quasi-compact subset of `X` whose distinct points are
separated by disjoint opens of `X`, and let `U : ι → Opens X` be an open cover of `Z`.  Suppose
given, for every `(p+1)`-tuple `τ` of indices, two sections `a τ` and `b τ` of `F` over
`⨅ k, U (τ k)` whose germs agree at every point of `Z`.  Then the cover can be shrunk to an open
cover `V : ι → Opens X` of `Z` with `V i ≤ U i` on which the two families agree on the nose. -/
theorem exists_refinement_eq_of_germ_eq (F : X.Sheaf (Type u)) {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set ↥X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    {ι : Type*} (p : ℕ) (U : ι → Opens X) (hcov : Z ⊆ ⋃ i, ((U i : Opens X) : Set ↥X))
    (a b : ∀ τ : Fin (p + 1) → ι, F.presheaf.obj (op (⨅ k, U (τ k))))
    (hab : ∀ (τ : Fin (p + 1) → ι) (x : ↥X), x ∈ Z → ∀ hx : x ∈ ⨅ k, U (τ k),
      F.presheaf.germ (⨅ k, U (τ k)) x hx (a τ)
        = F.presheaf.germ (⨅ k, U (τ k)) x hx (b τ)) :
    ∃ V : ι → Opens X, (∀ i, V i ≤ U i) ∧ Z ⊆ ⋃ i, ((V i : Opens X) : Set ↥X) ∧
      ∀ (τ : Fin (p + 1) → ι) (hle : (⨅ k, V (τ k)) ≤ ⨅ k, U (τ k)),
        F.presheaf.map (homOfLE hle).op (a τ) = F.presheaf.map (homOfLE hle).op (b τ) := by
  classical
  set W : (Fin (p + 1) → ι) → Set ↥X :=
    fun τ ↦ ((germEqOpens F.presheaf (a τ) (b τ) : Opens X) : Set ↥X) with hWdef
  have hWopen : ∀ τ, IsOpen (W τ) := fun τ ↦ (germEqOpens F.presheaf _ _).isOpen
  have hWinter : ∀ τ, W τ ∩ Z = (⋂ k, ((U (τ k) : Opens X) : Set ↥X)) ∩ Z := by
    intro τ
    refine Set.ext fun x ↦ ⟨fun hx ↦ ⟨?_, hx.2⟩, fun hx ↦ ⟨?_, hx.2⟩⟩
    · obtain ⟨h0, -, -⟩ := mem_germEqOpens.1 hx.1
      exact Set.mem_iInter.2 fun k ↦ (mem_iInf_opens (fun k ↦ U (τ k)) x).1 h0 k
    · have h0 : x ∈ (⨅ k, U (τ k)) :=
        (mem_iInf_opens (fun k ↦ U (τ k)) x).2 fun k ↦ Set.mem_iInter.1 hx.1 k
      exact mem_germEqOpens.2 ⟨h0, h0, hab τ x hx.2 h0⟩
  obtain ⟨V, hVopen, hVcover, hVsub, -, hVinter⟩ :=
    TopologicalSpace.exists_isOpen_refinement_of_isCompact_of_pairwiseSeparated Z hZ hSep p ι
      (fun i ↦ ((U i : Opens X) : Set ↥X)) (fun i ↦ (U i).isOpen) W hWopen hcov hWinter
  refine ⟨fun i ↦ ⟨V i, hVopen i⟩, fun i ↦ hVsub i, hVcover, ?_⟩
  intro τ hle
  refine TopCat.Presheaf.section_ext F _ _ _ fun x hx ↦ ?_
  have hxInter : x ∈ ⋂ k, V (τ k) :=
    Set.mem_iInter.2 fun k ↦
      (mem_iInf_opens (fun k ↦ (⟨V (τ k), hVopen (τ k)⟩ : Opens X)) x).1 hx k
  obtain ⟨h0, h1, he⟩ := mem_germEqOpens.1 (hVinter τ hxInter)
  rw [F.presheaf.germ_res_apply (homOfLE hle) x hx (a τ),
    F.presheaf.germ_res_apply (homOfLE hle) x hx (b τ)]
  exact he

/-! ### Refining a cover so that a family of sections on `Z` is represented on `X` -/

/-- Let `F` be a flasque sheaf on `X`, let `Z` be a quasi-compact subset of `X` whose distinct
points are separated by disjoint opens of `X`, and let `U : ι → Opens X` be an open cover of `Z`.
Suppose given, for every `(p+1)`-tuple `τ` of indices, a section `ξ τ` of `F|_Z` over the trace on
`Z` of `⨅ k, U (τ k)`.  Then there is a refinement of the cover — an open cover `V : J → Opens X`
of `Z` together with `α : J → ι` and `V j ≤ U (α j)` — and, for every `(p+1)`-tuple `τ` of indices
of the refinement, a section `s τ` of `F` over `⨅ k, V (τ k)` whose germs along `Z` are the values
of `ξ (α ∘ τ)`. -/
theorem exists_refinement_sections_of_isFlasque (F : X.Sheaf (Type u))
    [F.presheaf.IsFlasque] (hne : Nonempty (F.presheaf.obj (op (⊤ : Opens X))))
    {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set ↥X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    {ι : Type*} (p : ℕ) (U : ι → Opens X) (hcov : Z ⊆ ⋃ i, ((U i : Opens X) : Set ↥X))
    (ξ : ∀ τ : Fin (p + 1) → ι,
      (GermPullback.sheaf (subspaceInclusion Z) F.presheaf).presheaf.obj
        (op (⨅ k, traceOpen Z (U (τ k))))) :
    ∃ (J : Type) (V : J → Opens X) (α : J → ι),
      (∀ j, V j ≤ U (α j)) ∧ Z ⊆ ⋃ j, ((V j : Opens X) : Set ↥X) ∧
      ∃ s : ∀ τ : Fin (p + 1) → J, F.presheaf.obj (op (⨅ k, V (τ k))),
        ∀ (τ : Fin (p + 1) → J) (x : ↥X) (hxZ : x ∈ Z) (hxV : x ∈ ⨅ k, V (τ k))
          (hmem : (⟨x, hxZ⟩ : ↥(TopCat.of Z)) ∈ ⨅ k, traceOpen Z (U (α (τ k)))),
          (ξ fun k ↦ α (τ k)).1 ⟨⟨x, hxZ⟩, hmem⟩
            = ⟨x, F.presheaf.germ (⨅ k, V (τ k)) x hxV (s τ)⟩ := by
  classical
  have hcs : CompactSpace ↥(TopCat.of Z) := isCompact_iff_compactSpace.mp hZ
  have ht2 : T2Space ↥(TopCat.of Z) := by
    refine ⟨fun z w hzw ↦ ?_⟩
    obtain ⟨A, B, hA, hB, hzA, hwB, hAB⟩ :=
      hSep z.1 z.2 w.1 w.2 fun h ↦ hzw (Subtype.ext h)
    refine ⟨Subtype.val ⁻¹' A, Subtype.val ⁻¹' B, hA.preimage continuous_subtype_val,
      hB.preimage continuous_subtype_val, hzA, hwB, ?_⟩
    rw [Set.disjoint_left]
    intro y hyA hyB
    exact (Set.disjoint_left.1 hAB) hyA hyB
  set Wi : ι → Set ↥(TopCat.of Z) := fun i ↦ Subtype.val ⁻¹' ((U i : Opens X) : Set ↥X) with hWidef
  have hWiopen : ∀ i, IsOpen (Wi i) := fun i ↦ (U i).isOpen.preimage continuous_subtype_val
  have hWicov : ⋃ i, Wi i = Set.univ := by
    refine Set.eq_univ_of_forall fun z ↦ ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov z.2)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  choose Arep hArepMem hArepLe trep htrep using fun (τ : Fin (p + 1) → ι)
    (k : ↥(⨅ a, traceOpen Z (U (τ a)))) ↦
      exists_traceOpen_le_apply_eq_germ F.presheaf (ξ τ) k.2
  have hWcov : ∀ τ : Fin (p + 1) → ι,
      (⋂ a, Wi (τ a))
        = ⋃ k : ↥(⨅ a, traceOpen Z (U (τ a))),
            ((traceOpen Z (Arep τ k) : Opens (TopCat.of Z)) : Set ↥(TopCat.of Z)) := by
    intro τ
    refine Set.ext fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · have hz' : z ∈ (⨅ a, traceOpen Z (U (τ a))) :=
        (mem_iInf_opens _ z).2 fun a ↦ Set.mem_iInter.1 hz a
      exact Set.mem_iUnion.2 ⟨⟨z, hz'⟩, hArepMem τ ⟨z, hz'⟩⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
      have hz' : z ∈ (⨅ a, traceOpen Z (U (τ a))) := hArepLe τ k hk
      exact Set.mem_iInter.2 fun a ↦ (mem_iInf_opens _ z).1 hz' a
  obtain ⟨J, V', α, hV'open, hV'cov, hV'clos, hV'int⟩ :=
    exists_cover_closure_subset_and_refines Wi hWiopen hWicov p
      (fun τ k ↦ ((traceOpen Z (Arep τ k) : Opens (TopCat.of Z)) : Set ↥(TopCat.of Z)))
      (fun τ k ↦ (traceOpen Z (Arep τ k)).isOpen) hWcov
  choose B hBopen hBtrace using fun j ↦ isOpen_induced_iff.mp (hV'open j)
  set Vo : J → Opens X := fun j ↦ (⟨B j, hBopen j⟩ : Opens X) ⊓ U (α j) with hVodef
  have hVoU : ∀ j, Vo j ≤ U (α j) := fun j ↦ inf_le_right
  have hmemVo : ∀ (j : J) (z : ↥(TopCat.of Z)), (z.1 : ↥X) ∈ Vo j ↔ z ∈ V' j := by
    intro j z
    exact ⟨fun hz ↦ (Set.ext_iff.1 (hBtrace j) z).1 hz.1,
      fun hz ↦ ⟨(Set.ext_iff.1 (hBtrace j) z).2 hz, hV'clos j (subset_closure hz)⟩⟩
  have hZcov : Z ⊆ ⋃ j, ((Vo j : Opens X) : Set ↥X) := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hV'cov ▸ Set.mem_univ (⟨x, hx⟩ : ↥(TopCat.of Z)))
    exact Set.mem_iUnion.2 ⟨j, (hmemVo j ⟨x, hx⟩).2 hj⟩
  have hiInterVo : ∀ (τ : Fin (p + 1) → J) (x : ↥X) (hxZ : x ∈ Z),
      x ∈ (⨅ k, Vo (τ k)) → (⟨x, hxZ⟩ : ↥(TopCat.of Z)) ∈ ⋂ a, V' (τ a) := by
    intro τ x hxZ hxV
    exact Set.mem_iInter.2 fun a ↦
      (hmemVo (τ a) ⟨x, hxZ⟩).1 ((mem_iInf_opens (fun k ↦ Vo (τ k)) x).1 hxV a)
  have key : ∀ τ : Fin (p + 1) → J, ∃ t : F.presheaf.obj (op (⨅ k, Vo (τ k))),
      ∀ (x : ↥X) (hxZ : x ∈ Z) (hxV : x ∈ ⨅ k, Vo (τ k))
        (hmem : (⟨x, hxZ⟩ : ↥(TopCat.of Z)) ∈ ⨅ k, traceOpen Z (U (α (τ k)))),
        (ξ fun k ↦ α (τ k)).1 ⟨⟨x, hxZ⟩, hmem⟩
          = ⟨x, F.presheaf.germ (⨅ k, Vo (τ k)) x hxV t⟩ := by
    intro τ
    rcases hV'int τ with hempty | ⟨k, hsub⟩
    · refine ⟨F.presheaf.map (homOfLE (le_top : (⨅ k, Vo (τ k)) ≤ ⊤)).op hne.some,
        fun x hxZ hxV hmem ↦ ?_⟩
      exact absurd (hempty ▸ hiInterVo τ x hxZ hxV) (Set.notMem_empty _)
    · obtain ⟨g, hg⟩ := exists_map_top_eq_of_isFlasque F.presheaf (trep (fun a ↦ α (τ a)) k)
      refine ⟨F.presheaf.map (homOfLE (le_top : (⨅ k, Vo (τ k)) ≤ ⊤)).op g,
        fun x hxZ hxV hmem ↦ ?_⟩
      have hxA : (x : ↥X) ∈ Arep (fun a ↦ α (τ a)) k :=
        hsub (hiInterVo τ x hxZ hxV)
      rw [htrep (fun a ↦ α (τ a)) k ⟨x, hxZ⟩ hmem hxA, ← hg,
        F.presheaf.germ_res_apply (homOfLE (le_top : Arep (fun a ↦ α (τ a)) k ≤ ⊤)) x hxA g,
        F.presheaf.germ_res_apply (homOfLE (le_top : (⨅ k, Vo (τ k)) ≤ ⊤)) x hxV g]
  choose s hs using key
  exact ⟨J, Vo, α, hVoU, hZcov, s, hs⟩

/-! ### Sections on `Z` of a flasque sheaf come from global sections -/

/-- Let `F` be a flasque sheaf on `X` and let `Z` be a quasi-compact subset of `X` whose distinct
points are separated by disjoint opens of `X`.  Then every section of `F|_Z` is the family of germs
along `Z` of a *global* section of `F`. -/
theorem exists_global_restrictToSubset_eq_of_isFlasque (F : X.Sheaf (Type u))
    [F.presheaf.IsFlasque] {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set ↥X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (σ : sectionsOn F.presheaf Z) :
    ∃ s : F.presheaf.obj (op (⊤ : Opens X)),
      ∀ hZtop : Z ⊆ ((⊤ : Opens X) : Set ↥X),
        restrictToSubset F.presheaf hZtop s = σ := by
  obtain ⟨U, hZU, t, ht⟩ := exists_isOpen_restrictToSubset_eq F hZ hSep σ
  obtain ⟨s, hs⟩ := exists_map_top_eq_of_isFlasque F.presheaf t
  refine ⟨s, fun hZtop ↦ ?_⟩
  rw [← ht]
  refine GermPullback.ext fun w ↦ ?_
  rw [restrictToSubset_val, restrictToSubset_val, ← hs,
    F.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) w.1.1 _ s]

end Stacks.Topology.SectionsOnQuasiCompactSubset

end
