module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Compact.ShrinkingCover
public import StacksFrontier.Topology.Sheaves.Limits.GermPullback

/-!
# Sections of a sheaf of sets on a quasi-compact separated subset

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points
of which can be separated by disjoint opens *of `X`*, and let `F` be a sheaf of sets on `X`.
Write `F|_Z` for the inverse image of `F` on `Z` with its subspace topology, realised as the
sheaf of germs `GermPullback.sheaf`.  The canonical map

`colim_{Z ⊆ U open} F(U) ⟶ Γ(Z, F|_Z)`

is then bijective.  This is the degree-zero case of
[Stacks, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3).

Rather than as an isomorphism of colimits, the statement is recorded here as the two
elementary assertions it unwinds to: the map is injective, in the form that two sections
agreeing on `Z` already agree on an open neighbourhood of `Z`
(`exists_isOpen_eq_of_restrictToSubset_eq`, which needs neither quasi-compactness nor
separation), and it is surjective, in the form that every section on `Z` extends to an open
neighbourhood of `Z` (`exists_isOpen_restrictToSubset_eq`).

Applied to the fibre `Z = f⁻¹(y)` of a closed continuous map `f : X → Y`, the same two
assertions say that the canonical map `(f_*F)_y ⟶ Γ(f⁻¹(y), F|_{f⁻¹(y)})` is bijective, which
is the degree-zero case of
[Stacks, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5); they are
`exists_isOpen_mem_restrictToSubset_eq_of_isClosedMap` and
`exists_isOpen_mem_map_eq_of_restrictToSubset_eq_of_isClosedMap`.  Together they are the
topological input to proper base change in topology,
[Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90).

## Main definitions

* `Stacks.Topology.SectionsOnQuasiCompactSubset.subspaceInclusion`: the inclusion of a subset
  with its subspace topology, as a map of the underlying types of the corresponding objects of
  `TopCat`.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.sectionsOn`: the type `Γ(Z, F|_Z)` of sections
  of the inverse image of `F` on a subset `Z`.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.restrictToSubset`: the canonical map
  `F(U) → Γ(Z, F|_Z)` attached to an open `U ⊇ Z`, sending a section to its family of germs.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.germEqOpens`: the open locus where two sections
  of a presheaf of sets have the same germ.

## Main results

* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_isOpen_eq_of_restrictToSubset_eq`:
  injectivity in Stacks 09V3, degree zero — sections on two opens containing `Z` whose germ
  families on `Z` agree already agree on an open neighbourhood of `Z`.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_isOpen_restrictToSubset_eq`:
  surjectivity in Stacks 09V3, degree zero — every section of `F|_Z` is the family of germs of
  a section of `F` on an open neighbourhood of `Z`.
* `exists_isOpen_mem_restrictToSubset_eq_of_isClosedMap` and
  `exists_isOpen_mem_map_eq_of_restrictToSubset_eq_of_isClosedMap`, in the same namespace:
  the two assertions for the fibre of a closed map, which are Stacks 09V5 in degree zero.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_isOpen_preimage_subset_of_isClosedMap`:
  the elementary fact making the previous two work — an open neighbourhood of a fibre `f⁻¹(y)`
  of a closed map contains the preimage of an open neighbourhood of `y`.

## Implementation notes

The inverse image `F|_Z` is the germ model `GermPullback.sheaf` of the pullback, so a section
of `F|_Z` over an open `W ⊆ Z` *is* a function `W → Germs F` which is locally the germs of a
single section of `F`.  This makes `restrictToSubset` a one-liner and makes the germ-agreement
locus of two sections visibly open (`isOpen_setOf_germ_eq`), which is exactly the input the
shrinking lemma Stacks 0CY5 wants.

Surjectivity is the only place quasi-compactness and separation of `Z` enter.  The proof is the
one in the source: cover `Z` by opens `U z` of `X` carrying sections `s z` of `F` whose germs
realise the given section of `F|_Z` on `Z ∩ U z`; take `W` to be the locus where two of the
`s z` have equal germs, which is open and agrees with `U z ∩ U z'` along `Z`; shrink the cover
by Stacks 0CY5 with `p = 1` so that `V z ∩ V z' ⊆ W`; then the `s z` restricted to the `V z`
agree on overlaps — germwise equality upgrades to equality of sections because `F` is a sheaf
— and glue.

Because the fibre `Germs F` of the germ model is a sigma type over the points of `X` and the
stalks of `F`, the value universe of `F` is forced to be the universe of `X`.  The target `Y`
of the closed map in Stacks 09V5 is unconstrained, and is an arbitrary topological space rather
than an object of `TopCat`: nothing in those statements uses a sheaf on `Y`.

## References

* [Stacks, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
* [Stacks, Tag 0CY5](https://stacks.math.columbia.edu/tag/0CY5)
* [Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat Opposite

universe v u

noncomputable section

namespace Stacks.Topology.SectionsOnQuasiCompactSubset

variable {X : TopCat.{u}}

/-! ### Sections on a subset -/

/-- The inclusion of a subset `Z ⊆ X` carrying the subspace topology, as a map of the
underlying types of the corresponding objects of `TopCat`.  This is the map along which the
inverse image `F|_Z` appearing in Stacks 09V3 is taken. -/
def subspaceInclusion (Z : Set X) : ↥(TopCat.of Z) → ↥X := Subtype.val

/-- The inclusion of a subset with its subspace topology is continuous (Stacks 09V3). -/
lemma continuous_subspaceInclusion (Z : Set X) : Continuous (subspaceInclusion Z) :=
  continuous_subtype_val

/-- The type `Γ(Z, F|_Z)` of sections on a subset `Z ⊆ X` of a presheaf of sets `F` on `X`:
the global sections of the inverse image of `F` on `Z` with its subspace topology, realised as
the sheaf of germs of `F`.  This is the target of the comparison map of Stacks 09V3. -/
abbrev sectionsOn (F : X.Presheaf (Type u)) (Z : Set X) : Type u :=
  (GermPullback.sheaf (subspaceInclusion Z) F).presheaf.obj (op (⊤ : Opens (TopCat.of Z)))

/-- The canonical map `F(U) → Γ(Z, F|_Z)` attached to an open `U` containing `Z`: a section of
`F` on `U` goes to its family of germs along `Z`.  The comparison map of Stacks 09V3 is the map
induced by these on the colimit over all opens `U ⊇ Z`. -/
def restrictToSubset (F : X.Presheaf (Type u)) {Z : Set X} {U : Opens X}
    (hZU : Z ⊆ (U : Set X)) (s : F.obj (op U)) : sectionsOn F Z :=
  GermPullback.ofSection (fun z ↦ hZU z.1.2) s

/-- The value of `restrictToSubset F hZU s` at a point of `Z` is the germ of `s` there
(Stacks 09V3). -/
@[simp]
lemma restrictToSubset_val (F : X.Presheaf (Type u)) {Z : Set X} {U : Opens X}
    (hZU : Z ⊆ (U : Set X)) (s : F.obj (op U)) (w : ↥(⊤ : Opens (TopCat.of Z))) :
    (restrictToSubset F hZU s).1 w = ⟨w.1.1, F.germ U w.1.1 (hZU w.1.2) s⟩ := rfl

/-- Two germs of a presheaf at one point are equal as soon as they are equal in the total space
of germs. -/
private lemma germ_eq_of_germs_eq {F : X.Presheaf (Type u)} {x : X} {ξ ζ : F.stalk x}
    (h : (⟨x, ξ⟩ : GermPullback.Germs F) = ⟨x, ζ⟩) : ξ = ζ :=
  eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h).2

/-- Sections of `F` on two opens whose germ families along `Z` agree have equal germs at every
point of `Z` (Stacks 09V3). -/
lemma germ_eq_of_restrictToSubset_eq {F : X.Presheaf (Type u)} {Z : Set X} {U U' : Opens X}
    {hZU : Z ⊆ (U : Set X)} {hZU' : Z ⊆ (U' : Set X)} {s : F.obj (op U)} {s' : F.obj (op U')}
    (h : restrictToSubset F hZU s = restrictToSubset F hZU' s') {x : X} (hx : x ∈ Z) :
    F.germ U x (hZU hx) s = F.germ U' x (hZU' hx) s' :=
  germ_eq_of_germs_eq (congrArg (fun σ ↦ σ.1 ⟨⟨x, hx⟩, trivial⟩) h)

/-! ### The germ-agreement locus -/

/-- The locus where two sections of a presheaf of sets, each given on an open subset, have the
same germ is open.  This is the openness that lets the shrinking lemma Stacks 0CY5 be applied
in the proof of Stacks 09V3. -/
lemma isOpen_setOf_germ_eq (F : X.Presheaf (Type u)) (U U' : Opens X) (s : F.obj (op U))
    (s' : F.obj (op U')) :
    IsOpen {x : X | ∃ (hx : x ∈ U) (hx' : x ∈ U'), F.germ U x hx s = F.germ U' x hx' s'} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hxU, hxU', he⟩
  obtain ⟨W, hxW, iU, iU', hW⟩ := F.germ_eq x hxU hxU' s s' he
  refine ⟨W, fun y hy ↦ ⟨iU.le hy, iU'.le hy, ?_⟩, W.isOpen, hxW⟩
  rw [← F.germ_res_apply iU y hy s, ← F.germ_res_apply iU' y hy s', hW]

/-- The locus where two sections of a presheaf of sets, each given on an open subset, have the
same germ, as an open subset of `X` (Stacks 09V3). -/
def germEqOpens (F : X.Presheaf (Type u)) {U U' : Opens X} (s : F.obj (op U))
    (s' : F.obj (op U')) : Opens X :=
  ⟨_, isOpen_setOf_germ_eq F U U' s s'⟩

/-- A point lies in `germEqOpens F s s'` exactly when it lies in both opens and the two germs
there agree (Stacks 09V3). -/
lemma mem_germEqOpens {F : X.Presheaf (Type u)} {U U' : Opens X} {s : F.obj (op U)}
    {s' : F.obj (op U')} {x : X} :
    x ∈ germEqOpens F s s' ↔
      ∃ (hx : x ∈ U) (hx' : x ∈ U'), F.germ U x hx s = F.germ U' x hx' s' := Iff.rfl

/-- Restrictions of two sections of a sheaf to a common open are equal as soon as the two
sections have the same germ at every point of it. -/
private lemma map_eq_of_germ_eq (F : X.Sheaf (Type u)) {A U U' : Opens X} (i : A ⟶ U)
    (i' : A ⟶ U') (s : F.presheaf.obj (op U)) (s' : F.presheaf.obj (op U'))
    (h : ∀ (x : X) (hx : x ∈ A),
      F.presheaf.germ U x (i.le hx) s = F.presheaf.germ U' x (i'.le hx) s') :
    F.presheaf.map i.op s = F.presheaf.map i'.op s' := by
  refine TopCat.Presheaf.section_ext F _ _ _ fun x hx ↦ ?_
  rw [F.presheaf.germ_res_apply i x hx s, F.presheaf.germ_res_apply i' x hx s']
  exact h x hx

/-! ### Injectivity: sections agreeing on `Z` agree near `Z` -/

/-- **Stacks 09V3 in degree zero, injectivity.** Let `F` be a sheaf of sets on `X` and let `Z`
be a subset of `X`.  If sections of `F` on two opens `U, U' ⊇ Z` have the same family of germs
along `Z`, then they already agree on an open neighbourhood `V` of `Z` contained in both.

Neither quasi-compactness nor any separation of `Z` is needed. -/
theorem exists_isOpen_eq_of_restrictToSubset_eq (F : X.Sheaf (Type u)) {Z : Set X}
    {U U' : Opens X} (hZU : Z ⊆ (U : Set X)) (hZU' : Z ⊆ (U' : Set X))
    (s : F.presheaf.obj (op U)) (s' : F.presheaf.obj (op U'))
    (h : restrictToSubset F.presheaf hZU s = restrictToSubset F.presheaf hZU' s') :
    ∃ (V : Opens X) (_ : Z ⊆ (V : Set X)) (hVU : V ≤ U) (hVU' : V ≤ U'),
      F.presheaf.map (homOfLE hVU).op s = F.presheaf.map (homOfLE hVU').op s' := by
  have hleU : germEqOpens F.presheaf s s' ≤ U := fun _ hx ↦ (mem_germEqOpens.1 hx).1
  have hleU' : germEqOpens F.presheaf s s' ≤ U' := fun _ hx ↦ (mem_germEqOpens.1 hx).2.1
  refine ⟨germEqOpens F.presheaf s s',
    fun x hx ↦ ⟨hZU hx, hZU' hx, germ_eq_of_restrictToSubset_eq h hx⟩, hleU, hleU', ?_⟩
  exact map_eq_of_germ_eq F _ _ s s' fun x hx ↦ (mem_germEqOpens.1 hx).2.2

/-! ### Local representability of a section on `Z` -/

/-- A section of `F|_Z` is, near each point of `Z`, the family of germs of a section of `F` on
an open subset of `X` (Stacks 09V3). -/
lemma exists_isOpen_apply_eq_germ (F : X.Presheaf (Type u)) {Z : Set X} (σ : sectionsOn F Z)
    {z : X} (hz : z ∈ Z) :
    ∃ (U : Opens X) (_ : z ∈ U) (s : F.obj (op U)),
      ∀ (x : X) (hxZ : x ∈ Z) (hxU : x ∈ U),
        σ.1 ⟨⟨x, hxZ⟩, trivial⟩ = ⟨x, F.germ U x hxU s⟩ := by
  obtain ⟨W, hzW, i, V, hV, s, hs⟩ :=
    GermPullback.exists_repr σ
      (show (⟨z, hz⟩ : ↥(TopCat.of Z)) ∈ (⊤ : Opens (TopCat.of Z)) from trivial)
  obtain ⟨A, hA, hAW⟩ := isOpen_induced_iff.mp W.isOpen
  refine ⟨⟨A, hA⟩ ⊓ V, ⟨(Set.ext_iff.mp hAW ⟨z, hz⟩).mpr hzW, hV ⟨⟨z, hz⟩, hzW⟩⟩,
    F.map (Opens.infLERight ⟨A, hA⟩ V).op s, fun x hxZ hxU ↦ ?_⟩
  rw [F.germ_res_apply (Opens.infLERight ⟨A, hA⟩ V) x hxU s]
  exact hs ⟨⟨x, hxZ⟩, (Set.ext_iff.mp hAW ⟨x, hxZ⟩).mp hxU.1⟩

/-! ### Surjectivity: every section on `Z` extends to a neighbourhood of `Z` -/

/-- **Stacks 09V3 in degree zero, surjectivity.** Let `F` be a sheaf of sets on `X` and let `Z`
be a quasi-compact subset of `X` any two distinct points of which can be separated by disjoint
opens of `X`.  Then every section of `F|_Z` is the family of germs along `Z` of a section of
`F` on an open neighbourhood of `Z`.

The separation hypothesis is the one of the shrinking lemma Stacks 0CY5, which is applied with
`p = 1` to a cover of `Z` by opens carrying local representatives of the section. -/
theorem exists_isOpen_restrictToSubset_eq (F : X.Sheaf (Type u)) {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (σ : sectionsOn F.presheaf Z) :
    ∃ (U : Opens X) (hZU : Z ⊆ (U : Set X)) (s : F.presheaf.obj (op U)),
      restrictToSubset F.presheaf hZU s = σ := by
  classical
  -- Local representatives of `σ`, indexed by the points of `Z`.
  choose U hmemU s hs using fun z : Z ↦ exists_isOpen_apply_eq_germ F.presheaf σ z.2
  -- The germ-agreement loci of pairs of representatives, as in Stacks 09V3.
  set W : (Fin 2 → Z) → Set X :=
    fun τ ↦ ((germEqOpens F.presheaf (s (τ 0)) (s (τ 1)) : Opens X) : Set X)
  have hmem_two : ∀ (τ : Fin 2 → Z) (x : X),
      x ∈ ⋂ k, ((U (τ k) : Opens X) : Set X) ↔ x ∈ U (τ 0) ∧ x ∈ U (τ 1) :=
    fun _ _ ↦ Set.mem_iInter.trans Fin.forall_fin_two
  have hWinter : ∀ τ, W τ ∩ Z = (⋂ k, ((U (τ k) : Opens X) : Set X)) ∩ Z := by
    refine fun τ ↦ Set.ext fun x ↦ ⟨fun hx ↦ ⟨?_, hx.2⟩, fun hx ↦ ⟨?_, hx.2⟩⟩
    · obtain ⟨h0, h1, -⟩ := mem_germEqOpens.1 hx.1
      exact (hmem_two τ x).2 ⟨h0, h1⟩
    · obtain ⟨h0, h1⟩ := (hmem_two τ x).1 hx.1
      exact mem_germEqOpens.2 ⟨h0, h1, germ_eq_of_germs_eq
        ((hs (τ 0) x hx.2 h0).symm.trans (hs (τ 1) x hx.2 h1))⟩
  -- Shrink the cover so that pairwise intersections land in the germ-agreement loci.
  obtain ⟨V, hVopen, hVcover, hVsub, -, hVinter⟩ :=
    TopologicalSpace.exists_isOpen_refinement_of_isCompact_of_pairwiseSeparated Z hZ hSep 1 Z
      (fun z ↦ ((U z : Opens X) : Set X)) (fun z ↦ (U z).isOpen) W
      (fun _ ↦ (germEqOpens F.presheaf _ _).isOpen)
      (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hmemU ⟨x, hx⟩⟩) hWinter
  -- Pairwise germ agreement of the representatives on the shrunken cover.
  have hpair : ∀ (z z' : Z) (x : X) (hx : x ∈ V z) (hx' : x ∈ V z'),
      F.presheaf.germ (U z) x (hVsub z hx) (s z)
        = F.presheaf.germ (U z') x (hVsub z' hx') (s z') := fun z z' x hx hx' ↦
    (mem_germEqOpens.1 (hVinter (fun k : Fin 2 ↦ if k = 0 then z else z')
      (Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨hx, hx'⟩)))).2.2
  -- Glue the restricted representatives.
  let Vo : Z → Opens X := fun z ↦ ⟨V z, hVopen z⟩
  have hVoU : ∀ z : Z, Vo z ≤ U z := fun z ↦ hVsub z
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf Vo
      (fun z ↦ F.presheaf.map (homOfLE (hVoU z)).op (s z)) := by
    intro z z'
    simp only [← Functor.map_comp_apply, ← op_comp]
    exact map_eq_of_germ_eq F _ _ (s z) (s z') fun x hx ↦ hpair z z' x hx.1 hx.2
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing Vo _ hcompat
  have hZsup : Z ⊆ ((iSup Vo : Opens X) : Set X) := fun _ hx ↦
    Opens.mem_iSup.2 (Set.mem_iUnion.1 (hVcover hx))
  refine ⟨iSup Vo, hZsup, g, GermPullback.ext fun w ↦ ?_⟩
  obtain ⟨z, hz⟩ := Set.mem_iUnion.1 (hVcover w.1.2)
  have hzVo : (w.1.1 : X) ∈ Vo z := hz
  rw [restrictToSubset_val,
    ← F.presheaf.germ_res_apply (Opens.leSupr Vo z) w.1.1 hzVo g, hg z,
    F.presheaf.germ_res_apply (homOfLE (hVoU z)) w.1.1 hzVo (s z)]
  exact (hs z w.1.1 w.1.2 (hVoU z hzVo)).symm

/-! ### The fibres of a closed map -/

variable {Y : Type v} [TopologicalSpace Y]

/-- If `f` is a closed map and `U` is an open subset of `X` containing the fibre `f⁻¹(y)`, then
`y` has an open neighbourhood `V` with `f⁻¹(V) ⊆ U`.  This is what makes a section on an open
neighbourhood of a fibre into a section of the pushforward near `y`, and is the step passing
from Stacks 09V3 to Stacks 09V5. -/
lemma exists_isOpen_preimage_subset_of_isClosedMap {f : ↥X → Y} (hf : IsClosedMap f) {y : Y}
    {U : Set X} (hU : IsOpen U) (hfib : f ⁻¹' {y} ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  have H : ∀ᶠ y' in nhds y, ∀ x ∈ f ⁻¹' {y'}, x ∈ U :=
    hf.eventually_nhds_fiber y fun x hx ↦ hU.mem_nhds (hfib hx)
  obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp H
  exact ⟨V, hVopen, hyV, fun x hx ↦ hVU hx x rfl⟩

/-- A fibre of `f` over a point of an open `V` lies in the preimage `f⁻¹(V)` (Stacks 09V5). -/
lemma preimage_singleton_subset_comap (f : C(↥X, Y)) {V : Opens Y} {y : Y} (hy : y ∈ V) :
    f ⁻¹' {y} ⊆ ((Opens.comap f V : Opens X) : Set X) := by
  rintro x (rfl : f x = y)
  exact hy

/-- **Stacks 09V5 in degree zero, surjectivity.** Let `f : X → Y` be a continuous closed map,
let `F` be a sheaf of sets on `X`, and let `y : Y` be a point whose fibre `f⁻¹(y)` is
quasi-compact and has its distinct points separated by disjoint opens of `X`.  Then every
section of `F|_{f⁻¹(y)}` comes from a section of `F` on `f⁻¹(V)` for some open neighbourhood
`V` of `y`, that is, from a section of the pushforward `f_*F` near `y`.

Together with `exists_isOpen_mem_map_eq_of_restrictToSubset_eq_of_isClosedMap` this says that
the canonical map `(f_*F)_y → Γ(f⁻¹(y), F|_{f⁻¹(y)})` is bijective. -/
theorem exists_isOpen_mem_restrictToSubset_eq_of_isClosedMap (F : X.Sheaf (Type u))
    (f : C(↥X, Y)) (hf : IsClosedMap f) (y : Y) (hZ : IsCompact (f ⁻¹' {y}))
    (hSep : ∀ x ∈ f ⁻¹' {y}, ∀ x' ∈ f ⁻¹' {y}, x ≠ x' →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ x' ∈ B ∧ Disjoint A B)
    (σ : sectionsOn F.presheaf (f ⁻¹' {y})) :
    ∃ (V : Opens Y) (hy : y ∈ V) (s : F.presheaf.obj (op (Opens.comap f V))),
      restrictToSubset F.presheaf (preimage_singleton_subset_comap f hy) s = σ := by
  obtain ⟨U, hZU, t, rfl⟩ := exists_isOpen_restrictToSubset_eq F hZ hSep σ
  obtain ⟨V, hVopen, hyV, hVU⟩ := exists_isOpen_preimage_subset_of_isClosedMap hf U.isOpen hZU
  have hle : (Opens.comap f ⟨V, hVopen⟩ : Opens X) ≤ U := hVU
  refine ⟨⟨V, hVopen⟩, hyV, F.presheaf.map (homOfLE hle).op t, ?_⟩
  refine GermPullback.ext fun w ↦ ?_
  rw [restrictToSubset_val, restrictToSubset_val,
    F.presheaf.germ_res_apply (homOfLE hle) w.1.1 _ t]

/-- **Stacks 09V5 in degree zero, injectivity.** In the situation of
`exists_isOpen_mem_restrictToSubset_eq_of_isClosedMap`, two sections of `F` on the preimages
`f⁻¹(V)` and `f⁻¹(V')` of open neighbourhoods of `y` whose germ families along the fibre
`f⁻¹(y)` agree already agree on `f⁻¹(V'')` for some open neighbourhood `V''` of `y` inside
both `V` and `V'`.  That is, the canonical map `(f_*F)_y → Γ(f⁻¹(y), F|_{f⁻¹(y)})` is
injective.

Neither quasi-compactness nor separation of the fibre is needed here. -/
theorem exists_isOpen_mem_map_eq_of_restrictToSubset_eq_of_isClosedMap (F : X.Sheaf (Type u))
    (f : C(↥X, Y)) (hf : IsClosedMap f) {y : Y} {V V' : Opens Y} (hy : y ∈ V) (hy' : y ∈ V')
    (s : F.presheaf.obj (op (Opens.comap f V))) (s' : F.presheaf.obj (op (Opens.comap f V')))
    (h : restrictToSubset F.presheaf (preimage_singleton_subset_comap f hy) s
      = restrictToSubset F.presheaf (preimage_singleton_subset_comap f hy') s') :
    ∃ (V'' : Opens Y) (_ : y ∈ V'') (hV : V'' ≤ V) (hV' : V'' ≤ V'),
      F.presheaf.map (homOfLE (Opens.comap_mono f hV)).op s
        = F.presheaf.map (homOfLE (Opens.comap_mono f hV')).op s' := by
  obtain ⟨W, hZW, hWV, hWV', hW⟩ :=
    exists_isOpen_eq_of_restrictToSubset_eq F (preimage_singleton_subset_comap f hy)
      (preimage_singleton_subset_comap f hy') s s' h
  obtain ⟨V₀, hV₀open, hyV₀, hV₀W⟩ :=
    exists_isOpen_preimage_subset_of_isClosedMap hf W.isOpen hZW
  have factor : ∀ {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) (t : F.presheaf.obj (op C)),
      F.presheaf.map (homOfLE (hAB.trans hBC)).op t
        = F.presheaf.map (homOfLE hAB).op (F.presheaf.map (homOfLE hBC).op t) := by
    intro A B C hAB hBC t
    rw [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
  have hUW : (Opens.comap f (⟨V₀, hV₀open⟩ ⊓ V ⊓ V' : Opens Y) : Opens X) ≤ W :=
    fun x hx ↦ hV₀W hx.1.1
  refine ⟨⟨V₀, hV₀open⟩ ⊓ V ⊓ V', ⟨⟨hyV₀, hy⟩, hy'⟩, inf_le_left.trans inf_le_right, inf_le_right,
    ?_⟩
  rw [factor hUW hWV s, hW, factor hUW hWV' s']

end Stacks.Topology.SectionsOnQuasiCompactSubset

end
