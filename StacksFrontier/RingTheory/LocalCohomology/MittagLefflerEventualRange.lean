module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.CategoryTheory.MittagLefflerSections

/-!
# The limit of a Mittag-Leffler tower of modules surjects onto the eventual ranges

Let `F : ℕᵒᵖ ⥤ ModuleCat A` be an inverse system of modules satisfying the Mittag-Leffler
condition. The eventual range `⋂_{k ≥ i} Im(F_k → F_i)` at a level `i` — the *stable image* of
the transition maps — is then contained in the image of the projection `lim F ⟶ F_i`, hence
equal to it, the other inclusion being formal.

That is the step the proof of [Stacks, Tag 0EFX] compresses into "(some details omitted)": an
element of the stable image at level `i` has to be extended to a compatible family, and the
extension exists because the stable images form a *surjective* tower.

The extension is produced on the level of sets. Mathlib's `CategoryTheory.Functor.toPreimages`
cuts out of a system of sets the subsystem of elements mapping into a prescribed set at one
level; `CategoryTheory.Functor.IsMittagLeffler.toPreimages` says that subsystem is again
Mittag-Leffler, its values are nonempty exactly because the prescribed element lies in the
eventual range, and `nonempty_sections_of_isMittagLeffler` then provides a section. A compatible
family of elements of a tower of modules is the family of components of an element of the inverse
limit, by `ModuleCat.exists_limit_π_eq_of_sections`.

## Main results

* `Stacks.LocalCohomology.exists_sections_val_eq_of_mem_eventualRange` — a point of the eventual
  range of a Mittag-Leffler system of sets over `ℕᵒᵖ` extends to a section.
* `Stacks.LocalCohomology.mem_range_limit_π_of_mem_eventualRange` — the image of a projection of
  the inverse limit of a Mittag-Leffler tower of modules contains the eventual range at that
  level.
* `Stacks.LocalCohomology.isMittagLeffler_forget_of_range_eq`,
  `Stacks.LocalCohomology.mem_eventualRange_of_range_eq` — the Mittag-Leffler condition and
  membership of the eventual range, read off the ranges of the transition maps as `A`-linear maps.
* `Stacks.LocalCohomology.range_transitionMap_le_range_cone_π` — the practical form: for a cone
  whose limit comparison is invertible, each level `i` has an index `C ≥ i` beyond which the image
  of every transition map `F_k → F_i` is contained in the image of the projection `c.pt ⟶ F_i`.

## Implementation notes

The Mittag-Leffler hypothesis is `CategoryTheory.Functor.IsMittagLeffler` for the system of
underlying sets, not the subobject-valued `IsMittagLefflerCategorical`; that is the form the
inverse-limit results of
`StacksFrontier/Algebra/Homology/ShortComplex/InverseLimit.lean` are stated in as well.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.LocalCohomology

/-! ### Extending a point of the eventual range to a section -/

/-- **A point of the eventual range extends to a section.** For a Mittag-Leffler system of sets
over `ℕᵒᵖ` and a point `y` of the eventual range at a level `i`, there is a section of the system
whose value at `i` is `y`.

The subsystem of elements mapping to `y` at level `i` is Mittag-Leffler by
`CategoryTheory.Functor.IsMittagLeffler.toPreimages`. Its value at `j` is the intersection of the
preimages of `{y}` along the morphisms `j ⟶ i`, of which there is at most one, `ℕ` being a poset:
when there is one the value is nonempty because `y` lies in the range of that transition map, and
when there is none the value is the whole of `F_j`, which is nonempty because then `F_i` maps to
it. A section of the subsystem is a section of the system taking the value `y` at `i`. -/
theorem exists_sections_val_eq_of_mem_eventualRange {F : ℕᵒᵖ ⥤ Type u}
    (hML : F.IsMittagLeffler) (i : ℕᵒᵖ) (y : F.obj i) (hy : y ∈ F.eventualRange i) :
    ∃ s : F.sections, s.val i = y := by
  classical
  have hne : ∀ j : ℕᵒᵖ, Nonempty ((F.toPreimages {y}).obj j) := by
    intro j
    by_cases hji : i.unop ≤ j.unop
    · obtain ⟨x, hx⟩ := F.mem_eventualRange_iff.1 hy ((homOfLE hji).op : j ⟶ i)
      refine ⟨⟨x, Set.mem_iInter.2 fun g => ?_⟩⟩
      have hg : g = ((homOfLE hji).op : j ⟶ i) := Subsingleton.elim _ _
      subst hg
      exact hx
    · have hij : j.unop ≤ i.unop := le_of_lt (Nat.lt_of_not_le hji)
      refine ⟨⟨F.map ((homOfLE hij).op : i ⟶ j) y, Set.mem_iInter.2 fun g => ?_⟩⟩
      exact absurd (leOfHom g.unop) hji
  obtain ⟨t⟩ := nonempty_sections_of_isMittagLeffler (hML.toPreimages (s := {y})) hne
  refine ⟨⟨fun j => (t.val j).val, fun {j k} f => congrArg Subtype.val (t.property f)⟩, ?_⟩
  have hmem := Set.mem_iInter.1 (t.val i).property (𝟙 i)
  simpa only [F.map_id, types_id_apply, Set.mem_preimage, Set.mem_singleton_iff] using hmem

/-! ### The image of a projection of the inverse limit -/

variable {A : Type u} [Ring A]

/-- **The eventual range is hit by the projection of the inverse limit.** For a tower of
`A`-modules whose system of underlying sets is Mittag-Leffler, every element of the eventual
range at a level `i` is in the image of `lim F ⟶ F_i`.

The element extends to a compatible family by
`Stacks.LocalCohomology.exists_sections_val_eq_of_mem_eventualRange`, and a compatible family is
the family of components of an element of the inverse limit, by
`ModuleCat.exists_limit_π_eq_of_sections`. -/
theorem mem_range_limit_π_of_mem_eventualRange (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hML : (F ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler) (i : ℕᵒᵖ) (y : F.obj i)
    (hy : y ∈ (F ⋙ forget (ModuleCat.{u} A)).eventualRange i) :
    y ∈ LinearMap.range (limit.π F i).hom := by
  obtain ⟨s, hs⟩ := exists_sections_val_eq_of_mem_eventualRange hML i y hy
  obtain ⟨x, hx⟩ := ModuleCat.exists_limit_π_eq_of_sections F s
  exact ⟨x, (hx i).trans hs⟩

/-- The same conclusion for a cone whose limit comparison is invertible: the image of its `i`-th
projection contains the eventual range. -/
theorem mem_range_cone_π_of_mem_eventualRange {F : ℕᵒᵖ ⥤ ModuleCat.{u} A} (c : Cone F)
    (hc : IsIso (limit.lift F c))
    (hML : (F ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler) (i : ℕᵒᵖ) (y : F.obj i)
    (hy : y ∈ (F ⋙ forget (ModuleCat.{u} A)).eventualRange i) :
    y ∈ LinearMap.range (c.π.app i).hom := by
  obtain ⟨x, hx⟩ := mem_range_limit_π_of_mem_eventualRange F hML i y hy
  have := hc
  refine ⟨(CategoryTheory.inv (limit.lift F c)).hom x, ?_⟩
  rw [← ModuleCat.comp_apply, ← limit.lift_π c i, IsIso.inv_hom_id_assoc, hx]

/-! ### The Mittag-Leffler condition read off the ranges of the transition maps -/

/-- If the ranges of the transition maps stabilize from `C` on, the image of an element of
`F_C` in `F_j` is also the image of an element of `F_k`, for every `j ≤ k`. -/
private theorem exists_map_eq_of_range_eq {F : ℕᵒᵖ ⥤ ModuleCat.{u} A} {j C : ℕ} (hjC : j ≤ C)
    (hC : ∀ (k : ℕ) (hCk : C ≤ k),
      LinearMap.range (F.map (homOfLE (hjC.trans hCk)).op).hom =
        LinearMap.range (F.map (homOfLE hjC).op).hom)
    {k : ℕ} (hjk : j ≤ k) (x : F.obj (op C)) :
    ∃ w : F.obj (op k),
      (F ⋙ forget (ModuleCat.{u} A)).map (homOfLE hjk).op w = (F.map (homOfLE hjC).op).hom x := by
  rcases le_total C k with hCk | hkC
  · obtain ⟨w, hw⟩ : (F.map (homOfLE hjC).op).hom x ∈
        LinearMap.range (F.map (homOfLE (hjC.trans hCk)).op).hom := by
      rw [hC k hCk]
      exact ⟨x, rfl⟩
    exact ⟨w, hw⟩
  · refine ⟨(F.map (homOfLE hkC).op).hom x, ?_⟩
    change (F.map (homOfLE hjk).op).hom ((F.map (homOfLE hkC).op).hom x) = _
    rw [← ModuleCat.comp_apply, ← F.map_comp,
      show (homOfLE hkC).op ≫ (homOfLE hjk).op = (homOfLE hjC).op from Subsingleton.elim _ _]

/-- The Mittag-Leffler condition for the underlying sets of a tower of modules, from the
stabilization of the ranges of the transition maps as `A`-linear maps. -/
theorem isMittagLeffler_forget_of_range_eq {F : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (h : ∀ i : ℕ, ∃ C : ℕ, ∃ hiC : i ≤ C, ∀ (k : ℕ) (hCk : C ≤ k),
      LinearMap.range (F.map (homOfLE (hiC.trans hCk)).op).hom =
        LinearMap.range (F.map (homOfLE hiC).op).hom) :
    (F ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler := by
  intro j
  obtain ⟨C, hjC, hC⟩ := h j.unop
  refine ⟨op C, (homOfLE hjC).op, fun {k} g => ?_⟩
  have hjk : j.unop ≤ k.unop := leOfHom g.unop
  have hg : g = (homOfLE hjk).op := Subsingleton.elim _ _
  subst hg
  rintro z ⟨x, rfl⟩
  exact exists_map_eq_of_range_eq hjC hC hjk x

/-- An element in the range of a transition map from a stabilizing index lies in the eventual
range of the underlying sets. -/
theorem mem_eventualRange_of_range_eq {F : ℕᵒᵖ ⥤ ModuleCat.{u} A} {j C : ℕ} (hjC : j ≤ C)
    (hC : ∀ (k : ℕ) (hCk : C ≤ k),
      LinearMap.range (F.map (homOfLE (hjC.trans hCk)).op).hom =
        LinearMap.range (F.map (homOfLE hjC).op).hom)
    {y : F.obj (op j)} (hy : y ∈ LinearMap.range (F.map (homOfLE hjC).op).hom) :
    y ∈ (F ⋙ forget (ModuleCat.{u} A)).eventualRange (op j) := by
  refine (F ⋙ forget (ModuleCat.{u} A)).mem_eventualRange_iff.2 fun {k} g => ?_
  have hjk : j ≤ k.unop := leOfHom g.unop
  have hg : g = (homOfLE hjk).op := Subsingleton.elim _ _
  subst hg
  obtain ⟨x, rfl⟩ := hy
  exact exists_map_eq_of_range_eq hjC hC hjk x

/-- **The practical form.** For a cone `c` on a tower of `A`-modules whose limit comparison is
invertible and whose transition-map ranges stabilize, each level `i` has an index `C ≥ i` beyond
which the image of every transition map `F_k ⟶ F_i` is contained in the image of the projection
`c.pt ⟶ F_i`.

This is the statement the first paragraph of the proof of [Stacks, Tag 0EFX] uses: the stable
image of `{H^i_𝔪(M/IⁿM)}` at a level is the image of `H^i_𝔪(M)` there. -/
theorem range_transitionMap_le_range_cone_π {F : ℕᵒᵖ ⥤ ModuleCat.{u} A} (c : Cone F)
    (hc : IsIso (limit.lift F c))
    (h : ∀ i : ℕ, ∃ C : ℕ, ∃ hiC : i ≤ C, ∀ (k : ℕ) (hCk : C ≤ k),
      LinearMap.range (F.map (homOfLE (hiC.trans hCk)).op).hom =
        LinearMap.range (F.map (homOfLE hiC).op).hom)
    (i : ℕ) :
    ∃ C : ℕ, ∃ _hiC : i ≤ C, ∀ (k : ℕ) (hik : i ≤ k) (_hCk : C ≤ k),
      LinearMap.range (F.map (homOfLE hik).op).hom ≤
        LinearMap.range (c.π.app (op i)).hom := by
  obtain ⟨C, hiC, hC⟩ := h i
  refine ⟨C, hiC, fun k hik hCk y hy => ?_⟩
  refine mem_range_cone_π_of_mem_eventualRange c hc
    (isMittagLeffler_forget_of_range_eq h) (op i) y ?_
  refine mem_eventualRange_of_range_eq hiC hC ?_
  rw [← hC k hCk,
    show (homOfLE (hiC.trans hCk) : (i : ℕ) ⟶ k) = homOfLE hik from Subsingleton.elim _ _]
  exact hy

end Stacks.LocalCohomology

end
