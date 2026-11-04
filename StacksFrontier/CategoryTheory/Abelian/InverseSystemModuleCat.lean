module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem

/-!
# The Mittag-Leffler condition for an inverse system of modules, in terms of ranges

For an inverse system of modules `F : ℕᵒᵖ ⥤ ModuleCat A` the lattice of subobjects of
`F.obj (op i)` is order isomorphic to the lattice of submodules, by
`ModuleCat.subobjectModule`, and that isomorphism carries the categorical transition image
`transitionImage F i k h` to the range of the transition map. Consequently the Mittag-Leffler
condition of Stacks Tag 02N0, which is a statement about subobjects, is equivalent to the
elementary statement that the ranges of the transition maps `F.obj (op k) → F.obj (op i)`
stabilize as `k` grows.

This file records that dictionary and the resulting criterion, which is how the condition is
verified in practice: one exhibits, for each `i`, a bound `b i` beyond which every transition
map into `F.obj (op i)` has one and the same range.

## Main results

* `subobjectModule_transitionImage` — the order isomorphism `ModuleCat.subobjectModule` sends
  the transition image `transitionImage F i k h` to `LinearMap.range` of the transition map.
* `isMittagLefflerCategorical_of_forall_exists_range_eq` — stabilization of the ranges of the
  transition maps implies the Mittag-Leffler condition.
* `IsMittagLefflerCategorical.exists_range_eq` — its converse, which is how the condition is
  consumed by arguments about elements.
* `isMittagLefflerCategorical_of_range_eq_of_le` and
  `isMittagLefflerCategorical_of_range_eq_submodule` — the same criterion phrased with an
  explicit bound `b : ℕ → ℕ`, the latter taking the stabilized value as a given family of
  submodules.
* `isMittagLeffler_forget_of_isMittagLefflerCategorical` — the Mittag-Leffler condition for an
  inverse system of modules implies the Mittag-Leffler condition of
  `CategoryTheory.Functor.IsMittagLeffler` for the underlying inverse system of sets.

## References

* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- The image of a transition map of an inverse system of modules, read as a submodule through
the lattice isomorphism `ModuleCat.subobjectModule`, is the range of the corresponding linear
map. -/
theorem subobjectModule_transitionImage {A : Type u} [Ring A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A}
    (i k : ℕ) (h : i ≤ k) :
    ModuleCat.subobjectModule (F.obj (op i)) (transitionImage F i k h) =
      LinearMap.range (F.map (homOfLE h).op).hom := by
  have heq :
      Subobject.mk (image.ι (F.map (homOfLE h).op)) =
        Subobject.mk (ModuleCat.ofHom (F.map (homOfLE h).op).hom.range.subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange _)
      (ModuleCat.imageIsoRange_hom_subtype _)
  rw [transitionImage, heq]
  exact (ModuleCat.subobjectModule (F.obj (op i))).apply_symm_apply _

/-- The transition images `transitionImage F i k hk` and `transitionImage F i l hl` agree
exactly when the ranges of the corresponding transition maps agree. -/
private theorem transitionImage_eq_iff_range_eq {A : Type u} [Ring A]
    {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {i k l : ℕ} (hk : i ≤ k) (hl : i ≤ l) :
    transitionImage F i k hk = transitionImage F i l hl ↔
      LinearMap.range (F.map (homOfLE hk).op).hom =
        LinearMap.range (F.map (homOfLE hl).op).hom := by
  rw [← (ModuleCat.subobjectModule (F.obj (op i))).injective.eq_iff,
    subobjectModule_transitionImage, subobjectModule_transitionImage]

/-- A transition map factors through an intermediate transition map. -/
private theorem hom_map_homOfLE_comp {A : Type u} [Ring A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (F.map (homOfLE (hij.trans hjk)).op).hom =
      (F.map (homOfLE hij).op).hom.comp (F.map (homOfLE hjk).op).hom := by
  rw [← ModuleCat.hom_comp, ← F.map_comp]
  rfl

/-- **A range criterion for the Mittag-Leffler condition.** If for every `i` the ranges of the
transition maps `F.obj (op k) → F.obj (op i)` are eventually constant in `k`, then the inverse
system of modules `F` satisfies the Mittag-Leffler condition of Stacks Tag 02N0. -/
theorem isMittagLefflerCategorical_of_forall_exists_range_eq {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (h : ∀ i : ℕ, ∃ c : ℕ, ∃ hic : i ≤ c, ∀ k : ℕ, ∀ hck : c ≤ k,
      LinearMap.range (F.map (homOfLE (hic.trans hck)).op).hom =
        LinearMap.range (F.map (homOfLE hic).op).hom) :
    IsMittagLefflerCategorical F := by
  intro i
  obtain ⟨c, hic, hstab⟩ := h i
  refine ⟨c, hic, fun k hck => ?_⟩
  exact (transitionImage_eq_iff_range_eq _ _).2 (hstab k hck)

/-- **The range form of the Mittag-Leffler condition.** The converse of
`isMittagLefflerCategorical_of_forall_exists_range_eq`: the Mittag-Leffler condition of Stacks
Tag 02N0, a statement about subobjects, gives the eventual constancy of the ranges of the
transition maps, which is the form in which it is consumed by arguments about elements. -/
theorem IsMittagLefflerCategorical.exists_range_eq {A : Type u} [Ring A]
    {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} (hF : IsMittagLefflerCategorical F) (i : ℕ) :
    ∃ c : ℕ, ∃ hic : i ≤ c, ∀ k : ℕ, ∀ hck : c ≤ k,
      LinearMap.range (F.map (homOfLE (hic.trans hck)).op).hom =
        LinearMap.range (F.map (homOfLE hic).op).hom := by
  obtain ⟨c, hic, hstab⟩ := hF i
  refine ⟨c, hic, fun k hck => ?_⟩
  exact (transitionImage_eq_iff_range_eq _ _).1 (hstab k hck)

/-- **A range criterion for the Mittag-Leffler condition, with an explicit bound.** If `b i` is
a bound beyond which every transition map into `F.obj (op i)` has the same range as the one
from `F.obj (op (b i))`, then `F` satisfies the Mittag-Leffler condition. -/
theorem isMittagLefflerCategorical_of_range_eq_of_le {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (b : ℕ → ℕ) (hb : ∀ i, i ≤ b i)
    (h : ∀ i k, b i ≤ k → ∀ hik : i ≤ k,
      LinearMap.range (F.map (homOfLE hik).op).hom =
        LinearMap.range (F.map (homOfLE (hb i)).op).hom) :
    IsMittagLefflerCategorical F :=
  isMittagLefflerCategorical_of_forall_exists_range_eq F fun i =>
    ⟨b i, hb i, fun k hck => h i k hck _⟩

/-- **A range criterion for the Mittag-Leffler condition, with the stabilized value named.** If
every transition map `F.obj (op k) → F.obj (op i)` with `k ≥ b i` has range the given submodule
`N i`, then `F` satisfies the Mittag-Leffler condition. -/
theorem isMittagLefflerCategorical_of_range_eq_submodule {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (b : ℕ → ℕ) (hb : ∀ i, i ≤ b i)
    (N : ∀ i : ℕ, Submodule A (F.obj (op i)))
    (h : ∀ i k, b i ≤ k → ∀ hik : i ≤ k, LinearMap.range (F.map (homOfLE hik).op).hom = N i) :
    IsMittagLefflerCategorical F :=
  isMittagLefflerCategorical_of_range_eq_of_le F b hb fun i k hbk hik => by
    rw [h i k hbk hik, h i (b i) le_rfl (hb i)]

/-- Stabilization of the images of the transition maps, as subobjects, implies the Mittag-Leffler
condition for the underlying inverse system of sets. -/
theorem isMittagLeffler_forget_of_isMittagLefflerCategorical {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (hF : IsMittagLefflerCategorical F) :
    (F ⋙ forget (ModuleCat.{v} A)).IsMittagLeffler := by
  intro j
  obtain ⟨c, hjc, hstab⟩ := hF.exists_range_eq j.unop
  refine ⟨op c, (homOfLE hjc).op, ?_⟩
  intro k g
  have hjk : j.unop ≤ k.unop := leOfHom g.unop
  have hgeq : g = (homOfLE hjk).op := Subsingleton.elim _ _
  have hcm : c ≤ max c k.unop := le_max_left _ _
  have hkm : k.unop ≤ max c k.unop := le_max_right _ _
  have hrange := hstab (max c k.unop) hcm
  subst hgeq
  intro x hx
  have hx' : x ∈ LinearMap.range (F.map (homOfLE (hjc.trans hcm)).op).hom := by
    rw [hrange]
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  rw [hom_map_homOfLE_comp F hjk hkm] at hx'
  obtain ⟨y, hy⟩ := hx'
  exact ⟨(F.map (homOfLE hkm).op).hom y, hy⟩

/-- The Mittag-Leffler condition for the underlying inverse system of sets implies the
stabilization of the images of the transition maps, as subobjects. -/
theorem isMittagLefflerCategorical_of_isMittagLeffler_forget {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (hF : (F ⋙ forget (ModuleCat.{v} A)).IsMittagLeffler) :
    IsMittagLefflerCategorical F := by
  refine isMittagLefflerCategorical_of_forall_exists_range_eq F fun i => ?_
  obtain ⟨c, f, hf⟩ := hF (op i)
  have hic : i ≤ c.unop := leOfHom f.unop
  have hf' : f = (homOfLE hic).op := Subsingleton.elim _ _
  subst hf'
  refine ⟨c.unop, hic, fun k hck => le_antisymm ?_ ?_⟩
  · rw [hom_map_homOfLE_comp F hic hck]
    exact LinearMap.range_comp_le_range _ _
  · intro x hx
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hx
    obtain ⟨z, hz⟩ := hf (homOfLE (hic.trans hck)).op ⟨y, hy⟩
    exact LinearMap.mem_range.2 ⟨z, hz⟩

end
