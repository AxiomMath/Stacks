module


import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Monoidal.Mon
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
import StacksCore.Tactic.EgaSgaAttribute

/-! # Essentially constant systems and cofinal functors

Stacks 0A1S (Lemma 4.22.11): if `H : I ⥤ J` is a cofinal functor between filtered categories, then
a diagram `M : J ⥤ C` is essentially constant if and only if `H ⋙ M` is. Here "essentially
constant" is `IsEssentiallyConstantInd`, the reading of Stacks 05PU(1) / Definition 4.22.1(1)
provided by `StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject`, and the Stacks notion of
*cofinal* is Mathlib's `Functor.Final` — not `Functor.Initial`.

The two directions are `essentiallyConstant_comp_final_of` and
`essentiallyConstant_of_comp_final`, mirroring the cofiltered/initial statement 0A1T. Each
transports the witnessing cocone along `H` by a Mathlib construction: `Cocone.whisker H`
restricts a cocone on `M` to one on `H ⋙ M`, and `Functor.Final.extendCocone` extends a cocone
on `H ⋙ M` back to one on `M` — the latter being well defined precisely because
`StructuredArrow d H` is filtered, which is what `welldef` records.

Morphisms compose left-to-right: the Stacks-style composite `g ∘ f` is written `f ≫ g`.
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.EssentiallyConstantInd

/-
## Background: Definition 1 (Filtered index category, Stacks Tag 002V)

An index category `I` is *filtered* if it is nonempty and
- for every pair of objects `i, i'` there is an object `k` with morphisms
  `i ⟶ k`, `i' ⟶ k`, and
- for every pair of parallel morphisms `f, g : i ⟶ i'` there is a morphism
  `h : i' ⟶ k` coequalizing them.
This is Mathlib's `CategoryTheory.IsFiltered` (which includes nonemptiness).
-/

/-
## Background: Definition 2 (Essentially constant filtered diagram, Stacks Tag 05PU(1))

This is `CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantInd`: there are a cocone `t`
on `M`, an index `i₀` and a morphism `b : t.pt ⟶ M.obj i₀` with `b ≫ t.ι.app i₀ = 𝟙 t.pt`, such
that for all `j` there exist `k` and morphisms `σ : i₀ ⟶ k`, `τ : j ⟶ k` with
`M.map τ = t.ι.app j ≫ b ≫ M.map σ`.
-/

-- suggested change: `coc` and `welldef` are root-namespace names with no mathematical content;
-- they belong in `CategoryTheory.Functor.Final` as `exists_cocone` and `map_comp_app_eq`.

/-- Common cocone in the structured-arrow category `StructuredArrow d H`.
Since `I` is filtered and `H` is final, `StructuredArrow d H` is filtered, so any
two objects `(c₁, k₁)`, `(c₂, k₂)` admit a common cocone in `I` compatible with
`H`. -/
@[sga "4 V 8.1.6" "special case"]
theorem coc {I : Type*} [Category I] {J : Type*} [Category J]
    [IsFiltered I] [IsFiltered J] (H : I ⥤ J) [H.Final] (d : J) (c₁ c₂ : I)
    (k₁ : d ⟶ H.obj c₁) (k₂ : d ⟶ H.obj c₂) :
    ∃ (c : I) (p₁ : c₁ ⟶ c) (p₂ : c₂ ⟶ c), k₁ ≫ H.map p₁ = k₂ ≫ H.map p₂ := by
  have : IsFiltered (StructuredArrow d H) :=
    (Functor.final_iff_isFiltered_structuredArrow H).mp ‹H.Final› d
  let A : StructuredArrow d H := .mk k₁
  let B : StructuredArrow d H := .mk k₂
  exact ⟨(IsFiltered.max A B).right, (IsFiltered.leftToMax A B).right,
    (IsFiltered.rightToMax A B).right,
    (StructuredArrow.w (IsFiltered.leftToMax A B)).trans
      (StructuredArrow.w (IsFiltered.rightToMax A B)).symm⟩

/-- Well-definedness: for a cocone `a : (H ⋙ M) ⟶ const X` on the filtered `I`,
the quantity `M.map g ≫ a.app c` (for `g : d ⟶ H.obj c`) depends only on `d`,
not on the chosen lift `(c, g)` in `StructuredArrow d H`.

Both sides compute the component at `d` of `Functor.Final.extendCocone.obj (Cocone.mk X a)`. -/
theorem welldef {C : Type*} [Category C] {I : Type*} [Category I] {J : Type*}
    [Category J] [IsFiltered I] [IsFiltered J] (H : I ⥤ J) [H.Final] (M : J ⥤ C)
    (X : C) (a : (H ⋙ M) ⟶ (Functor.const I).obj X) (d : J)
    (c c' : I) (g : d ⟶ H.obj c) (g' : d ⟶ H.obj c') :
    M.map g ≫ a.app c = M.map g' ≫ a.app c' :=
  (Functor.Final.extendCocone_obj_ι_app' (F := H) (G := M) (Cocone.mk X a) g).symm.trans
    (Functor.Final.extendCocone_obj_ι_app' (F := H) (G := M) (Cocone.mk X a) g')

/-
## Background: Definition 3 (Cofinal functor, Stacks Tag 04E6)

The Stacks notion of *cofinal* functor `H : I ⥤ J` coincides with Mathlib's
`CategoryTheory.Functor.Final`. We therefore formalize the hypothesis as
`[H.Final]`. (Note: this is NOT Mathlib's `Functor.Initial`.)
-/

/-- Simultaneous lift along a cofinal functor of a cospan in `J` and of an arrow `t` out of its
apex's source. Given `uJ : H.obj j ⟶ kJ`, `vJ : i₀ ⟶ kJ` and `t : i₀ ⟶ H.obj i₀'`, there are an
object `c` of `I`, arrows `u : j ⟶ c`, `v : i₀' ⟶ c` and a connecting arrow `z : kJ ⟶ H.obj c`
of `J` with `H.map u = uJ ≫ z` and `t ≫ H.map v = vJ ≫ z`.

This is the combinatorial content of the forward direction of Stacks 0A1S, and the exact
`Functor.Final` counterpart of `coherence_lift_full` for an initial functor. It is obtained from
two applications of `coc`: one to push `uJ` into the image of `H`, one to merge the result
with `t`. -/
theorem exists_lift_cospan {I : Type*} [Category I] {J : Type*} [Category J]
    [IsFiltered I] [IsFiltered J] (H : I ⥤ J) [H.Final] {j i₀' : I} {i₀ kJ : J}
    (t : i₀ ⟶ H.obj i₀') (uJ : H.obj j ⟶ kJ) (vJ : i₀ ⟶ kJ) :
    ∃ (c : I) (u : j ⟶ c) (v : i₀' ⟶ c) (z : kJ ⟶ H.obj c),
      H.map u = uJ ≫ z ∧ t ≫ H.map v = vJ ≫ z := by
  set w : kJ ⟶ H.obj (Functor.Final.lift H kJ) := Functor.Final.homToLift H kJ
  obtain ⟨c₁, u₁, h₁, hu₁⟩ := coc H (H.obj j) j (Functor.Final.lift H kJ) (𝟙 _) (uJ ≫ w)
  obtain ⟨c₂, s₁, s₂, hs⟩ := coc H i₀ i₀' c₁ t (vJ ≫ w ≫ H.map h₁)
  refine ⟨c₂, u₁ ≫ s₂, s₁, w ≫ H.map h₁ ≫ H.map s₂, ?_, ?_⟩
  · rw [H.map_comp, show H.map u₁ = uJ ≫ w ≫ H.map h₁ by simpa using hu₁]
    simp
  · rw [hs]
    simp

/-- **Forward direction (→) of Stacks Tag 0A1S.** If `M` is essentially constant then so is
`H ⋙ M`.

Whisker the witnessing cocone along `H` (`Cocone.whisker H`, whose component at `i` is the
component of the original at `H.obj i`), take the index `i₀' := Final.lift H i₀` and the section
`b ≫ M.map s` for `s := Final.homToLift H i₀ : i₀ ⟶ H.obj i₀'`. The retraction clause follows
from cocone naturality of the witnessing cocone along `s`, and the cofinality clause from
`exists_lift_cospan` applied to the `J`-cofinality data of `M` at the object `H.obj j`. -/
theorem essentiallyConstant_comp_final_of
    {C : Type*} [Category C] {I : Type*} [Category I] {J : Type*} [Category J]
    [IsFiltered I] [IsFiltered J] (H : I ⥤ J) [H.Final] (M : J ⥤ C)
    (h : IsEssentiallyConstantInd M) : IsEssentiallyConstantInd (H ⋙ M) := by
  obtain ⟨t, i₀, b, hsec, hcond⟩ := h
  set s : i₀ ⟶ H.obj (Functor.Final.lift H i₀) := Functor.Final.homToLift H i₀
  refine ⟨t.whisker H, Functor.Final.lift H i₀, b ≫ M.map s, ?_, fun j => ?_⟩
  · dsimp only [Cocone.whisker_ι, Functor.whiskerLeft_app]
    rw [Category.assoc, t.w s]; exact hsec
  · obtain ⟨kJ, vJ, uJ, hJ⟩ := hcond (H.obj j)
    obtain ⟨c, u, v, z, hu, hv⟩ := exists_lift_cospan H s uJ vJ
    refine ⟨c, v, u, ?_⟩
    dsimp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Functor.comp_map]
    rw [hu, M.map_comp, hJ, Category.assoc, Category.assoc, ← M.map_comp, ← hv, M.map_comp]
    simp

/-- **Backward direction (←) of Stacks Tag 0A1S.** If `H ⋙ M` is essentially constant then so
is `M`.

Extend the witnessing cocone along `H` by `Functor.Final.extendCocone`, whose component at `d`
is `M.map (homToLift H d) ≫ t.ι.app (lift H d)` — well defined by `welldef` — and keep the index
`H.obj i₀` and the section `b`. The retraction clause is `hsec` after
`Functor.Final.extendCocone_obj_ι_app'` computes the component at `H.obj i₀`, and the
cofinality clause is the cofinality clause of `H ⋙ M` at `lift H d`, precomposed with
`homToLift H d`. -/
theorem essentiallyConstant_of_comp_final
    {C : Type*} [Category C] {I : Type*} [Category I] {J : Type*} [Category J]
    [IsFiltered I] [IsFiltered J] (H : I ⥤ J) [H.Final] (M : J ⥤ C)
    (h : IsEssentiallyConstantInd (H ⋙ M)) : IsEssentiallyConstantInd M := by
  obtain ⟨t, i₀, b, hsec, hcond⟩ := h
  refine ⟨Functor.Final.extendCocone.obj t, H.obj i₀, b, ?_, fun d => ?_⟩
  · rw [Functor.Final.extendCocone_obj_ι_app' t (𝟙 (H.obj i₀)), M.map_id, Category.id_comp]
    exact hsec
  obtain ⟨k, v, u, huv⟩ := hcond (Functor.Final.lift H d)
  refine ⟨H.obj k, H.map v, Functor.Final.homToLift H d ≫ H.map u, ?_⟩
  rw [M.map_comp, Functor.Final.extendCocone_obj_ι_app' t (Functor.Final.homToLift H d)]
  rw [show M.map (H.map u) = t.ι.app (Functor.Final.lift H d) ≫ b ≫ M.map (H.map v) from huv]
  exact (Category.assoc _ _ _).symm

/-- Stacks Tag 0A1S, Lemma 4.22.11. Let `H : I ⥤ J` be a cofinal (= `Final`)
functor between filtered categories `I` and `J`, and `M : J ⥤ C` a diagram. Then
`M` is essentially constant iff `M ∘ H` (written `H ⋙ M`) is essentially
constant. -/
@[stacks 0A1S]
theorem essentiallyConstant_iff_comp_final
    {C : Type*} [Category C] {I : Type*} [Category I] {J : Type*} [Category J]
    [IsFiltered I] [IsFiltered J] (H : I ⥤ J) [H.Final] (M : J ⥤ C) :
    IsEssentiallyConstantInd M ↔ IsEssentiallyConstantInd (H ⋙ M) :=
  ⟨essentiallyConstant_comp_final_of H M, essentiallyConstant_of_comp_final H M⟩
