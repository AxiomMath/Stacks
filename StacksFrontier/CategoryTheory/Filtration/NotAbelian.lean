module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import StacksCore.CategoryTheory.Filtration.Strict
import StacksCore.Tactic.StacksAttribute

/-!
# Filtered vector spaces do not form an abelian category

Stacks 0122 (4): the category `Fil(𝒜)` of filtered objects of an abelian category `𝒜` is in
general not abelian. Following Stacks 0108, let `k` be a field and take `V = W = k` with the
decreasing `ℤ`-filtrations
`F^nV = V` for `n < 0`, `F^nV = 0` for `n ≥ 0`, and `F^nW = W` for `n ≤ 0`, `F^nW = 0` for `n > 0`.
The identity of `k` is a morphism of filtered objects `f : V ⟶ W`. It is a monomorphism and an
epimorphism of `Fil(Mod_k)`, and it is not strict (Stacks 0123): `f(F^0V) = 0` while
`f(V) ∩ F^0W = k`. Hence

* `FilteredObject.not_isIso_coimageImageComparison_negToNonpos`: the canonical morphism
  `Coim(f) ⟶ Im(f)` of `Fil(Mod_k)` is not an isomorphism (Stacks 05SI), so the defining
  condition of an abelian category (Stacks 0109) fails for the additive structure of Stacks 0122
  (1), (3);
* `FilteredObject.isEmpty_abelian_moduleCat`: there is no abelian category structure at all on
  `Fil(Mod_k)` (with any preadditive structure), since `f` is a monomorphism and an epimorphism
  that is not an isomorphism, while abelian categories are balanced.

The index category is `ℤᵒᵖ`, the convention for Stacks' decreasing `ℤ`-filtrations in
`StacksCore.CategoryTheory.Filtration.Basic`.
-/

@[expose] public section

universe u

namespace CategoryTheory.FilteredObject

open Opposite Limits

variable (k : Type u) [Field k]

/-- The steps `F^nV = V` for `n < 0` and `F^nV = 0` for `n ≥ 0` of the filtration of Stacks 0108
on `V = k`. -/
noncomputable def negSubobject (n : ℤ) : Subobject (ModuleCat.of k k) :=
  if n < 0 then ⊤ else ⊥

/-- The steps `F^nW = W` for `n ≤ 0` and `F^nW = 0` for `n > 0` of the filtration of Stacks 0108
on `W = k`. -/
noncomputable def nonposSubobject (n : ℤ) : Subobject (ModuleCat.of k k) :=
  if n ≤ 0 then ⊤ else ⊥

/-- The steps `negSubobject k n` decrease in `n`. -/
lemma antitone_negSubobject : Antitone (negSubobject k) := by
  intro m n h
  by_cases hn : n < 0
  · simp [negSubobject, hn, show m < 0 by omega]
  · simp [negSubobject, hn]

/-- The steps `nonposSubobject k n` decrease in `n`. -/
lemma antitone_nonposSubobject : Antitone (nonposSubobject k) := by
  intro m n h
  by_cases hn : n ≤ 0
  · simp [nonposSubobject, hn, show m ≤ 0 by omega]
  · simp [nonposSubobject, hn]

/-- `F^nV ⊆ F^nW` for all `n`, so the identity of `k` is a morphism of filtered objects. -/
lemma negSubobject_le_nonposSubobject (n : ℤ) : negSubobject k n ≤ nonposSubobject k n := by
  by_cases hn : n < 0
  · simp [negSubobject, nonposSubobject, hn, show n ≤ 0 by omega]
  · simp [negSubobject, hn]

/-- The filtered vector space `V = k` of Stacks 0108, with `F^nV = V` for `n < 0` and
`F^nV = 0` for `n ≥ 0`. -/
noncomputable abbrev negFiltered : FilteredObject (ModuleCat.{u} k) ℤᵒᵖ :=
  ⟨ModuleCat.of k k, Filtration.ofAntitone _ (antitone_negSubobject k)⟩

/-- The filtered vector space `W = k` of Stacks 0108, with `F^nW = W` for `n ≤ 0` and
`F^nW = 0` for `n > 0`. -/
noncomputable abbrev nonposFiltered : FilteredObject (ModuleCat.{u} k) ℤᵒᵖ :=
  ⟨ModuleCat.of k k, Filtration.ofAntitone _ (antitone_nonposSubobject k)⟩

/-- The `n`-th step of `V`, as a subobject, is `negSubobject k n`. -/
lemma negFiltered_subobject (n : ℤ) : (negFiltered k).subobject (op n) = negSubobject k n :=
  Filtration.subobject_ofAntitone _ (antitone_negSubobject k) n

/-- The `n`-th step of `W`, as a subobject, is `nonposSubobject k n`. -/
lemma nonposFiltered_subobject (n : ℤ) :
    (nonposFiltered k).subobject (op n) = nonposSubobject k n :=
  Filtration.subobject_ofAntitone _ (antitone_nonposSubobject k) n

/-- The inclusion of the `n`-th step of `V` is the arrow of `negSubobject k n`. -/
lemma negFiltered_ι_app (n : ℤ) :
    (negFiltered k).filtration.ι.app (op n) = (negSubobject k n).arrow :=
  rfl

/-- The morphism `f : V ⟶ W` of Stacks 0108, the identity of `k` on underlying vector spaces. -/
noncomputable def negToNonpos : negFiltered k ⟶ nonposFiltered k :=
  homMk' (𝟙 (ModuleCat.of k k)) fun i => by
    induction i with
    | op n =>
      rw [nonposFiltered_subobject, negFiltered_ι_app]
      exact Subobject.factors_of_le _ (negSubobject_le_nonposSubobject k n)
        (Subobject.factors_self _)

/-- The underlying morphism of `negToNonpos k` is the identity of `k`. -/
@[simp] lemma negToNonpos_hom : (negToNonpos k).hom = 𝟙 (ModuleCat.of k k) :=
  homMk'_hom _ _

/-- The vector space `k` has a proper subobject: `⊥ ≠ ⊤`. -/
private lemma bot_ne_top_subobject : (⊥ : Subobject (ModuleCat.of k k)) ≠ ⊤ := by
  intro h
  have := congrArg (ModuleCat.subobjectModule (ModuleCat.of k k)) h
  rw [OrderIso.map_bot, OrderIso.map_top] at this
  exact bot_ne_top this

/-- `F^0V = 0`. -/
lemma negSubobject_zero : negSubobject k 0 = ⊥ := by
  simp [negSubobject]

/-- `F^0W = W`. -/
lemma nonposSubobject_zero : nonposSubobject k 0 = ⊤ := by
  simp [nonposSubobject]

/-- The morphism `f : V ⟶ W` of Stacks 0108 is not strict: `f(F^0V) = 0` while
`f(V) ∩ F^0W = k`. -/
theorem not_isStrict_negToNonpos : ¬ IsStrict (negToNonpos k) := by
  have : Mono (negToNonpos k).hom := by rw [negToNonpos_hom]; infer_instance
  rw [isStrict_iff_isStrictHom_of_mono, isStrictHom_iff]
  intro h
  have h0 := h (op 0)
  rw [nonposFiltered_subobject, negFiltered_subobject, nonposSubobject_zero, negSubobject_zero,
    Subobject.pullback_top] at h0
  exact bot_ne_top_subobject k h0.symm

/-- The morphism `f : V ⟶ W` of Stacks 0108 is not an isomorphism of filtered objects. -/
theorem not_isIso_negToNonpos : ¬ IsIso (negToNonpos k) := fun _ =>
  not_isStrict_negToNonpos k inferInstance

/-- `negToNonpos k` is a monomorphism of filtered objects. -/
instance mono_negToNonpos : Mono (negToNonpos k) := by
  have : Mono (negToNonpos k).hom := by
    rw [negToNonpos_hom]; infer_instance
  exact mono_of_mono_hom _

/-- `negToNonpos k` is an epimorphism of filtered objects. -/
instance epi_negToNonpos : Epi (negToNonpos k) := by
  have : Epi (negToNonpos k).hom := by
    rw [negToNonpos_hom]; infer_instance
  exact epi_of_epi_hom _

/-- Stacks 0122 (4), in the form of Stacks 0108: for the morphism `f : V ⟶ W` of filtered vector
spaces over a field `k`, the canonical morphism `Coim(f) ⟶ Im(f)` of `Fil(Mod_k)` (with the
additive structure and the kernels and cokernels of Stacks 0122 (1), (3)) is not an isomorphism.
So `Fil(Mod_k)` fails the defining condition of an abelian category, Stacks 0109. -/
@[stacks 0122 "(4) `Coim(f) ⟶ Im(f)` is not an isomorphism in `Fil(Mod_k)`, Stacks 0108"]
theorem not_isIso_coimageImageComparison_negToNonpos :
    ¬ IsIso (Abelian.coimageImageComparison (negToNonpos k)) := fun h =>
  not_isStrict_negToNonpos k ((isStrict_iff_isIso_coimageImageComparison _).2 h)

/-- Stacks 0122 (4): the category `Fil(Mod_k)` of filtered vector spaces over a field `k` is not
abelian. There is no abelian category structure on it at all, for any preadditive structure:
the morphism `f : V ⟶ W` of Stacks 0108 is a monomorphism and an epimorphism but not an
isomorphism, and abelian categories are balanced. -/
@[stacks 0122 "(4) `Fil(Mod_k)` admits no abelian structure, for any field `k`"]
theorem isEmpty_abelian_moduleCat : IsEmpty (Abelian (FilteredObject (ModuleCat.{u} k) ℤᵒᵖ)) :=
  ⟨fun inst => by
    have : Balanced (FilteredObject (ModuleCat.{u} k) ℤᵒᵖ) :=
      @balanced_of_strongEpiCategory _ _ (@strongEpiCategory_of_regularEpiCategory _ _
        (@regularEpiCategoryOfNormalEpiCategory _ _
          (@Preadditive.preadditiveHasZeroMorphisms _ _ inst.toPreadditive)
          inst.toIsNormalEpiCategory))
    exact not_isIso_negToNonpos k (isIso_of_mono_of_epi _)⟩

end CategoryTheory.FilteredObject
