module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ShortExactVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The connecting homomorphism of a short exact sequence of abelian sheaves

Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on a site. Composing
with its extension class gives, in each pair of consecutive degrees `n₀ + 1 = n₁`, the
connecting homomorphism

```
∂ : H^{n₀}(F₃) ⟶ H^{n₁}(F₁)
```

of the long exact sequence of sheaf cohomology, and the two exactness statements around it:

```
H^{n₀}(F₂) --g--> H^{n₀}(F₃) --∂--> H^{n₁}(F₁) --f--> H^{n₁}(F₂).
```

## Main definitions

* `Stacks.Cohomology.sheafHBoundary`: the connecting homomorphism `H^{n₀}(F₃) ⟶ H^{n₁}(F₁)`.

## Main results

* `Stacks.Cohomology.sheafHBoundary_eq_zero_iff`: its kernel is the image of `H^{n₀}(F₂)`.
* `Stacks.Cohomology.exists_sheafHBoundary_iff`: its image is the kernel of
  `H^{n₁}(F₁) ⟶ H^{n₁}(F₂)`.
* `Stacks.Cohomology.surjective_sheafHBoundary_of_subsingleton`: it is onto when `H^{n₁}(F₂)`
  vanishes.

## Implementation notes

Sheaf cohomology `CategoryTheory.Sheaf.H F n` is by definition
`Ext ((constantSheaf J AddCommGrpCat).obj (ULift ℤ)) F n`, and the map induced by a morphism of
sheaves is post-composition with `CategoryTheory.Abelian.Ext.mk₀` of it. So the connecting
homomorphism is literally `CategoryTheory.Abelian.Ext.comp` with
`CategoryTheory.ShortComplex.ShortExact.extClass`, additive by
`CategoryTheory.Abelian.Ext.add_comp`, and the two exactness statements are Mathlib's
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁` and
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃` with no reindexing. The two composites
that vanish are `CategoryTheory.ShortComplex.ShortExact.comp_extClass` and
`CategoryTheory.ShortComplex.ShortExact.extClass_comp`.

The degrees `n₀` and `n₁` are separate arguments related by `n₀ + 1 = n₁`, rather than `n₀` and
`n₀ + 1`, as in `Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w' w v u

namespace Stacks.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- **The connecting homomorphism `H^{n₀}(F₃) ⟶ H^{n₁}(F₁)`** of a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of abelian sheaves, where `n₀ + 1 = n₁`: composition with the extension
class of the sequence. -/
@[sga "4½ Sommes_trig 1.3" "Connecting map ∂"]
def sheafHBoundary (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w', w} S.X₃ n₀ →+ Sheaf.H.{w', w} S.X₁ n₁ where
  toFun x := x.comp hS.extClass h
  map_zero' := Ext.zero_comp ..
  map_add' _ _ := Ext.add_comp ..

/-- The connecting homomorphism sends `x` to its composite with the extension class. -/
@[simp] theorem sheafHBoundary_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w', w} S.X₃ n₀) :
    sheafHBoundary hS n₀ n₁ h x = x.comp hS.extClass h :=
  rfl

/-- **A boundary dies in the middle sheaf**: two consecutive maps of the long exact sequence
compose to zero. -/
theorem map_f_sheafHBoundary (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w', w} S.X₃ n₀) :
    Sheaf.H.map S.f n₁ (sheafHBoundary hS n₀ n₁ h x) = 0 := by
  rw [Sheaf.H.map_apply]
  show (x.comp hS.extClass h).comp (Ext.mk₀ S.f) (add_zero n₁) = 0
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

/-- **A class coming from the middle sheaf has zero boundary**, the other composite of two
consecutive maps of the long exact sequence. -/
theorem sheafHBoundary_map_g (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w', w} S.X₂ n₀) :
    sheafHBoundary hS n₀ n₁ h (Sheaf.H.map S.g n₀ x) = 0 := by
  show (Sheaf.H.map S.g n₀ x).comp hS.extClass h = 0
  rw [Sheaf.H.map_apply]
  show (x.comp (Ext.mk₀ S.g) (add_zero n₀)).comp hS.extClass h = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- **The kernel of the connecting homomorphism is the image of `H^{n₀}(F₂)`**: exactness of the
long exact sequence of sheaf cohomology at `H^{n₀}(F₃)`. -/
@[sga "4½ Arcata 1.6.5" "more general", sga "4½ Sommes_trig 1.3" "Exactness of Hom(X"]
theorem sheafHBoundary_eq_zero_iff (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w', w} S.X₃ n₀) :
    sheafHBoundary hS n₀ n₁ h x = 0 ↔ ∃ y, Sheaf.H.map.{w', w} S.g n₀ y = x := by
  refine ⟨fun hx => Ext.covariant_sequence_exact₃ _ hS x h hx, ?_⟩
  rintro ⟨y, rfl⟩
  exact sheafHBoundary_map_g hS n₀ n₁ h y

/-- **The image of the connecting homomorphism is the kernel of `H^{n₁}(F₁) ⟶ H^{n₁}(F₂)`**:
exactness of the long exact sequence of sheaf cohomology at `H^{n₁}(F₁)`. -/
@[sga "4½ Arcata 1.6.5" "partial"]
theorem exists_sheafHBoundary_iff (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w', w} S.X₁ n₁) :
    (∃ y, sheafHBoundary hS n₀ n₁ h y = x) ↔ Sheaf.H.map.{w', w} S.f n₁ x = 0 := by
  refine ⟨?_, fun hx => Ext.covariant_sequence_exact₁ _ hS x hx h⟩
  rintro ⟨y, rfl⟩
  exact map_f_sheafHBoundary hS n₀ n₁ h y

/-- **The connecting homomorphism is surjective when `H^{n₁}(F₂)` vanishes**, so that
`H^{n₁}(F₁)` is then the cokernel of `H^{n₀}(F₂) ⟶ H^{n₀}(F₃)`. -/
theorem surjective_sheafHBoundary_of_subsingleton (hS : S.ShortExact) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) (h₂ : Subsingleton (Sheaf.H.{w', w} S.X₂ n₁)) :
    Function.Surjective (sheafHBoundary hS n₀ n₁ h) :=
  fun x => (exists_sheafHBoundary_iff hS n₀ n₁ h x).2 (h₂.elim _ _)

end Stacks.Cohomology

end
