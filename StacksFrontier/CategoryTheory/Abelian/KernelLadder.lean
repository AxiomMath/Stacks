module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Two kernels of isomorphic maps are isomorphic

Let `C` be a category with zero morphisms and let

```
A  --i-->  B  --g-->  D
|          |          |
φ          β          γ
|          |          |
A' --i'--> B' --g'--> D'
```

be a diagram in which `i` is a kernel of `g`, `i'` is a kernel of `g'`, the two right-hand
vertical maps are isomorphisms and both squares commute. **Then `φ` is an isomorphism.**

The inverse is the morphism `A' ⟶ A` that `i' ≫ β⁻¹` factors through the kernel `i` by, and the
two composites are the identity because `i` and `i'` are monomorphisms.

No limit is constructed and no element is chased: the hypotheses are the two universal
properties and the two commuting squares, which is the form a comparison of two exact sequences
supplies them in.

## Main results

* `CategoryTheory.isIso_of_isKernel_of_isKernel`: **the comparison of two kernels of isomorphic
  maps is an isomorphism.**
* `CategoryTheory.ShortComplex.isIso_of_exact_ladder`: the same for two exact short complexes
  with monomorphic first map, which is how an exact sequence presents its first term as a kernel.
* `CategoryTheory.isLimit_kernelFork_of_split`: **a split pair is a kernel** — if `f ≫ r = 1` and
  `r ≫ f + g ≫ t = 1` then `f` is a kernel of `g`, with no exactness hypothesis of any kind.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [Limits.HasZeroMorphisms C]

/-- **The comparison of two kernels of isomorphic maps is an isomorphism.** If `i` is a kernel of
`g`, `i'` is a kernel of `g'`, the pairs `(g, g')` are identified by isomorphisms `β` and `γ` and
`φ` is compatible with `β`, then `φ` is invertible. -/
theorem isIso_of_isKernel_of_isKernel {A B D A' B' D' : C}
    {i : A ⟶ B} {g : B ⟶ D} {w : i ≫ g = 0} (hi : IsLimit (KernelFork.ofι i w))
    {i' : A' ⟶ B'} {g' : B' ⟶ D'} {w' : i' ≫ g' = 0} (hi' : IsLimit (KernelFork.ofι i' w'))
    (β : B ≅ B') (γ : D ≅ D') (hsq : g ≫ γ.hom = β.hom ≫ g')
    (φ : A ⟶ A') (hφ : φ ≫ i' = i ≫ β.hom) : IsIso φ := by
  have hmono : Mono i := mono_of_isLimit_fork hi
  have hmono' : Mono i' := mono_of_isLimit_fork hi'
  have hsq' : β.inv ≫ g = g' ≫ γ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hsq
  have w2 : (i' ≫ β.inv) ≫ g = 0 := by
    rw [Category.assoc, hsq', ← Category.assoc, w', zero_comp]
  have hψ : hi.lift (KernelFork.ofι (i' ≫ β.inv) w2) ≫ i = i' ≫ β.inv :=
    Fork.IsLimit.lift_ι hi
  refine ⟨hi.lift (KernelFork.ofι (i' ≫ β.inv) w2), ?_, ?_⟩
  · rw [← cancel_mono i, Category.assoc, hψ, ← Category.assoc, hφ, Category.assoc,
      β.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono i', Category.assoc, hφ, ← Category.assoc, hψ, Category.assoc,
      β.inv_hom_id, Category.comp_id, Category.id_comp]

end HasZeroMorphisms

section Preadditive

variable [Preadditive C]

/-- **A split pair is a kernel.** If `f : X ⟶ Y` and `g : Y ⟶ Z` compose to zero and there are
`r : Y ⟶ X` and `t : Z ⟶ Y` with

`f ≫ r = 1`  and  `r ≫ f + g ≫ t = 1`,

then `f` is a kernel of `g`: a morphism `x` killed by `g` factors as `(x ≫ r) ≫ f`, because
`x ≫ (r ≫ f) = x - (x ≫ g) ≫ t = x`, and the factorisation is unique because `f ≫ r = 1` makes
`f` a split monomorphism. -/
def isLimit_kernelFork_of_split {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : f ≫ g = 0) (r : Y ⟶ X) (t : Z ⟶ Y) (hr : f ≫ r = 𝟙 X)
    (ht : r ≫ f + g ≫ t = 𝟙 Y) : IsLimit (KernelFork.ofι f w) := by
  have hrf : r ≫ f = 𝟙 Y - g ≫ t := by rw [eq_sub_iff_add_eq]; exact ht
  refine Fork.IsLimit.mk _ (fun s => Fork.ι s ≫ r) (fun s => ?_) (fun s l hl => ?_)
  · change (Fork.ι s ≫ r) ≫ f = Fork.ι s
    rw [Category.assoc, hrf, Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      KernelFork.condition s, Limits.zero_comp, sub_zero]
  · change l = Fork.ι s ≫ r
    rw [← hl]
    change l = (l ≫ f) ≫ r
    rw [Category.assoc, hr]
    simp

end Preadditive

namespace ShortComplex

variable [Abelian C]

/-- **Two exact short complexes with monomorphic first map and isomorphic last two terms have
isomorphic first terms.** An exact short complex whose first map is a monomorphism presents its
first term as a kernel of its second map, so this is
`CategoryTheory.isIso_of_isKernel_of_isKernel`. -/
theorem isIso_of_exact_ladder {S S' : ShortComplex C} (hS : S.Exact) (hS' : S'.Exact)
    [Mono S.f] [Mono S'.f] (β : S.X₂ ≅ S'.X₂) (γ : S.X₃ ≅ S'.X₃)
    (hsq : S.g ≫ γ.hom = β.hom ≫ S'.g) (φ : S.X₁ ⟶ S'.X₁)
    (hφ : φ ≫ S'.f = S.f ≫ β.hom) : IsIso φ := by
  have h : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
  have h' : IsLimit (KernelFork.ofι S'.f S'.zero) := hS'.fIsKernel
  exact isIso_of_isKernel_of_isKernel h h' β γ hsq φ hφ

end ShortComplex

end CategoryTheory

end
