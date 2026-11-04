module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Lifting a complex into a kernel, and naturality of the lift

Consider a commutative diagram in a category with zero morphisms

```text
  A  --f-->  B  --g-->  Z
             |          |
             β          γ
             v          v
  A' --f'--> B' --g'--> C'
```

whose top row is a complex (`f ≫ g = 0`), whose right-hand square commutes, and whose bottom
row exhibits `A'` as the kernel of `g'`. Then the composite `f ≫ β` kills `g'`, so the
universal property of the kernel produces a unique dotted arrow `A ⟶ A'` making the left-hand
square commute. The lift is natural: a morphism between two such diagrams induces a morphism
between the lifts, and in particular the lifts of a diagram of functors assemble into a natural
transformation.

## Main results

* `CategoryTheory.Limits.kernelForkLift`: the lift `A ⟶ A'`, for `A'` the vertex of a limit
  kernel fork of `g'`.
* `CategoryTheory.Limits.existsUnique_comp_ι_eq`: it is the unique morphism making the
  left-hand square commute.
* `CategoryTheory.Limits.kernelForkLift_naturality`: a morphism of diagrams commutes with the
  lifts.
* `CategoryTheory.Limits.natTransKernelForkLift`: the lift of a diagram of functors, as a
  natural transformation `A ⟶ A'`.

## Implementation notes

For a bottom row literally of the form `kernel g' ⟶ B' ⟶ C'` the lift is Mathlib's
`CategoryTheory.Limits.kernel.lift` and its naturality along `kernel.map` is
`CategoryTheory.Limits.kernel.lift_map`; the point here is to allow `A'` to be an arbitrary
object with the kernel property, and the comparison morphism of kernels to be an arbitrary
morphism compatible with the inclusions.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u v₂ u₂

namespace NatTrans

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {D : Type u₂} [Category.{v₂} D]

/-- A composable pair of natural transformations whose composite vanishes has composite zero at
every object. -/
public theorem app_comp_app_eq_zero {A B Z : D ⥤ C} {f : A ⟶ B} {g : B ⟶ Z} (h : f ≫ g = 0)
    (X : D) : f.app X ≫ g.app X = 0 := by
  rw [← NatTrans.comp_app, h, zero_app]

omit [HasZeroMorphisms C] in
/-- A commuting square of natural transformations commutes at every object. -/
public theorem app_comp_app_eq {B Z B' C' : D ⥤ C} {g : B ⟶ Z} {γ : Z ⟶ C'} {β : B ⟶ B'}
    {g' : B' ⟶ C'} (h : g ≫ γ = β ≫ g') (X : D) :
    g.app X ≫ γ.app X = β.app X ≫ g'.app X := by
  rw [← NatTrans.comp_app, h, NatTrans.comp_app]

end NatTrans

namespace Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section

variable {A B Z B' C' : C} {g' : B' ⟶ C'} {f : A ⟶ B} {g : B ⟶ Z}
  {β : B ⟶ B'} {γ : Z ⟶ C'}

/-- If `f ≫ g = 0` and the square `g ≫ γ = β ≫ g'` commutes, then `f ≫ β` lands in the kernel
of `g'`. -/
public theorem comp_comp_eq_zero_of_square (hfg : f ≫ g = 0) (hsq : g ≫ γ = β ≫ g') :
    (f ≫ β) ≫ g' = 0 := by
  rw [Category.assoc, ← hsq, ← Category.assoc, hfg, zero_comp]

variable {c : KernelFork g'}

/-- The dotted arrow into a kernel: given a complex `f ≫ g = 0`, a limit kernel fork `c` of
`g'`, and a commuting square `g ≫ γ = β ≫ g'`, the morphism `f ≫ β` factors through `c`. -/
public def kernelForkLift (hc : IsLimit c) (hfg : f ≫ g = 0) (hsq : g ≫ γ = β ≫ g') :
    A ⟶ c.pt :=
  (KernelFork.IsLimit.lift' hc (f ≫ β) (comp_comp_eq_zero_of_square hfg hsq)).1

/-- The lift into a kernel makes the left-hand square of the diagram commute. -/
@[reassoc (attr := simp)]
public theorem kernelForkLift_comp_ι (hc : IsLimit c) (hfg : f ≫ g = 0)
    (hsq : g ≫ γ = β ≫ g') : kernelForkLift hc hfg hsq ≫ Fork.ι c = f ≫ β :=
  (KernelFork.IsLimit.lift' hc (f ≫ β) (comp_comp_eq_zero_of_square hfg hsq)).2

/-- The lift into a kernel is the only morphism making the left-hand square commute. -/
public theorem eq_kernelForkLift (hc : IsLimit c) (hfg : f ≫ g = 0) (hsq : g ≫ γ = β ≫ g')
    (t : A ⟶ c.pt) (ht : t ≫ Fork.ι c = f ≫ β) : t = kernelForkLift hc hfg hsq :=
  Fork.IsLimit.hom_ext hc (by rw [ht, kernelForkLift_comp_ι])

/-- There is a unique morphism `A ⟶ A'` making the left-hand square of the diagram commute. -/
public theorem existsUnique_comp_ι_eq (hc : IsLimit c) (hfg : f ≫ g = 0)
    (hsq : g ≫ γ = β ≫ g') : ∃! t : A ⟶ c.pt, t ≫ Fork.ι c = f ≫ β :=
  ⟨kernelForkLift hc hfg hsq, kernelForkLift_comp_ι hc hfg hsq,
    fun _ ht => eq_kernelForkLift hc hfg hsq _ ht⟩

end

section Naturality

variable {A₁ B₁ Z₁ B'₁ C'₁ A₂ B₂ Z₂ B'₂ C'₂ : C}
  {g'₁ : B'₁ ⟶ C'₁} {c₁ : KernelFork g'₁} {g'₂ : B'₂ ⟶ C'₂} {c₂ : KernelFork g'₂}
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ Z₁} {β₁ : B₁ ⟶ B'₁} {γ₁ : Z₁ ⟶ C'₁}
  {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ Z₂} {β₂ : B₂ ⟶ B'₂} {γ₂ : Z₂ ⟶ C'₂}

/-- A morphism between two such diagrams, given by `a` on the top left, `b` on the top middle,
`b'` on the bottom middle and `k` on the kernels, commutes with the lifts. -/
public theorem kernelForkLift_naturality (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂)
    (hfg₁ : f₁ ≫ g₁ = 0) (hsq₁ : g₁ ≫ γ₁ = β₁ ≫ g'₁)
    (hfg₂ : f₂ ≫ g₂ = 0) (hsq₂ : g₂ ≫ γ₂ = β₂ ≫ g'₂)
    {a : A₁ ⟶ A₂} {b : B₁ ⟶ B₂} {b' : B'₁ ⟶ B'₂} {k : c₁.pt ⟶ c₂.pt}
    (ha : f₁ ≫ b = a ≫ f₂) (hb : β₁ ≫ b' = b ≫ β₂) (hk : k ≫ Fork.ι c₂ = Fork.ι c₁ ≫ b') :
    kernelForkLift hc₁ hfg₁ hsq₁ ≫ k = a ≫ kernelForkLift hc₂ hfg₂ hsq₂ :=
  Fork.IsLimit.hom_ext hc₂ <| by
    rw [Category.assoc, hk, kernelForkLift_comp_ι_assoc, Category.assoc, hb,
      ← Category.assoc, ha, Category.assoc, kernelForkLift_comp_ι]

end Naturality

section Functorial

variable {D : Type u₂} [Category.{v₂} D] {A B Z A' B' C' : D ⥤ C}
  {f : A ⟶ B} {g : B ⟶ Z} {f' : A' ⟶ B'} {g' : B' ⟶ C'} {β : B ⟶ B'} {γ : Z ⟶ C'}
  (hfg : f ≫ g = 0) (hf'g' : f' ≫ g' = 0)
  (hc : ∀ X, IsLimit (KernelFork.ofι (f'.app X) (NatTrans.app_comp_app_eq_zero hf'g' X)))
  (hsq : g ≫ γ = β ≫ g')

/-- The dotted arrow for a diagram of functors, as a natural transformation: the objectwise
lifts into the kernels `A'.obj X` are natural in `X`. -/
public def natTransKernelForkLift : A ⟶ A' where
  app X := kernelForkLift (hc X) (NatTrans.app_comp_app_eq_zero hfg X)
    (β := β.app X) (γ := γ.app X) (NatTrans.app_comp_app_eq hsq X)
  naturality X Y u := by
    refine (kernelForkLift_naturality (hc X) (hc Y) _ _ _ _ (f.naturality u).symm
      (β.naturality u).symm ?_).symm
    simp

include hfg hsq in
/-- The natural transformation lifting a complex into a kernel makes the left-hand square of the
diagram of functors commute. -/
public theorem natTransKernelForkLift_comp :
    natTransKernelForkLift hfg hf'g' hc hsq ≫ f' = f ≫ β := by
  ext X
  exact kernelForkLift_comp_ι (hc X) (NatTrans.app_comp_app_eq_zero hfg X)
    (NatTrans.app_comp_app_eq hsq X)

include hfg hsq in
/-- It is the only natural transformation making that square commute. -/
public theorem eq_natTransKernelForkLift (t : A ⟶ A') (ht : t ≫ f' = f ≫ β) :
    t = natTransKernelForkLift hfg hf'g' hc hsq := by
  ext X
  refine Fork.IsLimit.hom_ext (hc X) ?_
  simpa using congrArg (fun s => s.app X)
    (ht.trans (natTransKernelForkLift_comp hfg hf'g' hc hsq).symm)

end Functorial

end Limits

end CategoryTheory
