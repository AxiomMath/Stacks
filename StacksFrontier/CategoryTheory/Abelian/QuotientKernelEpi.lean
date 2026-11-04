module

public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The kernel of a map of quotients, when the subobjects are surjected onto

Let `C` be an abelian category and let

```
P  --u-->  X  --p-->  X'
|          |          |
v          a          a'
|          |          |
P' --u'--> Y  --p'--> Y'
```

be a diagram in which the two rows present `X'` and `Y'` as quotients of `X` and `Y` by the
subobjects `P` and `P'`, the middle square commutes, `p` is surjective and the image of `P` in
`Y` already contains `P'`.  **The induced morphism `ker a ⟶ ker a'` is then surjective.**

This is exactness of the snake sequence at `ker a'`, in the only case needed when the left-hand
vertical map is surjective: the connecting map lands in `coker` of that map, which vanishes.  It
is proved here by the refinement calculus of `CategoryTheory.Abelian.Refinements` rather than by
assembling a `CategoryTheory.ShortComplex.SnakeInput`, so that the hypotheses are exactly the
five arrows above together with the two conditions `u ≫ p = 0` and
`u' ≫ CategoryTheory.Limits.cokernel.π (u ≫ a) = 0`; the latter is the containment of `P'` in the
image of `P`, in the form in which quotients by a sheaf of ideals supply it.

The row through `X` is only used through `u ≫ p = 0` and surjectivity of `p`; the row through `Y`
is used through its exactness, so it is asked for as a
`CategoryTheory.ShortComplex.Exact` hypothesis.

Two companion statements about the kernel of a cokernel projection are proved here as well, by
the same calculus: a morphism which becomes the projection onto a cokernel after composition with
an isomorphism presents an exact pair, and the canonical morphism onto the kernel of the second
map of an exact pair is surjective.

## Main results

* `CategoryTheory.Abelian.epi_kernelLift_of_exact_of_epi` — **the induced morphism on kernels is
  an epimorphism.**
* `CategoryTheory.Abelian.exact_of_comp_iso_eq_cokernel_π` — a cokernel projection recognised up
  to an isomorphism of its target presents an exact pair.
* `CategoryTheory.Abelian.epi_kernelLift_of_exact` — **the canonical morphism onto the kernel of
  the second map of an exact pair is an epimorphism.**
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Preadditive

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The composite `ker a ⟶ X ⟶ X'` is annihilated by `a'`, so it factors through `ker a'`. -/
theorem kernel_ι_comp_comp_eq_zero {X Y X' Y' : C} (a : X ⟶ Y) (a' : X' ⟶ Y') (p : X ⟶ X')
    (p' : Y ⟶ Y') (hsq : p ≫ a' = a ≫ p') :
    (kernel.ι a ≫ p) ≫ a' = 0 := by
  rw [Category.assoc, hsq, ← Category.assoc, kernel.condition, zero_comp]

/-- **The induced morphism on kernels is an epimorphism.**

Given a commutative square `p ≫ a' = a ≫ p'` with `p` an epimorphism, a subobject `u : P ⟶ X`
killed by `p`, and a presentation of `p'` as a cokernel of `u' : P' ⟶ Y` in the exactness form,
the morphism `ker a ⟶ ker a'` induced by `p` is an epimorphism as soon as `P'` is contained in
the image of `u ≫ a`.

The chase: a refinement of an element of `ker a'` lifts to `X` along `p`; its image under `a`
dies in `Y'`, so a further refinement comes from `P'`, and a further one from `P` by the
containment hypothesis; subtracting its image under `u` corrects the lift to one which `a`
annihilates, without changing its image in `X'`, since `u ≫ p = 0`. -/
theorem epi_kernelLift_of_exact_of_epi {P P' X Y X' Y' : C} (u : P ⟶ X) (u' : P' ⟶ Y)
    (a : X ⟶ Y) (a' : X' ⟶ Y') (p : X ⟶ X') (p' : Y ⟶ Y') [Epi p]
    (hsq : p ≫ a' = a ≫ p') (hup : u ≫ p = 0) (hzero : u' ≫ p' = 0)
    (hex : (ShortComplex.mk u' p' hzero).Exact)
    (hu' : u' ≫ cokernel.π (u ≫ a) = 0) :
    Epi (kernel.lift a' (kernel.ι a ≫ p)
      (kernel_ι_comp_comp_eq_zero a a' p p' hsq)) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A g
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi p (g ≫ kernel.ι a')
  have h1 : (y ≫ a) ≫ p' = 0 := by
    rw [Category.assoc, ← hsq, ← Category.assoc, ← hy, Category.assoc, Category.assoc,
      kernel.condition, comp_zero, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, z, hz⟩ := hex.exact_up_to_refinements (y ≫ a) h1
  have hSg : (ShortComplex.mk (u ≫ a) (cokernel.π (u ≫ a)) (cokernel.condition _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  obtain ⟨A₃, π₃, hπ₃, t, ht⟩ :=
    hSg.exact_up_to_refinements (z ≫ u') (by rw [Category.assoc, hu', comp_zero])
  have hz' : π₂ ≫ y ≫ a = z ≫ u' := hz
  have ht' : π₃ ≫ z ≫ u' = t ≫ u ≫ a := ht
  have hx : ((π₃ ≫ π₂ ≫ y) - t ≫ u) ≫ a = 0 := by
    rw [sub_comp, Category.assoc, Category.assoc, Category.assoc, hz', ← ht', sub_self]
  refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, kernel.lift a _ hx, ?_⟩
  refine (cancel_mono (kernel.ι a')).mp ?_
  simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, sub_comp, hup, comp_zero,
    sub_zero, hy]

/-! ### The kernel of a cokernel projection -/

/-- **A morphism which becomes the projection onto the cokernel after composition with an
isomorphism presents an exact pair.** -/
theorem exact_of_comp_iso_eq_cokernel_π {X Y Z : C} (a : X ⟶ Y) (p : Y ⟶ Z)
    (e : Z ≅ cokernel a) (he : p ≫ e.hom = cokernel.π a) (w : a ≫ p = 0) :
    (ShortComplex.mk a p w).Exact := by
  refine ShortComplex.exact_of_g_is_cokernel _ (IsColimit.ofIsoColimit (cokernelIsCokernel a)
    (Cofork.ext e.symm ?_))
  change cokernel.π a ≫ e.inv = p
  rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **The canonical morphism to the kernel of a cokernel projection is an epimorphism.**  A
refinement of an element of `ker p` comes from `X` by exactness, and the refinement itself is the
required lift. -/
theorem epi_kernelLift_of_exact {X Y Z : C} {a : X ⟶ Y} {p : Y ⟶ Z} (w : a ≫ p = 0)
    (hex : (ShortComplex.mk a p w).Exact) : Epi (kernel.lift p a w) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A g
  obtain ⟨A', π, hπ, x, hx⟩ := hex.exact_up_to_refinements (g ≫ kernel.ι p)
    (by rw [Category.assoc, kernel.condition, comp_zero])
  refine ⟨A', π, hπ, x, ?_⟩
  refine (cancel_mono (kernel.ι p)).mp ?_
  rw [Category.assoc, Category.assoc, kernel.lift_ι]
  exact hx

end CategoryTheory.Abelian

end
