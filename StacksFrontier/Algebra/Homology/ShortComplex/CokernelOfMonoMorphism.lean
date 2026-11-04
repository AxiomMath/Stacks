module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# The cokernels of a morphism of short exact sequences form a short exact sequence

Let

```
Y₁  ⟶  Y₂  ⟶  Y₃
|      |      |
α      β      γ
v      v      v
T.X₁ ⟶ T.X₂ ⟶ T.X₃
```

be a commutative ladder in an abelian category, with both rows short exact and `γ` a
monomorphism. Then the induced short complex on the cokernels of the vertical maps,
`Stacks.CategoryTheory.ShortComplex.cokernelShortComplex`, is **short exact**.

This is the half of [Stacks, Tag 010H] that the proof of [Stacks, Tag 08AG] consumes: there the
rows are a short exact sequence of coherent sheaves twisted by `d` and by `d + 1`, the vertical
maps are multiplication by a global section of `𝒪(1)` cutting out a hyperplane, and the
cokernels are the restrictions of the three sheaves to that hyperplane. Monicity of `γ` is the
only geometric input — it says the section does not vanish at an associated point of the third
term — and is what makes the restricted sequence short exact.

## Main results

* `CategoryTheory.ShortComplex.mono_cokernel_map_of_exact`: **the first map of the cokernel
  sequence is a monomorphism.** This is the one assertion that needs the connecting morphism of
  the snake lemma, and it is proved here directly by refinements.
* `CategoryTheory.ShortComplex.epi_cokernel_map_of_epi`: the second map is an epimorphism.
* `CategoryTheory.ShortComplex.shortExact_cokernelShortComplex`: the cokernel sequence is short
  exact.

## The mathematics

Exactness in the middle is already available as
`CategoryTheory.ShortComplex.Exact.exact_cokernelShortComplex`, clause (1) of
[Stacks, Tag 08N6] read in the opposite category, and needs only exactness of the bottom row and
that the top row's second map be an epimorphism. Surjectivity of the second cokernel map is
formal: it is an epimorphism after composition with the epimorphism `cokernel.π β`, because the
square it sits in has `T.g` and a cokernel projection on the other two sides.

Monicity of the first cokernel map is the content. In the snake lemma it is the vanishing of the
connecting morphism out of `ker γ`, and with `γ` a monomorphism that kernel is zero. The proof
below avoids constructing a `CategoryTheory.ShortComplex.SnakeInput` and argues by refinements
(`CategoryTheory.Abelian.Refinements`): a morphism into `cokernel α` killed by the first
cokernel map lifts to `T.X₁` after a refinement; its image under `T.f` is killed by
`cokernel.π β`, hence comes from `Y₂` after a further refinement; that class is killed by the
top row's second map because `γ` is a monomorphism, hence comes from `Y₁` by exactness of the
top row; and comparing the two expressions through the monomorphism `T.f` shows the original
morphism factors through `α`, so it was zero in `cokernel α` all along.

## References

* [Stacks Project, Tag 010H](https://stacks.math.columbia.edu/tag/010H)
* [Stacks Project, Tag 08N6](https://stacks.math.columbia.edu/tag/08N6)
* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

variable (T : ShortComplex C) {Y₁ Y₂ Y₃ : C} {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃}
  {α : Y₁ ⟶ T.X₁} {β : Y₂ ⟶ T.X₂} {γ : Y₃ ⟶ T.X₃}
  (comm₁ : α ≫ T.f = f ≫ β) (comm₂ : β ≫ T.g = g ≫ γ)

/-- **The first map of the cokernel sequence of a ladder with monic right-hand column is a
monomorphism.**

The hypotheses are: the top row `Y₁ ⟶ Y₂ ⟶ Y₃` is a complex and is exact, the bottom row's first
map `T.f` is a monomorphism, the bottom row is a complex, and the right-hand vertical `γ` is a
monomorphism. In the snake lemma this is the exactness of
`ker γ ⟶ cokernel α ⟶ cokernel β` together with `ker γ = 0`. -/
theorem mono_cokernel_map_of_exact (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono T.f] [Mono γ] (hcomm₂ : β ≫ T.g = g ≫ γ) :
    Mono (cokernel.map α β f T.f comm₁) := by
  have hπα : cokernel.π α ≫ cokernel.map α β f T.f comm₁ = T.f ≫ cokernel.π β :=
    cokernel.π_desc _ _ _
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  obtain ⟨A₁, π₁, hπ₁, x', hx'⟩ := surjective_up_to_refinements_of_epi (cokernel.π α) x
  have hstep : (x' ≫ T.f) ≫ cokernel.π β = 0 := by
    rw [Category.assoc, ← hπα, ← reassoc_of% hx', hx, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, (y : A₂ ⟶ Y₂), (hy : π₂ ≫ x' ≫ T.f = y ≫ β)⟩ :=
    (cokernelSequence_exact β).exact_up_to_refinements (x' ≫ T.f) hstep
  have hyg : y ≫ g = 0 := zero_of_comp_mono γ (by
    rw [Category.assoc, ← hcomm₂, ← reassoc_of% hy]
    simp)
  obtain ⟨A₃, π₃, hπ₃, (z : A₃ ⟶ Y₁), (hz : π₃ ≫ y = z ≫ f)⟩ := hS.exact_up_to_refinements y hyg
  have hzα : z ≫ α = π₃ ≫ π₂ ≫ x' := by
    refine (cancel_mono T.f).mp ?_
    simp only [Category.assoc]
    rw [comm₁, ← reassoc_of% hz, ← hy]
  have hfin : (π₃ ≫ π₂ ≫ π₁) ≫ x = 0 := by
    simp only [Category.assoc]
    rw [hx', ← reassoc_of% hzα]
    simp
  exact zero_of_epi_comp _ hfin

/-- **The second map of the cokernel sequence is an epimorphism**, as soon as the bottom row's
second map is: the square it sits in has `T.g` and a cokernel projection on the other two
sides, both epimorphisms. -/
theorem epi_cokernel_map_of_epi [Epi T.g] : Epi (cokernel.map β γ g T.g comm₂) := by
  have h : cokernel.π β ≫ cokernel.map β γ g T.g comm₂ = T.g ≫ cokernel.π γ :=
    cokernel.π_desc _ _ _
  exact epi_of_epi_fac (f := cokernel.π β) h

/-- **The cokernels of a morphism of short exact sequences, with monic right-hand column, form a
short exact sequence.** This is the shape of [Stacks, Tag 010H] that the hyperplane restriction
of a short exact sequence of coherent sheaves needs.

The three assertions are `CategoryTheory.ShortComplex.mono_cokernel_map_of_exact`,
`CategoryTheory.ShortComplex.Exact.exact_cokernelShortComplex` and
`CategoryTheory.ShortComplex.epi_cokernel_map_of_epi`. -/
theorem shortExact_cokernelShortComplex (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact) (hT : T.ShortExact) [Mono γ] :
    (T.cokernelShortComplex comm₁ comm₂).ShortExact :=
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  { exact := hT.exact.exact_cokernelShortComplex comm₁ comm₂
    mono_f := mono_cokernel_map_of_exact T comm₁ hfg hS.exact comm₂
    epi_g := epi_cokernel_map_of_epi T comm₂ }

end CategoryTheory.ShortComplex

end
