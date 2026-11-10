module

public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Evaluation
import StacksFrontier.CategoryTheory.Monoidal.TensorInversePin

/-!
# The pin of a comparison of tensor inverses against the *left* trivialisations

`Stacks.TensorPowers.TensorInverse` carries two trivialisations of its inverse object: `mulIso`,
on `L ⊗ inv`, and `mulIso'`, on `inv ⊗ L`. A comparison `u : a⁻¹ ⟶ b⁻¹` of the inverse objects of
`a : TensorInverse L₁` and `b : TensorInverse L₂` can therefore be pinned along an isomorphism
`ε : L₁ ≅ L₂` in two inequivalent ways,

`u ▷ L₁ ≫ b⁻¹ ◁ ε ≫ b.mulIso' = a.mulIso'`    and    `(ε ⊗ₘ u) ≫ b.mulIso = a.mulIso`,

and `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineDetermination` develops
the
first. **This file develops the second**, which is the form the geometry of Tag 0B3V's base-change
clause actually arrives in; see "Why the left form" below.

## Main results

* `Stacks.TensorPowers.TensorInverse.invIso_whiskerLeft_mulIso`: **the left pin of the canonical
  comparison.** Whiskered on the left by `L` and followed by the left trivialisation of the target,
  `Stacks.TensorPowers.TensorInverse.invIso h k` is the left trivialisation of the source. Its one
  hypothesis is the snake identity of `h` — the mirror of
  `Stacks.TensorPowers.TensorInverse.invIso_whiskerRight_mulIso'`, whose snake is taken at `k`
  instead, and like it not a consequence of the monoidal axioms.
* `Stacks.TensorPowers.TensorInverse.tensorHom_comp_mulIso_ofIso`: the same read at
  `Stacks.TensorPowers.TensorInverse.ofIso`, which is the shape the comparisons of Tag 0B3V are
  built in: `(ε ⊗ₘ invIso a (ofIso ε b)) ≫ b.mulIso = a.mulIso`.
* `Stacks.Monoidal.tensorHom_comp_eq_comp`: **being pinned in the left form composes**, the two
  isomorphisms of the objects being inverted composing with it. One
  `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`; no inverse object is mentioned, so it
  holds for arbitrary pairings out of a tensor product.

## Why the left form

The left form is the one the three general facts a diagram of such comparisons needs are already
stated in, and the only one in which the geometric inputs of Tag 0B3V's inverse-line factor arrive:

* **Uniqueness** is `Stacks.Monoidal.eq_of_tensorHom_comp_eq`: two isomorphisms satisfying
  `(ε ⊗ₘ φ) ≫ hy = hx` agree, as soon as the object being inverted has a tensor inverse on the
  left. It consumes exactly the left form.
* **Composition** is `tensorHom_comp_eq_comp` below, one rewrite — against one
  `CategoryTheory.MonoidalCategory.whisker_exchange` for the right form.
* The twist factor of the base-change comparison,
  `Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso`, is
  `Stacks.Monoidal.isoOfTensorInverseBraided`, and the pin it comes with —
  `Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp`, through
  `Stacks.Monoidal.isoOfTensorInverseBraided_tensorHom_comp` — **is** the left pin, against the
  evaluation pairings `Stacks.ProjectiveBundleConormal.invertibleEvaluation` and
  `pullbackInvertibleEvaluation`, both of which pair `L` with `L^{⊗ -1}` in that order.
* Tag 01CD's comparison is natural in both module arguments at that same re-seated monoidal
  structure, by `Stacks.ProjectiveBundleConormal.pullbackTensorComparison_naturality_tensorHom`;
  so a left pin transports along a pullback with no further input.

What the left form lacked, and this file supplies, is the pin of `invIso` itself: the comparisons
`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` and
`Stacks.Divisors.inverseQuotientBaseChange` are `invIso` at a transported structure, and the only
pins `invIso` had were the triangle
`Stacks.TensorPowers.TensorInverse.invIso_hom_evaluation` and the right form built from it.

**No `@[stacks 0B3V]` attribute is attached, and none is earned**: nothing here mentions a scheme.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Being pinned by an evaluation pairing composes.** If `u` carries the pairing `hy` back to
`hx` along `ε` and `v` carries `hz` back to `hy` along `δ`, then `u ≫ v` carries `hz` back to `hx`
along `ε ≪≫ δ`.

One `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`: the tensor product of the two
composites is the composite of the two tensor products, after which the two hypotheses apply in
turn. Nothing is assumed of the pairings — they are bare morphisms out of a tensor product, not
trivialisations of a tensor inverse — so this is the composition law for the pin of
`Stacks.Monoidal.eq_of_tensorHom_comp_eq`, which is the uniqueness. -/
theorem tensorHom_comp_eq_comp {L₁ L₂ L₃ Y₁ Y₂ Y₃ : C} (ε : L₁ ≅ L₂) (δ : L₂ ≅ L₃)
    {u : Y₁ ⟶ Y₂} {v : Y₂ ⟶ Y₃} {hx : L₁ ⊗ Y₁ ⟶ 𝟙_ C} {hy : L₂ ⊗ Y₂ ⟶ 𝟙_ C}
    {hz : L₃ ⊗ Y₃ ⟶ 𝟙_ C} (hu : (ε.hom ⊗ₘ u) ≫ hy = hx) (hv : (δ.hom ⊗ₘ v) ≫ hz = hy) :
    ((ε ≪≫ δ).hom ⊗ₘ (u ≫ v)) ≫ hz = hx := by
  rw [Iso.trans_hom, ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, hv, hu]

end Stacks.Monoidal

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The comparison of two two-sided tensor inverses, in left single-tensor form.** Whiskered on
the left by `L` and followed by the left trivialisation `k.mulIso : L ⊗ k⁻¹ ≅ 𝟙` of the target, the
comparison `Stacks.TensorPowers.TensorInverse.invIso h k` is the left trivialisation
`h.mulIso : L ⊗ h⁻¹ ≅ 𝟙` of the source.

This is the mirror of `Stacks.TensorPowers.TensorInverse.invIso_whiskerRight_mulIso'`, and the
snake it needs is taken at the *source* `h`, not at the target: the definition of `invIso` contains
`k.mulIso` and `h.mulIso'`, so the right form must relate `k`'s two trivialisations and the left
form must relate `h`'s. The hypothesis `hsh` is that relation for `h`: the two ways of cancelling
the middle factor of `h⁻¹ ⊗ L ⊗ h⁻¹` — reassociate and contract the right pair by `h.mulIso`, or
contract the left pair by `h.mulIso'` — agree. It is not a consequence of the monoidal axioms; see
`Stacks.Monoidal.braiding_eval_snake`, where rescaling one trivialisation breaks it.

Taking `h = k` shows the hypothesis cannot be dropped: left whiskering by `L` is faithful, so the
conclusion then says `invIso h h` is the identity, which is the snake itself. The faithfulness is
`Stacks.Monoidal.whiskerLeft_injective_of_tensorInverse` at `h.mulIso`, and after it the whole
proof is the triangle `Stacks.TensorPowers.TensorInverse.invIso_hom_evaluation` together with the
naturality, in the factor being inverted, of contracting the left pair. -/
theorem TensorInverse.invIso_whiskerLeft_mulIso {L : C} (h k : TensorInverse L)
    (hsh : (α_ h.inv L h.inv).hom ≫ h.inv ◁ h.mulIso.hom ≫ (ρ_ h.inv).hom =
      h.mulIso'.hom ▷ h.inv ≫ (λ_ h.inv).hom) :
    L ◁ (TensorInverse.invIso h k).hom ≫ k.mulIso.hom = h.mulIso.hom := by
  refine Stacks.Monoidal.whiskerLeft_injective_of_tensorInverse h.mulIso ?_
  rw [MonoidalCategory.whiskerLeft_comp]
  refine (cancel_mono (ρ_ h.inv).hom).mp ?_
  refine (cancel_epi (α_ h.inv L h.inv).hom).mp ?_
  simp only [Category.assoc]
  rw [hsh]
  refine (cancel_mono (TensorInverse.invIso h k).hom).mp ?_
  calc ((α_ h.inv L h.inv).hom ≫ h.inv ◁ (L ◁ (TensorInverse.invIso h k).hom) ≫
          h.inv ◁ k.mulIso.hom ≫ (ρ_ h.inv).hom) ≫ (TensorInverse.invIso h k).hom
      = (h.inv ⊗ L) ◁ (TensorInverse.invIso h k).hom ≫
          (α_ h.inv L k.inv).hom ≫ h.inv ◁ k.mulIso.hom ≫ (ρ_ h.inv).hom ≫
            (TensorInverse.invIso h k).hom := by
        rw [← Category.assoc (α_ h.inv L h.inv).hom,
          ← MonoidalCategory.associator_naturality_right]
        simp only [Category.assoc]
    _ = (h.inv ⊗ L) ◁ (TensorInverse.invIso h k).hom ≫
          h.mulIso'.hom ▷ k.inv ≫ (λ_ k.inv).hom := by
        rw [TensorInverse.invIso_hom_evaluation]
    _ = (h.mulIso'.hom ▷ h.inv ≫ (λ_ h.inv).hom) ≫ (TensorInverse.invIso h k).hom := by
        rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc,
          MonoidalCategory.leftUnitor_naturality, ← Category.assoc]

/-- **The left pin of the comparison of an inverse with a transported one.** For
`a : TensorInverse L₁`, `b : TensorInverse L₂` and `ε : L₁ ≅ L₂`, the canonical comparison of `a⁻¹`
with the inverse object of `Stacks.TensorPowers.TensorInverse.ofIso ε b` — which is `b⁻¹` —
tensored with `ε` and followed by the left trivialisation of `b`, is the left trivialisation of
`a`. -/
theorem TensorInverse.tensorHom_comp_mulIso_ofIso {L₁ L₂ : C} (a : TensorInverse L₁)
    (b : TensorInverse L₂) (ε : L₁ ≅ L₂)
    (hsa : (α_ a.inv L₁ a.inv).hom ≫ a.inv ◁ a.mulIso.hom ≫ (ρ_ a.inv).hom =
      a.mulIso'.hom ▷ a.inv ≫ (λ_ a.inv).hom) :
    (ε.hom ⊗ₘ (TensorInverse.invIso a (TensorInverse.ofIso ε b)).hom) ≫ b.mulIso.hom =
      a.mulIso.hom := by
  calc (ε.hom ⊗ₘ (TensorInverse.invIso a (TensorInverse.ofIso ε b)).hom) ≫ b.mulIso.hom
      = (L₁ ◁ (TensorInverse.invIso a (TensorInverse.ofIso ε b)).hom ≫
          ε.hom ▷ (TensorInverse.ofIso ε b).inv) ≫ b.mulIso.hom := by
        rw [MonoidalCategory.tensorHom_def']
    _ = L₁ ◁ (TensorInverse.invIso a (TensorInverse.ofIso ε b)).hom ≫
          (TensorInverse.ofIso ε b).mulIso.hom := Category.assoc _ _ _
    _ = a.mulIso.hom :=
        TensorInverse.invIso_whiskerLeft_mulIso a (TensorInverse.ofIso ε b) hsa

end Stacks.TensorPowers

end
