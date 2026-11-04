module

public import StacksFrontier.Deformation.LiftsOfObjects.Action.Functoriality

/-!
# A sum of values of a linear lift is realized over a doubled coordinate object

Let `F : C ⥤ Type _` be a set-valued functor carrying a linear lift `L` in the sense of
[Stacks Project, Tag 06I6], so that each `F.obj V` is the underlying set of a `k`-module
functorially in `V`. The addition of that module structure is not given by a formula — for the
associated square-zero functor of a deformation category it is produced by the product
conditions of [Stacks Project, Tag 06I6] — so a sum `s + t` of two elements of `F.obj V` cannot
be computed from `s` and `t` directly.

What *can* be done is to realize the sum geometrically. If `V` sits inside an object `W` as a
direct summand twice over, by sections `i₁, i₂ : V ⟶ W` of projections `p₁, p₂ : W ⟶ V`, then
there is a single element `z` of `F.obj W` whose image under `p₁` is `s`, whose image under `p₂`
is `t`, and whose image under `p₁ + p₂` is `s + t`. This is
`Deformation.exists_linearFunctorLift_sum`.

That is the only handle a sum of values offers, and it is what every additivity statement about a
map out of such a value consumes: to compare a construction applied to `s + t` with the two
constructions applied to `s` and to `t`, one runs the construction *once* at `z` over `W` and
pushes it forward along the three arrows. For the tangent space of a deformation category at the
rank-one module, `W` is the rank-two module and the three arrows are the two projections and
their sum — the step that forces the coefficient module `k ⊕ k` to appear in any additivity proof
about a first-order deformation, as in the derivation arrow of
[Stacks Project, Tag 0E3V].

## Main results

* `Deformation.exists_linearFunctorLift_sum`: a sum of two values of a linear lift at `V` is the
  image under `p₁ + p₂` of a single value at `W`, whose images under `p₁` and `p₂` are the two
  summands.

## Implementation notes

The element `z` is built in the module, where the sum is available, and then transported into
the set-valued functor by `Deformation.linearFunctorLiftEquiv`: it is
`i₁ (s) + i₂ (t)` read through the lift. Each of the three conclusions is then the naturality of
that transport, `Deformation.linearFunctorLiftEquiv_map`, followed by the splitting relations
`i₁ ≫ p₁ = 𝟙`, `i₂ ≫ p₁ = 0` and their mirrors, which turn the two terms of the sum into one
summand and zero.

The four splitting relations are taken as hypotheses rather than obtained from a biproduct
decomposition of `W`. Stating them that way keeps the lemma applicable at the concrete rank-two
module `V × V` of `FGModuleCat`, where the four relations hold by `rfl` while exhibiting the
object as a categorical biproduct would be extra work.

## References

* [Stacks Project, Tag 06I6](https://stacks.math.columbia.edu/tag/06I6)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

section

universe uk uC vC uM

variable {k : Type uk} [CommRing k]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [CategoryTheory.Linear k C]
  {F : C ⥤ Type uM}

/-- **A sum of two values of a linear lift is realized by a single value over a doubled
coordinate object.** Let `V` be a direct summand of `W` twice over, by sections `i₁` and `i₂` of
projections `p₁` and `p₂` with `i₁ ≫ p₁ = 𝟙`, `i₂ ≫ p₁ = 0`, `i₁ ≫ p₂ = 0` and `i₂ ≫ p₂ = 𝟙`.
Then for any two elements `s` and `t` of `F.obj V` there is a single `z` in `F.obj W` with
`p₁ z = s`, `p₂ z = t` and `(p₁ + p₂) z = s + t`, the sum being the one the lift `L` puts on
`F.obj V`.

This is the only way to get at a sum of values of a lift whose addition is not given by a
formula: run a construction once at `z` and push it along the three arrows. -/
theorem exists_linearFunctorLift_sum (L : LinearFunctorLift k F) {V W : C}
    (p₁ p₂ : W ⟶ V) (i₁ i₂ : V ⟶ W)
    (h₁₁ : i₁ ≫ p₁ = 𝟙 V) (h₂₁ : i₂ ≫ p₁ = 0)
    (h₁₂ : i₁ ≫ p₂ = 0) (h₂₂ : i₂ ≫ p₂ = 𝟙 V)
    (s t : F.obj V) :
    ∃ z : F.obj W, F.map p₁ z = s ∧ F.map p₂ z = t ∧
      F.map (p₁ + p₂) z =
        linearFunctorLiftEquiv L V
          ((linearFunctorLiftEquiv L V).symm s + (linearFunctorLiftEquiv L V).symm t) := by
  -- the element built in the module, where the sum is available
  set zL := (L.functor.map i₁).hom ((linearFunctorLiftEquiv L V).symm s) +
    (L.functor.map i₂).hom ((linearFunctorLiftEquiv L V).symm t) with hzL
  -- the image of the transported `zL` under an arrow `W ⟶ V`, via the splitting relations
  have hproj : ∀ (q : W ⟶ V) (a b : V ⟶ V),
      i₁ ≫ q = a → i₂ ≫ q = b →
      F.map q (linearFunctorLiftEquiv L W zL) = linearFunctorLiftEquiv L V
        ((L.functor.map a).hom ((linearFunctorLiftEquiv L V).symm s) +
          (L.functor.map b).hom ((linearFunctorLiftEquiv L V).symm t)) := by
    intro q a b ha hb
    rw [← linearFunctorLiftEquiv_map L q zL, hzL, map_add,
      ← ModuleCat.comp_apply (L.functor.map i₁) (L.functor.map q),
      ← ModuleCat.comp_apply (L.functor.map i₂) (L.functor.map q),
      ← L.functor.map_comp, ← L.functor.map_comp, ha, hb]
  refine ⟨linearFunctorLiftEquiv L W zL, ?_, ?_, ?_⟩
  · rw [hproj p₁ (𝟙 V) 0 h₁₁ h₂₁, L.functor.map_id, L.functor.map_zero]
    simp
  · rw [hproj p₂ 0 (𝟙 V) h₁₂ h₂₂, L.functor.map_id, L.functor.map_zero]
    simp
  · -- both sections split the *sum* of the two projections, so one computation does it
    rw [hproj (p₁ + p₂) (𝟙 V) (𝟙 V)
        (by rw [Preadditive.comp_add, h₁₁, h₁₂, add_zero])
        (by rw [Preadditive.comp_add, h₂₁, h₂₂, zero_add]),
      L.functor.map_id]
    simp

end

end Deformation

end
