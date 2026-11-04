module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposTransition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorTwoMorphismMonoidal

/-!
# A transition twisted by a 2-morphism is coherent as soon as the transition is

`Stacks.SheafOfModules.PullbackTensorTransitionCoherence φ ψ χ θ` is the compatibility of a
transition `θ : ψ^* ⋙ φ^* ⟶ χ^*` of pullbacks of sheaves of modules with the comparison of
**Stacks 03EL** at the three morphisms of ringed topoi involved. The `θ` it speaks of is
arbitrary, and the transitions that arise in practice are not: they are obtained from a transition
at some *other* morphism `χ₀ : X ⟶ Z` by composing with the transformation of pullbacks induced by
a 2-morphism `χ ⟶ χ₀` of Stacks 04IC.

This file records that the coherence is **stable under that twist**: the coherence for `θ₀` at
`χ₀` implies the coherence for `θ₀ ≫ t.pullbackModulesMap` at `χ`, for every 2-morphism
`t : χ ⟶ χ₀`, with no invertibility assumed anywhere. The reason is the monoidal law of
`StacksDraft.…​.PullbackTensorTwoMorphismMonoidal` — the comparison of Stacks 03EL is compatible
with `AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` at two *parallel* morphisms
of ringed topoi — and nothing else; the remaining steps are associativity and the functoriality of
the tensor product in its two variables.

What this reduces the coherence to is the one case `χ₀ = ψ ∘ φ`,
`θ₀ = (Stacks.SheafOfModules.pullbackModulesCompAdjIso φ ψ).inv`: the assertion that the
*compositor* of Stacks 03D8 is monoidal. That case is the only remaining input, and it is what the
six composition laws of the chain of Stacks 03EL
(`Stacks.SheafOfModules.pullbackTensorStep1_comp'` through `…Step5_comp` and
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_eq_comp`) are about; it is not
proved here.

## Main results

* `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_comp_pullbackModulesMap`: **the
  coherence of a transition of pullbacks with the comparison of Stacks 03EL is stable under
  composing the transition with the transformation of pullbacks induced by a 2-morphism.**

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

/-- The rearrangement the transfer consists of, over abstract morphisms of an abstract category:
from `m₂ ≫ m₃ = m₄ ≫ m₅` (the monoidal law for the 2-morphism), `m₁ ≫ m₄ = m₆ ≫ m₇ ≫ m₈` (the
coherence at `χ₀`) and `m₈ ≫ m₅ = m₉` (the merge of the two tensored transformations) to
`(m₁ ≫ m₂) ≫ m₃ = m₆ ≫ m₇ ≫ m₉`.

It is stated separately because the categories of sheaves of modules the transfer takes place in
are the ones in which a rewrite by associativity has to unify category instances; here there is a
single abstract category and the rewriting is free. -/
private lemma transfer_aux {𝒞 : Type u} [Category.{v} 𝒞] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ : 𝒞}
    {m₁ : O₁ ⟶ O₂} {m₂ : O₂ ⟶ O₃} {m₃ : O₃ ⟶ O₄} {m₄ : O₂ ⟶ O₅} {m₅ : O₅ ⟶ O₄}
    {m₆ : O₁ ⟶ O₆} {m₇ : O₆ ⟶ O₇} {m₈ : O₇ ⟶ O₅} {m₉ : O₇ ⟶ O₄}
    (h₁ : m₂ ≫ m₃ = m₄ ≫ m₅) (h₂ : m₁ ≫ m₄ = m₆ ≫ m₇ ≫ m₈) (h₃ : m₈ ≫ m₅ = m₉) :
    (m₁ ≫ m₂) ≫ m₃ = m₆ ≫ m₇ ≫ m₉ := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, Category.assoc, h₃]

section Transfer

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- **The coherence of a transition of pullbacks with the comparison of Stacks 03EL is stable
under twisting by a 2-morphism.**

Let `φ : X ⟶ Y` and `ψ : Y ⟶ Z` be morphisms of ringed topoi, let `χ, χ₀ : X ⟶ Z` be two further
ones and let `t : χ ⟶ χ₀` be a 2-morphism of Stacks 04IC between them, so that
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` is a transformation
`χ₀^* ⟶ χ^*` of the pullbacks of sheaves of modules. If a transition `θ₀ : ψ^* ⋙ φ^* ⟶ χ₀^*`
satisfies `Stacks.SheafOfModules.PullbackTensorTransitionCoherence`, then so does the transition
`θ₀ ≫ t.pullbackModulesMap : ψ^* ⋙ φ^* ⟶ χ^*`.

Neither `t` nor `θ₀` is assumed invertible. The proof composes the coherence at `χ₀` with the
monoidal law
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackTensorIso_hom_app_comp_pullbackModulesMap`
for `t` and merges the two transformations tensored into the two factors by functoriality of the
tensor product. -/
theorem pullbackTensorTransitionCoherence_comp_pullbackModulesMap
    (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
    {χ χ₀ : AlgebraicGeometry.RingedToposHom X Z}
    (t : AlgebraicGeometry.RingedToposHom.TwoMorphism χ χ₀)
    (θ₀ : ψ.pullbackModules ⋙ φ.pullbackModules ⟶ χ₀.toModulesHom.pullbackModules)
    (h : PullbackTensorTransitionCoherence φ ψ χ₀.toModulesHom θ₀) :
    PullbackTensorTransitionCoherence φ ψ χ.toModulesHom (θ₀ ≫ t.pullbackModulesMap) := by
  intro A B
  exact transfer_aux (t.pullbackTensorIso_hom_app_comp_pullbackModulesMap A B) (h A B)
    (by rw [← Functor.map_comp]; rfl)

end Transfer

end Stacks.SheafOfModules

end
