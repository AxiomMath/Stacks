module

public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Evaluation
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerAssoc
import StacksFrontier.CategoryTheory.Monoidal.TensorInversePin

/-!
# The single-tensor pin of the comparison of two tensor inverses, and what it determines

`Stacks.TensorPowers.TensorInverse.invIso h k` compares the inverse objects of two two-sided
tensor inverses of one object `L`. The compatibility it is known to satisfy,
`Stacks.TensorPowers.TensorInverse.invIso_hom_evaluation`, is a *triangle* on the triple product
`(h⁻¹ ⊗ L) ⊗ k⁻¹`. A consumer that wants to identify two composites of such comparisons needs
instead the *single-tensor* form `φ ▷ L ≫ k.mulIso' = h.mulIso'`, which is the form that composes:
the pins of `φ₁ : X ⟶ Y` and `φ₂ : Y ⟶ Z` multiply to the pin of `φ₁ ≫ φ₂`, by
`CategoryTheory.MonoidalCategory.comp_whiskerRight` alone. **This file supplies that form**, and
records what the comparison determines in return.

## Main results

* `Stacks.TensorPowers.TensorInverse.invIso_whiskerRight_mulIso'`: **the single-tensor pin.**
  Whiskered on the right by `L` and followed by the right trivialisation of `k`, the comparison is
  the right trivialisation of `h`. The hypothesis is the snake identity of `k` *read at `k.inv`*:
  the two trivialisations of `k` cancel the middle factor of `k⁻¹ ⊗ L ⊗ k⁻¹` the same way. It is
  not a formal consequence of the monoidal axioms — see `Stacks.Monoidal.braiding_eval_snake`,
  where rescaling one trivialisation breaks it — and it is the only input beyond the triangle.
* `Stacks.TensorPowers.TensorInverse.mulIso_eq_of_invIso_eq`: **the comparison determines the left
  trivialisation of its target.** Two tensor inverses of `L` with the same inverse object and the
  same comparison against a fixed `h` have the same `mulIso`.

## Why the second result is the one a base-change clause needs

The second statement looks like a curiosity and is not: it is what settles whether a square of
such comparisons can commute. `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso g L
L' hL` is `invIso` at `TensorInverse.ofIso hL.symm (negOneTensorInverse L')`, whose `mulIso` is
`hL.symm` whiskered into the left factor of the trivialisation of `L'`. So by this result the
comparison *determines* `hL`, up to nothing: replacing `hL` by `hL ≪≫ u` for an automorphism `u`
of `L'` changes the comparison whenever it changes `u ▷ (L')^{⊗ -1}` followed by that
trivialisation, which for `u = -𝟙` it does on any sheaf that is not `2`-torsion.

Consequently an equation between two composites of such comparisons, one side of which does not
mention `hL` while the other does, is **false** unless `hL` is pinned by a further hypothesis. That
is exactly the shape of the hypothesis `hinv` of
`Stacks.ProjectiveBundleConormal.sourceCoherence`, whose left-hand side is built from `e` and `hL`
and whose right-hand side is built from `e'`; the two classifying comparisons `e` and `e'` are
independent parameters there, and nothing in that statement relates them. The missing relation is
the one that `Stacks.ProjectiveBundleConormal.conormalCanonicalMap` carries as its hypothesis
`hqe`: that `e` is the comparison through which `σ^*` of the tautological map becomes `q`. The
module documentation of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceCoherence` records the measurement.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The comparison of two two-sided tensor inverses, in single-tensor form.** Whiskered on the
right by `L` and followed by the right trivialisation `k.mulIso' : k⁻¹ ⊗ L ≅ 𝟙` of the target, the
comparison `Stacks.TensorPowers.TensorInverse.invIso h k` is the right trivialisation
`h.mulIso' : h⁻¹ ⊗ L ≅ 𝟙` of the source.

This is the form that composes, and so the form a diagram of such comparisons is checked in: the
triangle `Stacks.TensorPowers.TensorInverse.invIso_hom_evaluation` has the comparison sitting after
an isomorphism out of a triple product, and two triangles do not paste without knowing how the
middle object's two trivialisations are related.

The hypothesis `hsk` is exactly that relation, for `k`: the two ways of cancelling the middle
factor of `k⁻¹ ⊗ L ⊗ k⁻¹` — reassociate and contract the right pair by `k.mulIso`, or contract the
left pair by `k.mulIso'` — agree. It is not a consequence of the monoidal axioms; in a symmetric
category with `L` of trivial self-braiding it is `Stacks.Monoidal.braiding_eval_snake`, and in
super vector spaces, where the self-braiding of an odd line is `-𝟙`, it fails. Faithfulness of
whiskering on the right by `k.inv`, which `k.mulIso'` supplies through
`Stacks.TensorPowers.whiskerRight_injective_of_mulIso`, is what lets it be used: both sides of the
conclusion are morphisms out of `h⁻¹ ⊗ L`, and `hsk` speaks of them whiskered by `k.inv`. -/
theorem TensorInverse.invIso_whiskerRight_mulIso' {L : C} (h k : TensorInverse L)
    (hsk : (α_ k.inv L k.inv).hom ≫ k.inv ◁ k.mulIso.hom ≫ (ρ_ k.inv).hom =
      k.mulIso'.hom ▷ k.inv ≫ (λ_ k.inv).hom) :
    (TensorInverse.invIso h k).hom ▷ L ≫ k.mulIso'.hom = h.mulIso'.hom := by
  refine whiskerRight_injective_of_mulIso k.mulIso' ?_
  refine (cancel_mono (λ_ k.inv).hom).mp ?_
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
  calc ((TensorInverse.invIso h k).hom ▷ L) ▷ k.inv ≫
        k.mulIso'.hom ▷ k.inv ≫ (λ_ k.inv).hom
      = ((TensorInverse.invIso h k).hom ▷ L) ▷ k.inv ≫
          (α_ k.inv L k.inv).hom ≫ k.inv ◁ k.mulIso.hom ≫ (ρ_ k.inv).hom := by rw [hsk]
    _ = (α_ h.inv L k.inv).hom ≫ (TensorInverse.invIso h k).hom ▷ (L ⊗ k.inv) ≫
          k.inv ◁ k.mulIso.hom ≫ (ρ_ k.inv).hom := by
        rw [← Category.assoc, MonoidalCategory.associator_naturality_left, Category.assoc]
    _ = (α_ h.inv L k.inv).hom ≫ h.inv ◁ k.mulIso.hom ≫
          (TensorInverse.invIso h k).hom ▷ 𝟙_ C ≫ (ρ_ k.inv).hom := by
        rw [← Category.assoc ((TensorInverse.invIso h k).hom ▷ (L ⊗ k.inv)),
          ← MonoidalCategory.whisker_exchange, Category.assoc]
    _ = (α_ h.inv L k.inv).hom ≫ h.inv ◁ k.mulIso.hom ≫ (ρ_ h.inv).hom ≫
          (TensorInverse.invIso h k).hom := by
        rw [MonoidalCategory.rightUnitor_naturality]
    _ = h.mulIso'.hom ▷ k.inv ≫ (λ_ k.inv).hom :=
        TensorInverse.invIso_hom_evaluation h k

/-- **The comparison of two two-sided tensor inverses determines the left trivialisation of its
target.** Fix a two-sided tensor inverse `h` of `L` and an object `Y`, and give `Y` two structures
of two-sided tensor inverse of `L`, with left trivialisations `m` and `m'`. If the two comparisons
`h⁻¹ ≅ Y` that `Stacks.TensorPowers.TensorInverse.invIso` builds agree, then `m = m'`.

The comparison is the right unitor, `h⁻¹` whiskered into `m⁻¹`, the associator, `h.mulIso'`
whiskered by `Y`, and the left unitor; every factor but the second is independent of `m`, and all
of them are isomorphisms. So the hypothesis cancels down to `h⁻¹ ◁ m⁻¹ = h⁻¹ ◁ (m')⁻¹`, and
whiskering on the left by `h⁻¹` is faithful because `h.mulIso` exhibits `h⁻¹` as a tensor inverse
of `L` — `Stacks.Monoidal.whiskerLeft_injective_of_tensorInverse`.

The right trivialisations play no part: they are parameters of the two structures and do not occur
in the comparison. -/
theorem TensorInverse.mulIso_eq_of_invIso_eq {L Y : C} (h : TensorInverse L)
    {m m' : L ⊗ Y ≅ 𝟙_ C} (p p' : Y ⊗ L ≅ 𝟙_ C)
    (he : TensorInverse.invIso h ⟨Y, m, p⟩ = TensorInverse.invIso h ⟨Y, m', p'⟩) :
    m = m' := by
  have hcomp : h.inv ◁ m.inv ≫ ((α_ h.inv L Y).inv ≫ h.mulIso'.hom ▷ Y ≫ (λ_ Y).hom) =
      h.inv ◁ m'.inv ≫ ((α_ h.inv L Y).inv ≫ h.mulIso'.hom ▷ Y ≫ (λ_ Y).hom) := by
    have h0 := congrArg Iso.hom he
    simp only [TensorInverse.invIso, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom] at h0
    exact (cancel_epi (ρ_ h.inv).inv).mp h0
  have : IsIso ((α_ h.inv L Y).inv ≫ h.mulIso'.hom ▷ Y ≫ (λ_ Y).hom) := by
    have : IsIso (h.mulIso'.hom ▷ Y) :=
      (MonoidalCategory.whiskerRightIso h.mulIso' Y).isIso_hom
    infer_instance
  exact Iso.ext ((Iso.inv_eq_inv _ _).mp
    (Stacks.Monoidal.whiskerLeft_injective_of_tensorInverse h.mulIso
      ((cancel_mono ((α_ h.inv L Y).inv ≫ h.mulIso'.hom ▷ Y ≫ (λ_ Y).hom)).mp hcomp)))

end Stacks.TensorPowers

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.SheafOfModules.TensorSheafification Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorPower
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

section Scheme

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (L : Mods X)
  [Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L]

/-- **Tag 0B3V's base change of the inverse determines the comparison of the lines it is taken
at.** If the two comparisons `g^*(L^{⊗ -1}) ≅ (L')^{⊗ -1}` that
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` builds from `hL` and from `hL'`
agree, then `hL = hL'`.

The comparison is `Stacks.TensorPowers.TensorInverse.invIso` at the pullback of `L`'s own tensor
inverse and at `L'`'s transported along `hL.symm`; only the second depends on `hL`, and only
through its left trivialisation, which is `hL.symm` whiskered into the first factor of
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'`. So
`Stacks.TensorPowers.TensorInverse.mulIso_eq_of_invIso_eq` recovers that trivialisation, the
trivialisation cancels, and whiskering on the right by `(L')^{⊗ -1}` is faithful because
`negOneMulIso` exhibits `L'` as its tensor inverse.

**This is why a base-change square of such comparisons needs the comparisons of the *positive*
lines to be related by a hypothesis.** An equation whose one side is built from `hL` and whose
other side is not cannot hold for two values of `hL`, and the two differ as soon as `L'` admits an
automorphism other than the identity. -/
theorem inverseQuotientBaseChangeIso_injective (L' : Mods X')
    [Stacks.SheafOfModules.IsInvertible X'.presheaf (isSheaf_structureRingPresheaf X') L']
    (hL hL' : L' ≅ (pullbackFunctor g).obj L)
    (he : inverseQuotientBaseChangeIso g L L' hL = inverseQuotientBaseChangeIso g L L' hL') :
    hL = hL' := by
  -- Several monoidal structures on sheaves of modules are in scope, and synthesis for `Mods X'`
  -- need not terminate on the local instance. Naming it in the local context fixes that; it is
  -- the same structure `inverseQuotientBaseChangeIso` is built at, so nothing is reascribed.
  let : MonoidalCategory (Mods X') :=
    Stacks.SheafInternalHom.monoidalCategory X'.presheaf (isSheaf_structureRingPresheaf X')
  have hm := TensorInverse.mulIso_eq_of_invIso_eq
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L)) _ _ he
  have h0 := congrArg Iso.hom hm
  simp only [Iso.trans_hom, MonoidalCategory.whiskerRightIso_hom] at h0
  exact Iso.ext ((Iso.inv_eq_inv _ _).mp
    (whiskerRight_injective_of_mulIso
      (negOneMulIso X'.presheaf (isSheaf_structureRingPresheaf X') L')
      ((cancel_mono
        (negOneMulIso' X'.presheaf (isSheaf_structureRingPresheaf X') L').hom).mp h0)))

end Scheme

end Stacks.ProjBundleInverseBaseChange

end
