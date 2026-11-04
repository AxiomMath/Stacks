module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal

/-!
# A module over a factor is a retract of its tensor product with that factor

Let `R ≅ ∏_i factor i` be a sheaf of commutative rings presented as a product, and let `L` be a
sheaf of modules over the factor `factor n`, read as a sheaf of `R`-modules through the `n`-th
projection (`Stacks.SheafOfModules.RingSheafProductFactor.projRing`).  Then `L` is a retract of
`factor n ⊗_R L` in `Mod(R)`.

In fact the two are isomorphic — the projection `R ⟶ factor n` is surjective on sections, so
`factor n ⊗_R L = factor n ⊗_{factor n} L = L` — but the retract is what the consumer needs and
it is cheaper: only one of the two composites has to be computed.

The retract is produced at the level of *presheaves* of modules, where the two maps are the
section formulas `x ↦ 1 ⊗ x` and `a ⊗ x ↦ a • x`, and is then carried to sheaves of modules by
sheafification.  The composite `x ↦ 1 ⊗ x ↦ 1 • x = x` is where the content sits, and the content
is the surjectivity half of `ProductPresentation`: `1 : (factor n)(U)` is the `n`-th component of
a section `e` of `R(U)` whose other components vanish
(`ProductPresentation.inclSection`), and that `e` acts as the identity on the sections of every
module over `factor n`.  **The statement is false for a general `R`-module**: for `L = R` itself
and two nonzero factors, `factor n ⊗_R R = factor n` is not a retract of `R`, which is why the
restriction of scalars is load-bearing here and not bookkeeping.

## Main definitions

* `Stacks.SheafOfModules.RingSheafProductFactor.presheafRetractRestrictScalars`: the retract at
  the level of presheaves of modules, with `i` the left unit constraint followed by the `n`-th
  projection and `r` the inclusion of the `n`-th factor followed by the left unit constraint.

## Main results

* `Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_sheafTensor_restrictScalars`:
  **`L` is a retract of `factor n ⊗_R L`** for the tensor product sheaf
  `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_tensorObj_restrictScalars`: the
  same at the monoidal spelling `F ⊗ G` of `SheafOfModules.monoidalCategorySheafTensor`.

## Implementation notes

**Why the presheaf level.**  The source of the retract is `L`, not a sheafification, so no
morphism has to be constructed *out of* a sheafified tensor product and no local-pure-tensor
extensionality argument is needed; applying `Stacks.SheafOfModules.Tensor.sheafifyMod` to a
presheaf-level retract (`CategoryTheory.Retract.map`) and composing with the counit isomorphism
`SheafOfModules.counitIso` is the whole passage to sheaves.

**The two scalar spellings.**  The section `e` acts on the sections of `L` through the ring
homomorphism `R(U) ⟶ (factor n)(U)`, and the carrier of `(Stacks.SheafOfModules.Tensor.ringSheaf
R)(U)` gets its `Ring` instance through `RingCat` while the same carrier read as a section of `R`
gets one through `CommRingCat`; the two are not identified at `implicit` transparency, so no `rw`
or `simp only` acts on a goal mixing them.  The single step needed is therefore taken by
`Stacks.SheafOfModules.RingSheafProductFactor.restrictScalars_smul_eq_self`, which states it with
both rings, the module and the section all variables and is applied by `exact`; it is reused from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal` rather than
copied.  The same device is used for the one-object step
`leftUnitor_whiskerRight_apply_of_unit`, stated over a bare commutative ring.

Nothing here is a clause of Stacks 0FPG; this is a step of the proof of its implication
`(2) ⟹ (1)`, so no declaration carries the project tag.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose off-diagonal terms consume this retract.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TensorProduct

universe v u w t

noncomputable section

namespace Stacks.SheafOfModules.RingSheafProductFactor

/-- **The one-object step**: conjugating `g ∘ f : 𝟙_ ⟶ 𝟙_` by the left unit constraint of
`ModuleCat` is scalar multiplication by `g (f 1)`.

Stated over a bare commutative ring with the two morphisms and the element variables, so that it
applies by `exact` at the sections of a presheaf of modules, where the goal mixes the `RingCat`
and `CommRingCat` spellings of one ring of sections and no rewriting tactic can act on it. -/
public theorem leftUnitor_whiskerRight_apply_of_unit {A : Type w} [CommRing A]
    {N : ModuleCat.{w} A} (f : 𝟙_ (ModuleCat.{w} A) ⟶ N) (g : N ⟶ 𝟙_ (ModuleCat.{w} A))
    (M : ModuleCat.{w} A) (m : M) :
    (λ_ M).hom ((g ▷ M) ((f ▷ M) ((λ_ M).inv m))) = g (f (1 : A)) • m := by
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type t}
  {factor : ι → Sheaf J CommRingCat.{max u v}} {R : Sheaf J CommRingCat.{max u v}}
  (hp : ProductPresentation R factor)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

section Presheaf

variable [DecidableEq ι]

/-- **A module over the `n`-th factor is a retract of its presheaf tensor product with that
factor.**  The inclusion is `x ↦ 1 ⊗ x`, written as the inverse left unit constraint followed by
the `n`-th projection; the retraction is `a ⊗ x ↦ a • x`, written as the inclusion of the `n`-th
factor followed by the left unit constraint.  Their composite is `x ↦ e • x` for `e` the section
of `R` with `n`-th component `1` and all others zero, and that is `x`. -/
public def presheafRetractRestrictScalars (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    Retract ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L).val
      ((factorModule hp n).val ⊗
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L).val) where
  i := (λ_ _).inv ≫ (factorProjection hp n).val ▷ _
  r := (factorInclusion hp n).val ▷ _ ≫ (λ_ _).hom
  retract := by
    refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    let : CommRing ↥((Tensor.ringSheaf R).obj.obj U) :=
      inferInstanceAs (CommRing ↥(R.obj.obj U))
    have h1 : (factorProjection hp n).val.app U (1 : ↥((Tensor.ringSheaf R).obj.obj U))
        = (1 : ↥((factor n).obj.obj U)) := map_one ((hp.π n).hom.app U).hom
    refine Eq.trans (leftUnitor_whiskerRight_apply_of_unit
      ((factorProjection hp n).val.app U) ((factorInclusion hp n).val.app U) _ x) ?_
    exact restrictScalars_smul_eq_self _ _
      ((hp.app_inclSection_self n U _).trans h1) x

end Presheaf

/-- **A module over the `n`-th factor is a retract of its tensor product with that factor**, for
the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 01CA].

Sheafification carries the presheaf-level retract `presheafRetractRestrictScalars` to one between
the sheafification of `L` and the tensor product sheaf, and the counit isomorphism
`SheafOfModules.counitIso` identifies the former with `L`.

The statement is independent of a decidable equality on the index type. -/
public theorem nonempty_retract_sheafTensor_restrictScalars (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    Nonempty (Retract ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)
      (((Tensor.sheafTensor R).obj (factorModule hp n)).obj
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L))) := by
  classical
  exact ⟨(Retract.ofIso (_root_.SheafOfModules.counitIso R
      ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)).symm).trans
    ((presheafRetractRestrictScalars hp n L).map
      (PresheafOfModules.sheafification (R := Tensor.ringSheaf R) (𝟙 (Tensor.ringSheaf R).obj)))⟩

/-- **A module over the `n`-th factor is a retract of its tensor product with that factor**, at
the monoidal spelling `F ⊗ G` of `SheafOfModules.monoidalCategorySheafTensor`, whose tensor
product is `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose.

This is the form the assembly of the implication `(2) ⟹ (1)` of Stacks 0FPG consumes: it is what
removes the flatness hypotheses from the off-diagonal vanishing, because the idempotent cutting
out a factor acts as the identity on every module over that factor and hence kills every `Tor`
against a module over a different factor, not merely the tensor product. -/
public theorem nonempty_retract_tensorObj_restrictScalars (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
    Nonempty (Retract ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)
      (factorModule hp n ⊗ (_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)) :=
  nonempty_retract_sheafTensor_restrictScalars hp n L

end Stacks.SheafOfModules.RingSheafProductFactor

end

end
