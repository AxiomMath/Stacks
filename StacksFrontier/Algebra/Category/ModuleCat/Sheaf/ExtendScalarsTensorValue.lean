module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor

/-!
# The value of the base change comparison of a tensor product sheaf

`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` is the comparison

`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`

of base change along `θ : A₁ ⟶ A₂` with a tensor product of sheaves of modules. It is **step 6 of
the chain of six bijections of Tag 03EL**, `Stacks.SheafOfModules.pullbackTensorHomEquiv`, and
until now it was the one step of that chain accompanied by no formula: it is a three-fold
composite of isomorphisms of sheaves of modules, and its first factor is used *inverted*, so
nothing could be evaluated through it.

This file removes that inversion. The first factor is
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso`, which is by construction the
sheafification of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnit`; composing the
comparison with *that morphism* instead of inverting it leaves an identity in which the inverse
does not appear, and whose right-hand side is a single `sheafification.map` of a morphism of
**presheaves** of modules. That presheaf-level morphism does have a formula on sections: its
first factor is `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso`, whose
components are `TensorProduct.AlgebraTensorModule.distribBaseChange` by
`changeOfRingsTensorObjIso_hom_app`, carrying `a ⊗ₜ (x ⊗ₜ y)` to `(a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)`, and its
second is the tensor of the two sheafification units.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_eq`: the comparison as its three
  factors.
* `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_hom_eq`: the first factor is the
  sheafification of `changeOfRingsUnit`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom`:
  **the inverse eliminated.**
* `Stacks.Sheaves.RingedToposModules.changeOfRingsUnit_comp_extendScalarsTensorIso_hom`: **the
  value formula for step 6**, with the whole right-hand side one `sheafification.map` of an
  explicit morphism of presheaves of modules.

## Implementation notes

**Why `rw` is not used to cancel the inverse.** The target of the cancellation is literally
`e.hom ≫ e.inv ≫ h`, and `CategoryTheory.Iso.hom_inv_id_assoc` nevertheless does not apply by
`rw`: the two occurrences of `e` are produced by different elaborations and agree only at
*default* transparency, while `rw` unifies at `reducible`. The cancellation is therefore supplied
as a term, which is the discipline this directory prescribes for the seams of a composite — the
same reason `Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom` exists at all. The last
step of `changeOfRingsUnit_comp_extendScalarsTensorIso_hom` is a term for the same reason.

## What this file does not contain

**It does not prove a monoidal coherence, and it does not discharge
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`.** It supplies one of the inputs
that coherence was missing, namely the value formula for step 6 of the chain of Tag 03EL — the
one input shared by all three coherences. Two obligations recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence` and in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal` remained when this was
written, and neither is touched here:

* for either unitality coherence, a formula on sections for the unit comparison
  `ν : f^*O_D ≅ O_C` (Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, and this library's
  `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`), which came with none. **This
  one now exists**, at a common coefficient universe, as
  `moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv` in the
  namespace `Stacks.Sheaves.RingedToposModules`, in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue`;
* for the associativity coherence, the transport of *triple* pairings across the adjunction
  `f⁻¹ ⊣ f_*`, the three-variable mirror of `Stacks.SheafOfModules.inverseImageBilinearEquiv`,
  which does not exist in any form.

Nothing here is specific to a differential graded module, to a morphism of ringed topoi, or to
Tag 0FSG: the statement is about base change of sheaves of modules along a morphism of presheaves
of commutative rings, which is where it belongs.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe w v u

namespace Stacks.Sheaves.RingedToposModules

open Stacks.PresheafOfModules.ChangeOfRings

section ExtendScalarsValue

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The comparison of a base change with a tensor product, as its three factors**: the
sheafification comparison of `extendScalarsSheafifyIso` inverted, the sheafification of the
presheaf-level comparison of Tag 03CU, and the comparison of Tag 05NA. This is the definition,
restated so that a consumer need not unfold it. -/
theorem extendScalarsTensorIso_hom_eq (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalarsTensorIso θ h₁ h₂ F G).hom =
      (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val)).inv ≫
        ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
            (changeOfRingsTensorObjIso θ F.val G.val).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso A₂ h₂
            ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val)).hom) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The sheafification comparison for a base change is the sheafification of
`changeOfRingsUnit`.** `extendScalarsSheafifyIso` is by construction `asIso` of that morphism, so
this is its defining equation, needed because the comparison of a tensor product uses it
*inverted*. -/
theorem extendScalarsSheafifyIso_hom_eq (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    (extendScalarsSheafifyIso θ h₁ h₂ P).hom =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
        (changeOfRingsUnit θ h₁ P) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The inverse eliminated**: composing the comparison with the sheafification comparison —
rather than inverting the latter — leaves the two factors which are not inverses of anything. -/
theorem extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val)).hom ≫
        (extendScalarsTensorIso θ h₁ h₂ F G).hom =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
          (changeOfRingsTensorObjIso θ F.val G.val).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso A₂ h₂
          ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val)).hom :=
  (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val)).hom_inv_id_assoc _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The value formula for step 6 of the chain of Tag 03EL.** The comparison

`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`

composed with the sheafification of `changeOfRingsUnit` is the sheafification of a single
morphism of **presheaves** of modules: the presheaf-level base change comparison of Tag 03CU
followed by the tensor of the two sheafification units.

This is what step 6 was missing. Both factors on the right have a formula on sections — the first
is `TensorProduct.AlgebraTensorModule.distribBaseChange` in each component by
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso_hom_app`, carrying
`a ⊗ₜ (x ⊗ₜ y)` to `(a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)`, and the second is a tensor of sheafification units —
so an identity of morphisms out of a base-changed tensor product can now be checked past step 6.
The left-hand side carries the comparison, the right-hand side does not. -/
theorem changeOfRingsUnit_comp_extendScalarsTensorIso_hom
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
          (changeOfRingsUnit θ h₁ (F.val ⊗ G.val)) ≫
        (extendScalarsTensorIso θ h₁ h₂ F G).hom =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
        ((changeOfRingsTensorObjIso θ F.val G.val).hom ≫
          ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj F.val) ⊗ₘ
            (PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj G.val))) := by
  refine (extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom θ h₁ h₂ F G).trans ?_
  rw [Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_eq]
  exact ((PresheafOfModules.sheafification
    (R := commRingSheaf J A₂ h₂) (𝟙 _)).map_comp _ _).symm

end ExtendScalarsValue

end Stacks.Sheaves.RingedToposModules

end
