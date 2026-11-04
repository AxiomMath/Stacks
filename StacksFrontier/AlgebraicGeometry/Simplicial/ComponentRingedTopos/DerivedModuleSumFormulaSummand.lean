module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormula

/-!
# The derived module direct-sum formula, read back as a composite

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site whose structure-sheaf transitions out of degree `n` are flat. The componentwise
direct-sum formula of Stacks 0D72 (6) on derived categories,
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula`, is built in two steps: the
formula at the degreewise transition pullbacks,
`…derivedModuleSumFormulaMapDerivedCategory`, composed summandwise with the identification
`…derivedTransitionPullbackIsoMapDerivedCategory` of each derived pullback `Lf_φ^*` with the
functor induced by `f_φ^*`.

This file records that two-step construction as an *equation*. The generic summand description of
such a formula, `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_liftedTransition`, is
stated about the composite `derivedCompBiproductIso … ≪≫ biproduct.mapIso …`; to apply it to
`…derivedModuleSumFormula` one needs exactly this equation; it is the step from that generic
description to the derived form of the summand assertion of Stacks 0D72 (6).

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula_eq`: **the derived direct-sum
  formula is the degreewise formula composed summandwise with the identification of the derived
  pullbacks.**

## Implementation notes

*The obstruction was instance synthesis, not the cost of the conversion.* The equation holds by a
single delta step, and once its right-hand side elaborates the proof is `rfl` and costs
essentially nothing. What is delicate is making the right-hand side elaborate at all, and two
devices are needed.

First, the ambient category of `CategoryTheory.Limits.biproduct.mapIso` is pinned, with
`(C := DerivedCategory (S.componentRingedTopos O m).Modules)`. Its two families live at the two
spellings of the module category of the degree-`m` component —
`AlgebraicGeometry.RingedTopos.Modules` of `…componentRingedTopos` for the target, and
`SheafOfModules` over `…componentRingSheaf` for the source — and left to itself the elaborator
takes the ambient category from the source family and then asks for the biproduct of the target
family at that spelling, which instance search does not find. Pinning it makes the target family's
biproduct the one that is found in the signature of `…derivedModuleSumFormula` itself.

Second, with the ambient category pinned, the biproduct of the *degreewise* family is the one that
instance search cannot reach, and it is supplied by `inferInstanceAs`: the instance is synthesized
at the `SheafOfModules` spelling, where plain search finds it, and accepted against the pinned
spelling by `rfl`. This is the crossing described in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedModuleSumFormula.lean` —
a term of one spelling accepted against a statement in the other — performed once, on an
instance.

Without either device the failure is reported as `failed to synthesize HasBiproduct …` on a family
that prints exactly as the one `CategoryTheory.Limits.biproduct.ι` accepts two lines above, which
is why it reads as a universe or metavariable problem and is neither.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The derived componentwise direct-sum formula is the degreewise formula composed summandwise
with the identification of the derived pullbacks.** The restriction to degree `m` of the derived
lower shriek from degree `n` is identified with the direct sum of the derived pullbacks `Lf_φ^*`
by first identifying it with the direct sum of the functors induced by the degreewise pullbacks
`f_φ^*`, and then rewriting each summand along
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory`.

This is the definition of `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` read
back as an equation, which is what exhibits that formula in the shape the generic summand
description `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_liftedTransition` is stated
about. See the implementation notes of this file for the two devices that make the right-hand
side elaborate. -/
theorem derivedModuleSumFormula_eq (n m : SimplexCategory)
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    letI : ∀ φ : n ⟶ m, (S.transitionPullbackModules' O φ).Additive := fun φ =>
      inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
    letI : ∀ φ : n ⟶ m, PreservesFiniteLimits (S.transitionPullbackModules' O φ) := fun φ =>
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).1
    letI : ∀ φ : n ⟶ m, PreservesFiniteColimits (S.transitionPullbackModules' O φ) := fun φ =>
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).2
    letI : Limits.HasBiproduct (C := DerivedCategory (S.componentRingedTopos O m).Modules)
        (fun φ : n ⟶ m => (S.transitionPullbackModules' O φ).mapDerivedCategory.obj X) :=
      inferInstanceAs (Limits.HasBiproduct
        (fun φ : n ⟶ m => (S.transitionPullbackModules' O φ).mapDerivedCategory.obj X))
    S.derivedModuleSumFormula O n m hflat X =
      S.derivedModuleSumFormulaMapDerivedCategory O n m hflat X ≪≫
        Limits.biproduct.mapIso
          (C := DerivedCategory (S.componentRingedTopos O m).Modules)
          (fun φ : n ⟶ m =>
            ((S.derivedTransitionPullbackIsoMapDerivedCategory O φ (hflat m φ)).app X).symm) :=
  rfl

end CategoryTheory.SimplicialSiteSituation

end
