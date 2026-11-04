module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldGenericValue

/-!
# The denominator ideal of a rational function embeds in the structure sheaf

Let `X` be a scheme. The canonical morphism `𝒪_X ⟶ 𝒦_X(𝒪_X)` is injective on the sections over
every open set: it factors as the canonical ring map `𝒪_X ⟶ K_X`, which is injective by
`AlgebraicGeometry.toTotalQuotientSheaf_app_injective`, followed by the isomorphism
`K_X ≅ 𝒦_X(𝒪_X)`. Consequently the inclusion of the ideal of denominators of any meromorphic
section of `𝒪_X` into `𝒪_X` is a monomorphism, being the base change of a monomorphism along
the opposite leg of the defining cospan.

This is the monomorphism half of the first short exact sequence of Stacks 02SW part (1) in the
case `L = 𝒪_X` needed for Stacks 0FDS; the monomorphism half of the second sequence is the
lemma `AlgebraicGeometry.denominatorIdeal_section_mono`, applied with the invertibility of
`𝒪_X` over itself.

## Main results

* `AlgebraicGeometry.toMeromorphicSectionSheafAsModule_unitModule_app` — the canonical morphism
  `𝒪_X ⟶ 𝒦_X(𝒪_X)` on the sections over an open set.
* `AlgebraicGeometry.mono_toMeromorphicSectionSheafAsModule_unitModule` — it is a monomorphism.
* `AlgebraicGeometry.mono_denominatorIdealι_unitModule` — the inclusion of the ideal of
  denominators in `𝒪_X` is a monomorphism.

## Implementation notes

Injectivity is checked on sections rather than deduced from a composite of monomorphisms:
`CategoryTheory.mono_comp` does not fire for these morphisms, because the monomorphism obtained
from the isomorphism `K_X ≅ 𝒦_X(𝒪_X)` is not synthesized in the category of sheaves of modules
over the structure sheaf. On sections the two factors are visible, and the isomorphism's
injectivity is read off its `hom_inv_id`.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample (unitModule)

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The canonical morphism `𝒪_X ⟶ 𝒦_X(𝒪_X)`, on the sections over an open set: the canonical
ring map to the sheaf of meromorphic functions, followed by the identification
`K_X ≅ 𝒦_X(𝒪_X)`. -/
theorem toMeromorphicSectionSheafAsModule_unitModule_app (V : (Opens X)ᵒᵖ)
    (a : (unitModule X).val.obj V) :
    (toMeromorphicSectionSheafAsModule X (unitModule X)).val.app V a =
      (unitIsoMeromorphicSectionSheafUnit X).hom.val.app V
        ((toTotalQuotientRingSheaf X).hom.app V a) :=
  (ConcreteCategory.congr_hom (congrArg (fun q => SheafOfModules.Hom.val q |>.app V)
      (toMeromorphicSectionSheafAsModule_eq X)) a).trans
    (congrArg (fun y => (unitIsoMeromorphicSectionSheafUnit X).hom.val.app V y)
      (toKUnit_val_app_apply X V a))

/-- **The canonical morphism `𝒪_X ⟶ 𝒦_X(𝒪_X)` is a monomorphism.** On sections it is the
canonical ring map `𝒪_X ⟶ K_X`, which is injective, followed by an isomorphism. -/
theorem mono_toMeromorphicSectionSheafAsModule_unitModule :
    Mono (toMeromorphicSectionSheafAsModule X (unitModule X)) := by
  refine SheafOfModules.mono_of_forall_app_injective _ fun V a b hab => ?_
  refine toTotalQuotientSheaf_app_injective X V.unop ?_
  have hid (z) := ConcreteCategory.congr_hom (congrArg (fun q => q.val.app V)
    (unitIsoMeromorphicSectionSheafUnit X).hom_inv_id) z
  refine (hid _).symm.trans (Eq.trans ?_ (hid _))
  exact congrArg (fun y => (unitIsoMeromorphicSectionSheafUnit X).inv.val.app V y)
    ((toMeromorphicSectionSheafAsModule_unitModule_app X V a).symm.trans
      (hab.trans (toMeromorphicSectionSheafAsModule_unitModule_app X V b)))

/-- **The inclusion of the ideal of denominators in `𝒪_X` is a monomorphism.** The ideal of
denominators is the fibre product of multiplication by the section and of the canonical morphism
`𝒪_X ⟶ 𝒦_X(𝒪_X)`, and base change of the latter monomorphism along the former is a
monomorphism. -/
theorem mono_denominatorIdealι_unitModule
    (s : MeromorphicSection X.sheaf (unitModule X)) :
    Mono (denominatorIdealι X (unitModule X) s) :=
  have := mono_toMeromorphicSectionSheafAsModule_unitModule X
  pullback.fst_of_mono

end AlgebraicGeometry
