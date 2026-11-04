module

public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Basic

/-!
# Restriction to an open, read on components, and transported through a direct image

The predicate that [Stacks, Tag 01YE] concludes asks for a morphism of module sheaves on `X`
that becomes invertible after restriction to an open neighbourhood of a point, while the
construction supplies such a morphism on a *closed subscheme* and pushes it forward. This file
is the dictionary that moves the invertibility across the direct image.

## Main results

* `isIso_restrictFunctor_map_iff_forall_app`: restricting a morphism to `U` gives an isomorphism
  exactly when its component over every open contained in `U` is invertible.
* `isIso_restrictFunctor_map_pushforward`: for a morphism `ψ` of module sheaves on `W` and a
  morphism `i : W ⟶ X` with `i ⁻¹ᵁ U ≤ V`, invertibility of `ψ` restricted to `V` gives
  invertibility of `i_* ψ` restricted to `U`.

## Implementation notes

Both directions avoid comparing the two scalar actions on `Γ(M.restrict U.ι, V)` and
`Γ(M, U.ι ''ᵁ V)`, which is the usual difficulty with open immersions. The component of
`(Scheme.Modules.restrictFunctor U.ι).map φ` over `V` is literally the component of `φ` over
`U.ι ''ᵁ V` (`Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictFunctor_map_val_app`, proved
by `rfl`), and `AlgebraicGeometry.Scheme.Modules.Hom.app` lands in `AddCommGrpCat`, where the
base ring has already been forgotten — so the two module structures are never asked to agree and
no compiler escape is needed. The same remark applies to the direct image, whose components are
literally the components of the original morphism over preimages
(`AlgebraicGeometry.Scheme.Modules.pushforward_map_app`, also `rfl`).

Invertibility is assembled from and read off components by Mathlib's own
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`, which is stated at the `X.Modules`
spelling; stating these lemmas over `SheafOfModules X.ringCatSheaf` instead makes
`CategoryTheory.Functor.map_isIso` unreachable, `Scheme.Modules` being a `def`.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPowerHomColimit

universe u

namespace Stacks.AlgebraicGeometry.Tag01YEIntegralReduction

variable {X : Scheme.{u}}

/-- The image of the preimage of an open contained in `U` is that open again. -/
theorem ι_image_preimage_eq {U V : X.Opens} (hVU : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  have h : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = U ⊓ V := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf]
  rw [h, inf_eq_right.mpr hVU]

/-- **A morphism all of whose components over the opens inside `U` are invertible restricts to
an isomorphism over `U`.** -/
theorem isIso_restrictFunctor_map_of_forall_app {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (h : ∀ V : X.Opens, V ≤ U → IsIso (φ.app V)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W ↦ h _ (U.ι_image_le W)

/-- **Conversely, a morphism that restricts to an isomorphism over `U` has an invertible
component over every open contained in `U`.** -/
theorem isIso_app_of_isIso_restrictFunctor_map {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (h : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ))
    (V : X.Opens) (hVU : V ≤ U) : IsIso (φ.app V) :=
  ι_image_preimage_eq hVU ▸ Scheme.Modules.Hom.isIso_iff_isIso_app.mp h (U.ι ⁻¹ᵁ V)

/-- **Restriction to an open, read on components.** -/
theorem isIso_restrictFunctor_map_iff_forall_app {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) ↔
      ∀ V : X.Opens, V ≤ U → IsIso (φ.app V) :=
  ⟨fun h ↦ isIso_app_of_isIso_restrictFunctor_map φ U h,
    isIso_restrictFunctor_map_of_forall_app φ U⟩

/-- **Invertibility near a point transports through a direct image.** If `ψ` restricted to `V`
is an isomorphism and `U` is an open of `X` whose preimage lies in `V`, then `i_* ψ` restricted
to `U` is an isomorphism.

No hypothesis on `i` is needed: the components of `i_* ψ` are the components of `ψ` over
preimages, by definition. -/
theorem isIso_restrictFunctor_map_pushforward {W : Scheme.{u}} (i : W ⟶ X) {A G : W.Modules}
    (ψ : A ⟶ G) (V : W.Opens) (hψ : IsIso ((Scheme.Modules.restrictFunctor V.ι).map ψ))
    (U : X.Opens) (hU : i ⁻¹ᵁ U ≤ V) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward i).map ψ)) := by
  refine isIso_restrictFunctor_map_of_forall_app _ U fun V' hV' ↦ ?_
  exact isIso_app_of_isIso_restrictFunctor_map ψ V hψ (i ⁻¹ᵁ V')
    (le_trans ((Opens.map i.base).monotone hV') hU)

end Stacks.AlgebraicGeometry.Tag01YEIntegralReduction

end
