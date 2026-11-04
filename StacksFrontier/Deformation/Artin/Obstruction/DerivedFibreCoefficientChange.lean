module

public import StacksFrontier.Deformation.Artin.Obstruction

/-!
# Changing the coefficients of a derived fibre by an isomorphism

The two cohomological conditions of [Stacks, Tag 07YM] are statements about the map
`H^n(ξ ⊗ᴸ_A k)` induced by `ξ : E ⟶ NL_{A/Λ}` on the derived fibre at a coefficient
`A`-algebra `k`. The tag states them at the residue field `κ(u₀)` of the point, while the
direction `(2) ⇒ (1)` runs through the complete local ring `R` of `Spec A` at `u₀` and its
*own* residue field, which is canonically isomorphic to `κ(u₀)` but not equal to it.

This file is the transport. In the presentation of the derived fibre through a chosen
derived tensor product the coefficient enters as an object `M` of `ModuleCat A`, so an
isomorphism of coefficient modules gives, by functoriality alone, a natural isomorphism of
the two functors `(−) ⊗ᴸ_A M` and `(−) ⊗ᴸ_A N`; naturality at `ξ` then exchanges the two
maps up to isomorphisms on both sides, and surjectivity and injectivity are preserved.

## Main results

* `Deformation.Artin.surjective_derivedTensorFibre_congr` and
  `Deformation.Artin.injective_derivedTensorFibre_congr` — the two conditions depend on the
  coefficient module only through its isomorphism class.

## Implementation notes

Nothing is used of the derived tensor product beyond that it is a bifunctor: the statement
holds for an arbitrary morphism of `D(A)`, an arbitrary degree and an arbitrary isomorphism
of coefficient modules, with no boundedness or finiteness hypothesis. The transport of
surjectivity across the resulting square is `CategoryTheory.epi_of_epi` together with the
observation that a map equal to an epimorphism composed with an isomorphism is an
epimorphism; `ModuleCat.epi_iff_surjective` and `ModuleCat.mono_iff_injective` convert.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

section Squares

variable {C : Type*} [Category C] {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') [IsIso a] [IsIso b] (w : f ≫ b = a ≫ f')

include w in
/-- In a commuting square whose vertical maps are isomorphisms, one horizontal map is an
epimorphism exactly when the other is. -/
public theorem epi_iff_of_isIso_sq : Epi f ↔ Epi f' := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : Epi (a ≫ f') := by
      rw [← w]
      infer_instance
    exact epi_of_epi a f'
  · rw [show f = (f ≫ b) ≫ inv b by simp, w]
    infer_instance

include w in
/-- In a commuting square whose vertical maps are isomorphisms, one horizontal map is a
monomorphism exactly when the other is. -/
public theorem mono_iff_of_isIso_sq : Mono f ↔ Mono f' := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [show f' = inv a ≫ a ≫ f' by simp, ← w]
    infer_instance
  · have : Mono (f ≫ b) := by
      rw [w]
      infer_instance
    exact mono_of_mono f b

end Squares

section CoefficientChange

variable {A : Type u} [CommRing A] (T : DerivedTensorProduct A)
  {E F : DerivedCategory (ModuleCat.{u} A)} (ξ : E ⟶ F) (n : ℤ)
  {M N : ModuleCat.{u} A} (ε : M ≅ N)

/-- The natural isomorphism between tensoring with `M` and tensoring with `N`, for
isomorphic coefficient modules placed in degree `0`. -/
public def derivedTensorCoefficientIso :
    T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) :=
  T.tensor.flip.mapIso ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso ε)

/-- The square relating the two derived fibres of `ξ` commutes, by naturality. -/
public theorem homologyFunctor_map_derivedTensorCoefficientIso_naturality :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).map ξ) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((derivedTensorCoefficientIso T ε).hom.app F) =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((derivedTensorCoefficientIso T ε).hom.app E) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).map ξ) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
    ((derivedTensorCoefficientIso T ε).hom.naturality ξ)

include ε in
/-- **The degree-`n` derived fibre depends on the coefficient module only through its
isomorphism class, surjectively.** -/
public theorem surjective_derivedTensorFibre_congr :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).map ξ)) ↔
      Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).map ξ)) := by
  rw [← ModuleCat.epi_iff_surjective, ← ModuleCat.epi_iff_surjective]
  exact epi_iff_of_isIso_sq _ _ _ _
    (homologyFunctor_map_derivedTensorCoefficientIso_naturality T ξ n ε)

include ε in
/-- **The degree-`n` derived fibre depends on the coefficient module only through its
isomorphism class, injectively.** -/
public theorem injective_derivedTensorFibre_congr :
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).map ξ)) ↔
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).map ξ)) := by
  rw [← ModuleCat.mono_iff_injective, ← ModuleCat.mono_iff_injective]
  exact mono_iff_of_isIso_sq _ _ _ _
    (homologyFunctor_map_derivedTensorCoefficientIso_naturality T ξ n ε)

end CoefficientChange

end Deformation.Artin

end
