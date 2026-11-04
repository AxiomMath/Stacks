module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.ReflectionAlongTriangulatedFunctor
public import StacksFrontier.Homology.DerivedComplete.CompletionUnitDenseModIdeal

/-!
# The derived completion unit is surjective modulo the ideal on cohomology in every degree

Let `I` be an ideal of a Noetherian ring `A` and let `X` be an object of `D(A)` all of whose
cohomology modules are finite. `Homology/DerivedComplete/CompletionUnitDenseModIdeal.lean` proves
that the image of

`H^0(X) ⟶ H^0(X^∧)`

together with `I · H^0(X^∧)` is all of `H^0(X^∧)`. This file carries that statement to an
arbitrary degree `q`.

## The one thing the shift costs

`H^q(η_X)` is `H^0(η_{X⟦q⟧})` read through the identification `(X⟦q⟧)^∧ ≅ (X^∧)⟦q⟧` — and the
statement being transported is about the *image of a map*, so a non-canonical identification is
useless: it has to carry `η_{X⟦q⟧}` to `(η_X)⟦q⟧`. That is
`CategoryTheory.ObjectProperty.unit_comp_isoReflectionShift_hom`, which holds because the derived
`I`-complete objects are stable under the shift, so the shifted reflection *is* a reflection of
the shift.

## Main results

* `Stacks.Algebraization.range_sup_smul_eq_top_of_linearEquiv` — transport of "the image of `f`
  together with `I • ⊤` is everything" along linear equivalences of the source and the target.
* `Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree` — the
  statement in degree `q`.

## References

* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Algebraization

attribute [local instance] HasDerivedCategory.standard

/-- **Transport of "the image of `f` together with `I • ⊤` is everything"** along linear
equivalences `α` of the source and `β` of the target intertwining `f` with `f'`. -/
public theorem range_sup_smul_eq_top_of_linearEquiv {A : Type u} [CommRing A] (I : Ideal A)
    {M N M' N' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup M'] [Module A M'] [AddCommGroup N'] [Module A N']
    (f : M →ₗ[A] N) (f' : M' →ₗ[A] N') (α : M ≃ₗ[A] M') (β : N ≃ₗ[A] N')
    (hcomm : ∀ m, β (f m) = f' (α m))
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule A N) = ⊤) :
    LinearMap.range f' ⊔ I • (⊤ : Submodule A N') = ⊤ := by
  refine le_antisymm le_top fun x' _ => ?_
  have hx : β.symm x' ∈ LinearMap.range f ⊔ I • (⊤ : Submodule A N) := by
    rw [h]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hx
  obtain ⟨m, rfl⟩ := hu
  have hx' : x' = f' (α m) + β v := by
    rw [← hcomm m, ← map_add, huv, β.apply_symm_apply]
  rw [hx']
  refine Submodule.add_mem_sup ⟨α m, rfl⟩ ?_
  have hmap := Submodule.mem_map_of_mem (f := (β : N →ₗ[A] N')) hv
  rw [Submodule.map_smul''] at hmap
  exact (smul_mono_right I (le_top : Submodule.map (β : N →ₗ[A] N') ⊤ ≤ ⊤)) hmap

/-- **The derived completion unit is surjective modulo `I` on cohomology in every degree.** Let
`I` be an ideal of a Noetherian ring `A` and let `X` be an object of `D(A)` all of whose
cohomology modules are finite. Then the image of `H^q(X) ⟶ H^q(X^∧)` together with
`I · H^q(X^∧)` is all of `H^q(X^∧)`.

This is `Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top` at `X⟦q⟧`,
transported along the identification `(X⟦q⟧)^∧ ≅ (X^∧)⟦q⟧` of
`CategoryTheory.ObjectProperty.isoReflectionShift`, which carries `η_{X⟦q⟧}` to `(η_X)⟦q⟧` and
so may be used on a statement about the image of a map, and along the shift isomorphism
`H^0(-⟦q⟧) ≅ H^q(-)` of the shift sequence on the cohomology functors. -/
public theorem range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X)) (q : ℤ) :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map
          ((adicCompletionUnit A I hI).app X)).hom ⊔
        I • (⊤ : Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((adicCompletionFunctor A I hI).obj X))) = ⊤ := by
  have : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have : (Dualizing.derivedCompleteProperty.{u, u} A I).IsStableUnderShift ℤ :=
    ⟨fun n => ⟨fun K hK => isDerivedComplete_shift I hK n⟩⟩
  -- the shift isomorphisms on cohomology
  let Φ : ∀ n n' : ℤ, q + n = n' → (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) q ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n') := fun n n' h =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso q n n' h
  have hX' : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj (X⟦q⟧)) := by
    intro n
    have := hX (q + n)
    exact Module.Finite.equiv ((Φ n (q + n) rfl).app X).toLinearEquiv.symm
  let Φ₀ := Φ 0 q (add_zero q)
  have h0 := range_homologyMap_adicCompletionUnit_sup_smul_eq_top A I hI (X⟦q⟧) hX'
  -- the unit-compatible identification `(X⟦q⟧)^∧ ≅ (X^∧)⟦q⟧`
  let e := CategoryTheory.ObjectProperty.isoReflectionShift
    (Dualizing.derivedCompleteProperty.{u, u} A I) (adicCompletionAdjunction A I hI) X q
  have hunit : (adicCompletionUnit A I hI).app (X⟦q⟧) ≫ e.hom =
      ((adicCompletionUnit A I hI).app X)⟦q⟧' :=
    CategoryTheory.ObjectProperty.unit_comp_isoReflectionShift_hom
      (Dualizing.derivedCompleteProperty.{u, u} A I) (adicCompletionAdjunction A I hI) X q
  -- the commuting square
  have hsq : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((adicCompletionUnit A I hI).app (X⟦q⟧)) ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso e ≪≫
        Φ₀.app ((adicCompletionFunctor A I hI).obj X)).hom =
      (Φ₀.app X).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map
        ((adicCompletionUnit A I hI).app X) := by
    have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((adicCompletionUnit A I hI).app (X⟦q⟧)) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso e).hom =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (((adicCompletionUnit A I hI).app X)⟦q⟧') := by
      rw [Functor.mapIso_hom, ← Functor.map_comp]
      exact congrArg _ hunit
    refine Eq.trans ?_ (Φ₀.hom.naturality ((adicCompletionUnit A I hI).app X))
    rw [Iso.trans_hom, ← Category.assoc, h1]
    exact rfl
  refine range_sup_smul_eq_top_of_linearEquiv I _ _ (Φ₀.app X).toLinearEquiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso e ≪≫
      Φ₀.app ((adicCompletionFunctor A I hI).obj X)).toLinearEquiv) (fun m => ?_) h0
  exact congrArg (fun t : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X⟦q⟧) ⟶
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
      ((adicCompletionFunctor A I hI).obj X) => t.hom m) hsq

end Stacks.Algebraization

end
