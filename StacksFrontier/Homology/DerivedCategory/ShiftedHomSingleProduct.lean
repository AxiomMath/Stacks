module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Shifted morphisms into a countable product of modules

Let `R` be a ring and `L` an object of `D(R)`. For a countable product `N = ∏ Nᵢ` of
`R`-modules, the map `Hom_{D(R)}(L, N[n]) → ∏ Hom_{D(R)}(L, Nᵢ[n])` induced by the projections
is bijective: products of modules are exact, so the localization functor of `D(R)` preserves
them (Stacks 07KC), and so do the embedding of modules in degree zero and the shift.

## Main results

* `DerivedCategory.bijective_shiftedHom_single_comp_of_isLimit`: composition with the projections
  of a countable product `N = ∏ Nᵢ` of modules is a bijection
  `Hom_{D(R)}(L, N[n]) → ∏ Hom_{D(R)}(L, Nᵢ[n])`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace DerivedCategory

variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The embedding of `R`-modules in degree zero of `D(R)` preserves countable products. -/
instance preservesLimitsOfShape_singleFunctor_discrete_nat :
    PreservesLimitsOfShape (Discrete ℕ) (singleFunctor (ModuleCat.{u} R) 0) := by
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{u} R) (I := ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ) (CochainComplex.singleFunctor (ModuleCat.{u} R) 0) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0))
  have : PreservesLimitsOfShape (Discrete ℕ)
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ Q) := comp_preservesLimitsOfShape _ _
  exact preservesLimitsOfShape_of_natIso (singleFunctorIsoCompQ (ModuleCat.{u} R) 0).symm

/-- **Shifted morphisms into a countable product of modules.** For a limit fan `N → Nᵢ` of
`R`-modules indexed by `ℕ`, composition with the projections identifies
`Hom_{D(R)}(L, N[n])` with `∏ Hom_{D(R)}(L, Nᵢ[n])`. -/
theorem bijective_shiftedHom_single_comp_of_isLimit (L : DerivedCategory (ModuleCat.{u} R))
    (n : ℤ) {N : ModuleCat.{u} R} {F : ℕ → ModuleCat.{u} R} (π : ∀ i, N ⟶ F i)
    (hc : IsLimit (Fan.mk N π)) :
    Function.Bijective (fun y : ShiftedHom L ((singleFunctor (ModuleCat.{u} R) 0).obj N) n =>
      fun i => y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((singleFunctor (ModuleCat.{u} R) 0).map (π i)))
        (zero_add n)) := by
  let G := singleFunctor (ModuleCat.{u} R) 0 ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n
  have : PreservesLimitsOfShape (Discrete ℕ) G := comp_preservesLimitsOfShape _ _
  let hc' := isLimitFanMkObjOfIsLimit G F π hc
  have hfun : (fun y : ShiftedHom L ((singleFunctor (ModuleCat.{u} R) 0).obj N) n =>
      fun i => y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((singleFunctor (ModuleCat.{u} R) 0).map (π i)))
        (zero_add n)) = fun y i => y ≫ G.map (π i) := by
    funext y i
    exact ShiftedHom.comp_mk₀ y 0 rfl _
  rw [hfun]
  refine ⟨fun y y' h => Fan.IsLimit.hom_ext hc' _ _ fun i => congrFun h i, fun f => ?_⟩
  exact ⟨hc'.lift (Fan.mk L f), funext fun i => hc'.fac (Fan.mk L f) ⟨i⟩⟩

end DerivedCategory

end
