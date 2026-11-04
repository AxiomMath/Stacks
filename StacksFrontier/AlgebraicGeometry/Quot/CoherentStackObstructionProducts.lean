module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDualGroups
public import StacksFrontier.Homology.DerivedCategory.ShiftedHomSingleProduct

/-!
# The Ext groups of an object of `Coh_{X/B}` commute with countable products

Let `x = (T, g, ℱ)` be an object of `Coh_{X/Y}` (Stacks 08KB) over a Noetherian affine test
scheme `T`, whose ring of global functions is identified with a ring `A`. Part (B) of Stacks
08JR identifies `Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃)` with `Hom_{D(A)}(L, M[n])` for a pseudo-coherent `L`,
naturally in the `A`-module `M`
(`AlgebraicGeometry.Space.CoherentSituation.exists_isPseudoCoherentFrom_extEquiv`). The latter
commutes with countable products in `M`, so the former does. This is the input of the second
proof of Stacks 08WA for assumption (5) of Stacks 0CYF.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.extShiftedHomEquiv`: the identification
  `Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃) ≃ Hom_{D(A)}(L, M[n])` given by data of 08JR(B).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.bijective_extGroupMap_pi`: the map
  `Ext^n_{X_T}(ℱ, ℱ ⊗ f^*(∏ Mₖ)~) → ∏ Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃ₖ)` induced by the projections is
  bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] pointTopology

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
variable (x : CoherentObject D) [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
variable {A : Type u} [CommRing A] (e : A ≃+* D.baseRing x)

section Data

variable (L : DerivedCategory (ModuleCat.{u} (D.baseRing x)))
  (Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
        ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
          (D.singleComplex x)
          ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
            ((representedAffineAssociated B S hS x.T.left).obj N))) i)

/-- **`Ext^n_{X_T}(ℱ, ℱ ⊗ f^*M̃) ≃ Hom_{D(A)}(L, M[n])`**, from data of part (B) of Stacks 08JR. -/
def extShiftedHomEquiv (M : ModuleCat.{u} A) (i : ℤ) :
    D.extGroup x e M i ≃+ ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj
      (D.baseModule x e M)) i :=
  (D.extGroupEquiv x e M i).trans (Ξ (D.baseModule x e M) i).symm

variable {L Ξ}

/-- The identification `extShiftedHomEquiv` carries the map induced by a module map to
composition with that map. -/
theorem extShiftedHomEquiv_extGroupMap
    (hΞnat : ∀ {N N' : ModuleCat.{u} (D.baseRing x)}
      (g : N ⟶ N') (i : ℤ) (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
      Ξ N' i (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
        Ξ N i y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
          (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧')
    {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ) (c : D.extGroup x e M i) :
    D.extShiftedHomEquiv x e L Ξ N i (D.extGroupMap x e g i c) =
      (D.extShiftedHomEquiv x e L Ξ M i c).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((DerivedCategory.singleFunctor _ 0).map
          ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g)))
        (zero_add i) := by
  apply (Ξ (D.baseModule x e N) i).injective
  simp only [extShiftedHomEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, extGroupMap_apply]
  rw [hΞnat, AddEquiv.apply_symm_apply]

/-- **The Ext groups commute with countable products**, from data of part (B) of Stacks 08JR. -/
theorem bijective_extGroupMap_pi_of_data
    (hΞnat : ∀ {N N' : ModuleCat.{u} (D.baseRing x)}
      (g : N ⟶ N') (i : ℤ) (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
      Ξ N' i (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
        Ξ N i y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
          (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧')
    (M : ℕ → ModuleCat.{u} A) (i : ℤ) :
    Function.Bijective (fun (c : D.extGroup x e (ModuleCat.of A (∀ n, (M n : Type u))) i) n =>
      D.extGroupMap x e (ModuleCat.ofHom (LinearMap.proj n) :
        ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) i c) := by
  let T := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor
  have hc : IsLimit (Fan.mk (T.obj (ModuleCat.of A (∀ n, (M n : Type u))))
      (fun n => T.map (ModuleCat.ofHom (LinearMap.proj n) :
        ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n))) :=
    isLimitFanMkObjOfIsLimit T M _ (ModuleCat.HasLimit.productLimitCone M).isLimit
  have hb := DerivedCategory.bijective_shiftedHom_single_comp_of_isLimit L i _ hc
  have hfun : (fun (c : D.extGroup x e (ModuleCat.of A (∀ n, (M n : Type u))) i) n =>
      D.extGroupMap x e (ModuleCat.ofHom (LinearMap.proj n) :
        ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) i c) =
      (fun y n => (D.extShiftedHomEquiv x e L Ξ (M n) i).symm (y n)) ∘
        (fun y n => y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map (T.map (ModuleCat.ofHom (LinearMap.proj n) :
            ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n)))) (zero_add i)) ∘
        (D.extShiftedHomEquiv x e L Ξ (ModuleCat.of A (∀ n, (M n : Type u))) i) := by
    funext c n
    simp only [Function.comp_apply]
    rw [← D.extShiftedHomEquiv_extGroupMap x e hΞnat, AddEquiv.symm_apply_apply]
  rw [hfun]
  exact (Equiv.piCongrRight fun n =>
      (D.extShiftedHomEquiv x e L Ξ (M n) i).symm.toEquiv).bijective.comp
    (hb.comp (D.extShiftedHomEquiv x e L Ξ _ i).bijective)

end Data

/-- **The Ext groups of an object of `Coh_{X/B}` over a Noetherian affine base commute with
countable products.** For `A`-modules `Mₙ`, the map
`Ext^i_{X_T}(ℱ, ℱ ⊗ f^*(∏ Mₙ)~) → ∏ Ext^i_{X_T}(ℱ, ℱ ⊗ f^*M̃ₙ)` induced by the projections is
bijective. -/
theorem bijective_extGroupMap_pi [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)]
    (M : ℕ → ModuleCat.{u} A) (i : ℤ) :
    Function.Bijective (fun (c : D.extGroup x e (ModuleCat.of A (∀ n, (M n : Type u))) i) n =>
      D.extGroupMap x e (ModuleCat.ofHom (LinearMap.proj n) :
        ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) i c) := by
  have hX := D.exists_isPseudoCoherentFrom_extEquiv x
  exact D.bijective_extGroupMap_pi_of_data x e (L := hX.choose) (Ξ := hX.choose_spec.2.choose)
    hX.choose_spec.2.choose_spec.1 M i

end CoherentSituation

end AlgebraicGeometry.Space

end
