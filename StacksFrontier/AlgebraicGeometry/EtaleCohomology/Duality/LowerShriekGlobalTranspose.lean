module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTraceExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor

/-!
# Classes on a compactification as classes over the base field

Let `g : W → Spec k` have a compactification `j : W → X̄` over `k`, with `π : X̄ → Spec k`, and let
`Λ = ℤ/N`. Since `Rg_! = Rπ_* ∘ Rj_!` and `π⁻¹ ⊣ Rπ_*` on bounded below derived categories
(`CategoryTheory.Adjunction.rightDerivedFunctorPlus`, `π⁻¹` being exact), with `π⁻¹ Λ = Λ`,
morphisms `Λ_X̄[0] ⟶ Rj_! M` correspond to morphisms `Λ_k[0] ⟶ Rg_! M`, naturally in `M`
(`Stacks.EtaleCohomology.unitHomEquivLowerShriek`,
`Stacks.EtaleCohomology.unitHomEquivLowerShriek_comp`).

This moves classes in `H^*_c(W) = Ext^*_X̄(Λ, j_! Λ)` to `D⁺(Spec k)`, where the Leray isomorphism
`Rg_! ≅ Rq_! ∘ Rf_!` of a factorization `g = q ∘ f` (Tag 0F7J) can be applied in degree zero, to
morphisms into shifted objects: the proof of the step of the class of a point through an
elementary fibration (proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) tests
nonvanishing this way, and never needs the Leray isomorphism to commute with shifts.

The statements consume `Rj_!` and `Rg_!`, defined in the standard model
`HasDerivedCategory.standard` of the derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.unitHomEquivLowerShriek`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {k : Type u} [Field k] {W : Scheme.{u}} (g : W ⟶ Spec (.of k))
  (jc : CompactificationOf (Over.mk g)) (N : ℕ)

/-- `π⁻¹(Λ_k[0]) ≅ Λ_X̄[0]` for the derived inverse image along `π : X̄ → Spec k`. -/
def derivedInverseImageUnitSingleIso :
    (etaleModuleInverseImage.{u, 0} (ZMod N) jc.toBase).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj (ExtensionTorsor.unitSheaf (X := jc.space) N) :=
  ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleInverseImage.{u, 0} (ZMod N) jc.toBase) 0).app _).symm ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) jc.toBase).app
        (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))

/-- **Morphisms `Λ_X̄[0] ⟶ Rj_! M` are morphisms `Λ_k[0] ⟶ Rg_! M`**, by `π⁻¹ ⊣ Rπ_*` and
`π⁻¹ Λ = Λ`. -/
def unitHomEquivLowerShriek (M : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) W)) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (ExtensionTorsor.unitSheaf (X := jc.space) N) ⟶
        (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj M) ≃
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N) ⟶
        (derivedLowerShriek.{u, 0} g jc (ZMod N)).obj M) :=
  haveI : (etaleModuleInverseImage.{u, 0} (ZMod N) jc.toBase).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Iso.homCongr (derivedInverseImageUnitSingleIso g jc N).symm (Iso.refl _)).trans
    (((etaleModuleInverseImageAdj.{u, 0} (ZMod N) jc.toBase).rightDerivedFunctorPlus).homEquiv
      _ _)

/-- **The correspondence is natural in `M`.** -/
theorem unitHomEquivLowerShriek_comp
    {M M' : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) W)}
    (φ : (DerivedCategory.Plus.singleFunctor _ 0).obj
        (ExtensionTorsor.unitSheaf (X := jc.space) N) ⟶
      (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj M) (u : M ⟶ M') :
    unitHomEquivLowerShriek g jc N M'
        (φ ≫ (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).map u) =
      unitHomEquivLowerShriek g jc N M φ ≫ (derivedLowerShriek.{u, 0} g jc (ZMod N)).map u := by
  have : (etaleModuleInverseImage.{u, 0} (ZMod N) jc.toBase).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  simp only [unitHomEquivLowerShriek, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id]
  rw [← Category.assoc]
  exact ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) jc.toBase).rightDerivedFunctorPlus
    ).homEquiv_naturality_right _ _

/-- **A class is zero exactly when its transpose is.** -/
theorem unitHomEquivLowerShriek_eq_zero_iff
    {M : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) W)}
    (φ : (DerivedCategory.Plus.singleFunctor _ 0).obj
        (ExtensionTorsor.unitSheaf (X := jc.space) N) ⟶
      (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj M) :
    unitHomEquivLowerShriek g jc N M φ = 0 ↔ φ = 0 := by
  have h0 : unitHomEquivLowerShriek g jc N M 0 = 0 := by
    simpa using unitHomEquivLowerShriek_comp g jc N 0 (0 : M ⟶ M)
  exact (unitHomEquivLowerShriek g jc N M).injective.eq_iff' h0

end Stacks.EtaleCohomology

end
