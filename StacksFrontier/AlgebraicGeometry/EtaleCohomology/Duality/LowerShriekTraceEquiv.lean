module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekYonedaDuality

/-!
# Compactly supported cohomology over the base field, read in `Ext` on a compactification

Let `g : V → Spec k` have a compactification `j : V → X̄`, `Λ = ℤ/N` and `D₀` a sheaf of
`Λ`-modules on `V_ét`. The trace `Stacks.EtaleCohomology.lowerShriekTrace` on
`H_V(D₀[0][n]) = Hom_{D⁺(k)}(Λ_k[0], Rg_!(D₀[0])[n])` is a trace `t` on `Ext^n_X̄(Λ, j_! D₀)`
read through an additive equivalence `H_V(D₀[0][n]) ≃+ Ext^n_X̄(Λ, j_! D₀)`
(`Stacks.EtaleCohomology.lowerShriekTraceEquiv`): the transpose of `π⁻¹ ⊣ Rπ_*`,
`Rj_!(D₀[0]) ≅ (j_! D₀)[0]` and `Ext^n ≅ Hom_{D⁺}(-[0], -[0][n])`. Consequently

* every trace on `H_V(D₀[0][n])` is `lowerShriekTrace` of a trace on `Ext^n_X̄(Λ, j_! D₀)`,
  injective exactly when the given one is (`Stacks.EtaleCohomology.lowerShriekTrace_comp_symm`);
* `H_V(D₀[0][n])` vanishes as soon as `Ext^n_X̄(Λ, j_! D₀) = H^n_c(V, D₀)` does
  (`Stacks.EtaleCohomology.subsingleton_lowerShriek_shift`), for instance above twice the
  dimension of `X̄` ([Tag 095U](https://stacks.math.columbia.edu/tag/095U)).

The statements consume `Rg_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.lowerShriekTraceEquiv`.

## Main results

* `Stacks.HomologicalDuality.isIso_transferHom`.
* `Stacks.EtaleCohomology.lowerShriekTrace_eq_comp`.
* `Stacks.EtaleCohomology.lowerShriekTrace_comp_symm`.
* `Stacks.EtaleCohomology.subsingleton_lowerShriek_shift`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w v v' u₁ u₂ u

namespace Stacks.HomologicalDuality

variable {C : Type u₁} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  {C' : Type u₂} [Category.{v'} C'] [Preadditive C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (F : C ⥤ C') [F.CommShift ℤ] [F.Additive]
  {H : C ⥤ AddCommGrpCat.{w}} [H.Additive] {H' : C' ⥤ AddCommGrpCat.{w}} [H'.Additive]
  (e : H ≅ F ⋙ H') {D : C} {D' : C'} {c : ℤ} (θ : F.obj D ⟶ D'⟦c⟧) {N N' : ℤ}
  (hN : N + c = N')

omit [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Preadditive C']
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [F.Additive] [H.Additive] [H'.Additive] in
/-- **The transfer map `H(D[N]) ⟶ H'(D'[N'])` is an isomorphism when `θ` is.** -/
theorem isIso_transferHom [IsIso θ] : IsIso (transferHom F e θ hN) := by
  unfold transferHom
  infer_instance

end Stacks.HomologicalDuality

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {k : Type u} [Field k] {V : Scheme.{u}} (g : V ⟶ Spec (.of k))
  (jc : CompactificationOf (Over.mk g)) (N : ℕ) (D₀ : EtaleModules.{u, 0} (ZMod N) V) (n : ℕ)

/-- The comparison `Rj_!(D₀[0]) ⟶ (j_! D₀)[0][0]` through which `lowerShriekTrace` is defined is an
isomorphism. -/
theorem isIso_degreeZeroTheta_extensionByZero :
    IsIso (HomologicalDuality.degreeZeroTheta _ (isLE_extensionByZero_single g jc N)
      (isGE_extensionByZero_single g jc N) _ (extensionByZeroTopHomologyIso g jc N) D₀) := by
  unfold HomologicalDuality.degreeZeroTheta
  exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv ((shiftFunctorZero _ ℤ).app _))

/-- **`H^n_c(V, D₀)` over the base field as `Ext` on the compactification**: the additive
equivalence `Hom_{D⁺(k)}(Λ_k[0], Rg_!(D₀[0])[n]) ≃+ Ext^n_X̄(Λ, j_! D₀)` through which
`Stacks.EtaleCohomology.lowerShriekTrace` reads a trace. -/
def lowerShriekTraceEquiv :
    (derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N)))).obj
      (((DerivedCategory.Plus.singleFunctor _ 0).obj D₀)⟦(n : ℤ)⟧) ≃+
    Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n :=
  haveI := isIso_degreeZeroTheta_extensionByZero g jc N D₀
  haveI := HomologicalDuality.isIso_transferHom
    (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion)
    (H' := preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (ExtensionTorsor.unitSheaf (X := jc.space) N)))) (Iso.refl _)
    (HomologicalDuality.degreeZeroTheta _ (isLE_extensionByZero_single g jc N)
      (isGE_extensionByZero_single g jc N) _ (extensionByZeroTopHomologyIso g jc N) D₀)
    (add_zero (n : ℤ))
  ((lowerShriekCoyonedaIso g jc N).app _).addCommGroupIsoToAddEquiv.trans
    ((asIso (HomologicalDuality.transferHom
      (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion)
      (H' := preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (ExtensionTorsor.unitSheaf (X := jc.space) N)))) (Iso.refl _)
      (HomologicalDuality.degreeZeroTheta _ (isLE_extensionByZero_single g jc N)
        (isGE_extensionByZero_single g jc N) _ (extensionByZeroTopHomologyIso g jc N) D₀)
      (add_zero (n : ℤ)))).addCommGroupIsoToAddEquiv.trans
      (HomologicalDuality.extPlusAddEquiv _ _ n).symm)

/-- **`lowerShriekTrace` is the trace read through `lowerShriekTraceEquiv`.** -/
theorem lowerShriekTrace_eq_comp
    (t : Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n →+ ZMod N) :
    lowerShriekTrace g jc N D₀ n t = t.comp (lowerShriekTraceEquiv g jc N D₀ n).toAddMonoidHom := by
  ext x
  rfl

/-- **Every trace on `H_V(D₀[0][n])` comes from a trace on `Ext^n_X̄(Λ, j_! D₀)`**: `τ` is
`lowerShriekTrace` of `τ` read back through `lowerShriekTraceEquiv`. -/
theorem lowerShriekTrace_comp_symm
    (τ : (derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N)))).obj
      (((DerivedCategory.Plus.singleFunctor _ 0).obj D₀)⟦(n : ℤ)⟧) →+ ZMod N) :
    lowerShriekTrace g jc N D₀ n
      (τ.comp (lowerShriekTraceEquiv g jc N D₀ n).symm.toAddMonoidHom) = τ := by
  rw [lowerShriekTrace_eq_comp]
  ext x
  simp

/-- **`H_V(D₀[0][n])` vanishes when `H^n_c(V, D₀) = Ext^n_X̄(Λ, j_! D₀)` does.** -/
theorem subsingleton_lowerShriek_shift
    (h : Subsingleton (Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n)) :
    Subsingleton ((derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N)))).obj
      (((DerivedCategory.Plus.singleFunctor _ 0).obj D₀)⟦(n : ℤ)⟧)) :=
  (lowerShriekTraceEquiv g jc N D₀ n).toEquiv.subsingleton

end Stacks.EtaleCohomology

end
