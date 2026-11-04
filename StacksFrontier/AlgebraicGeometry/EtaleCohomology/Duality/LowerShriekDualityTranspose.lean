module

public import StacksFrontier.CategoryTheory.Triangulated.HomologicalDualityPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekGlobalTranspose

/-!
# Compactly supported cohomology as a homological functor, on the base field or a compactification

Let `g : V → Spec k` have a compactification `j : V → X̄` with `π : X̄ → Spec k`, and `Λ = ℤ/N`.
The functors `M ↦ Hom_{D⁺(k)}(Λ_k[0], Rg_! M)` and `M ↦ Hom_{D⁺(X̄)}(Λ_X̄[0], Rj_! M)` on
`D⁺(V)` are isomorphic as functors to abelian groups
(`Stacks.EtaleCohomology.lowerShriekCoyonedaIso`), by the transpose
`Stacks.EtaleCohomology.unitHomEquivLowerShriek` of `π⁻¹ ⊣ Rπ_*`, which is additive
(`Stacks.EtaleCohomology.unitHomEquivLowerShriek_add`). Duality pairings for isomorphic
homological functors agree, for the transported trace
(`Stacks.HomologicalDuality.isPerfect_iff_of_natIso`). So Poincaré duality for complexes on `V`
can be read either over the base field, where the Leray isomorphism of a factorization
`g = q ∘ f` applies, or on the compactification, where it is Yoneda duality of sheaves; this is
used in the fibration step of Poincaré duality in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rg_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.unitHomAddEquivLowerShriek`.
* `Stacks.EtaleCohomology.lowerShriekCoyonedaIso`.

## Main results

* `Stacks.HomologicalDuality.isPerfect_iff_of_natIso`.
* `Stacks.EtaleCohomology.unitHomEquivLowerShriek_add`,
  `Stacks.EtaleCohomology.unitHomEquivLowerShriek_symm_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w v u u'

namespace Stacks.HomologicalDuality

variable {C : Type u'} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  {H H' : C ⥤ AddCommGrpCat.{w}} [H.Additive] [H'.Additive] (e : H ≅ H') (D : C) (N : ℤ)
  {A : Type*} [AddCommGroup A] (τ' : H'.obj (D⟦N⟧) →+ A)

/-- **Duality for isomorphic homological functors**: for `e : H ≅ H'`, duality holds at `M` for
`H` and the trace `τ' ∘ e` exactly when it holds for `H'` and `τ'`. -/
theorem isPerfect_iff_of_natIso (M : C) :
    IsPerfect H D N (τ'.comp (e.hom.app (D⟦N⟧)).hom) M ↔ IsPerfect H' D N τ' M := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun h => ?_
  let a := (e.app (M⟦i⟧)).addCommGroupIsoToAddEquiv
  refine bijective_iff_of_comp _ _ a a.bijective (AddMonoidHom.id _) Function.bijective_id
    (fun x y => ?_)
  show τ' ((shiftHom H' D N y i h).hom ((e.hom.app (M⟦i⟧)).hom x)) =
    τ' ((e.hom.app (D⟦N⟧)).hom ((shiftHom H D N y i h).hom x))
  rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, shiftHom, shiftHom,
    e.hom.naturality]

end Stacks.HomologicalDuality

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {k : Type u} [Field k] {V : Scheme.{u}} (g : V ⟶ Spec (.of k))
  (jc : CompactificationOf (Over.mk g)) (N : ℕ)

/-- **The transpose is additive.** -/
theorem unitHomEquivLowerShriek_add {M : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) V)}
    (φ₁ φ₂ : (DerivedCategory.Plus.singleFunctor _ 0).obj
        (ExtensionTorsor.unitSheaf (X := jc.space) N) ⟶
      (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj M) :
    unitHomEquivLowerShriek g jc N M (φ₁ + φ₂) =
      unitHomEquivLowerShriek g jc N M φ₁ + unitHomEquivLowerShriek g jc N M φ₂ := by
  have : (etaleModuleInverseImage.{u, 0} (ZMod N) jc.toBase).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  simp only [unitHomEquivLowerShriek, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Adjunction.homEquiv_unit, Preadditive.comp_add, Functor.map_add]

/-- The transpose `Hom(Λ_X̄[0], Rj_! M) ≃+ Hom(Λ_k[0], Rg_! M)` as an additive equivalence. -/
def unitHomAddEquivLowerShriek (M : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) V)) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (ExtensionTorsor.unitSheaf (X := jc.space) N) ⟶
        (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj M) ≃+
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N) ⟶
        (derivedLowerShriek.{u, 0} g jc (ZMod N)).obj M) :=
  { unitHomEquivLowerShriek g jc N M with
    map_add' := fun φ₁ φ₂ => unitHomEquivLowerShriek_add g jc N φ₁ φ₂ }

/-- The inverse transpose is natural. -/
theorem unitHomEquivLowerShriek_symm_comp
    {M M' : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) V)}
    (ψ : (DerivedCategory.Plus.singleFunctor _ 0).obj
        (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N) ⟶
      (derivedLowerShriek.{u, 0} g jc (ZMod N)).obj M) (u : M ⟶ M') :
    (unitHomEquivLowerShriek g jc N M').symm (ψ ≫ (derivedLowerShriek.{u, 0} g jc (ZMod N)).map u) =
      (unitHomEquivLowerShriek g jc N M).symm ψ ≫
        (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion).map u := by
  apply (unitHomEquivLowerShriek g jc N M').injective
  rw [unitHomEquivLowerShriek_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **`Hom(Λ_k[0], Rg_! -) ≅ Hom(Λ_X̄[0], Rj_! -)`** as functors `D⁺(V) ⥤ Ab`, by the transpose of
`π⁻¹ ⊣ Rπ_*`. -/
def lowerShriekCoyonedaIso :
    derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N))) ≅
      etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := jc.space) N))) :=
  NatIso.ofComponents (fun M => (unitHomAddEquivLowerShriek g jc N M).symm.toAddCommGrpIso)
    (fun {_ _} u => by
      ext ψ
      exact unitHomEquivLowerShriek_symm_comp g jc N ψ u)

end Stacks.EtaleCohomology

end
