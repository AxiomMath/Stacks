module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeOfQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleBaseChangeFromAbelian

/-!
# The unbounded abelian base change map from the bounded below one

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes and `K` a bounded below complex of abelian sheaves on `X_étale`
with `f_*`-acyclic terms. The base change map `g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` exists on the bounded below
derived categories (`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, through which the base
change maps on higher direct images `Stacks.EtaleCohomology.higherBaseChangeMapAb` are defined)
and on the unbounded ones (`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, Stacks 0A2A).
If the first is invertible at `K`, so is the second: choosing a quasi-isomorphism
`g'⁻¹ K ⟶ L` onto a bounded below complex of injectives, both are invertible exactly when the
degreewise comparison `g⁻¹ f_* K ⟶ f'_* g'⁻¹ K ⟶ f'_* L` is a quasi-isomorphism
(`Stacks.Cohomology.BaseChange.isIso_Q_map_comp_of_isIso_derived` and
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isIso_Q_map_comp`), and the two
underived comparisons agree up to the identification of the two inverse images
(`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero`).

The coefficient universe of the unbounded statement is that of the sheaves of `ℤ/N`-modules,
`AddCommGrpCat.{max (u + 1) 0}`, so that it can be fed to the comparison with sheaves of modules
(`isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange`, in the namespace
`Stacks.EtaleCohomology`).

The statements are made in the standard model `HasDerivedCategory.standard`, in which both base
change maps are stated.

## Main results

* `isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb`: if the bounded
  below base change map is invertible at `K`, so is the unbounded one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (w : g' ≫ f = f' ≫ g)

/-- **The unbounded abelian base change map from the bounded below one.** Let `K` be a bounded
below complex of abelian sheaves on `X_étale` with `f_*`-acyclic terms. If the base change map
`g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` of the bounded below derived categories is invertible at `K`, so is the
one of the unbounded derived categories, with coefficients in `AddCommGrpCat.{max (u + 1) 0}`. -/
theorem isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb
    (K : CochainComplex.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hK : ∀ n : ℤ, (smallEtalePushforwardAb f).rightAcyclic (K.obj.X n))
    (hbc : IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' w.symm).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj K)))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K.obj))) := by
  obtain ⟨n₁, hn₁⟩ := ((smallEtalePullbackAb g').mapCochainComplexPlus.obj K).property
  obtain ⟨L₁, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ((smallEtalePullbackAb g').mapCochainComplexPlus.obj K) n₁
  -- a resolution of `g'⁻¹ K` by a bounded below complex of injectives, as opaque variables
  obtain ⟨L, hL, i', hi'⟩ : ∃ (L : CochainComplex.Plus (Sheaf (smallEtaleTopology X') Ab.{u + 1}))
      (_ : ∀ m, Injective (L.obj.X m))
      (i' : (smallEtalePullbackAb g').mapCochainComplexPlus.obj K ⟶ L), QuasiIso i'.hom :=
    ⟨(InjectiveObject.ι (Sheaf (smallEtaleTopology X') Ab.{u + 1})).mapCochainComplexPlus.obj L₁,
      fun m => (L₁.obj.X m).property, i, hi⟩
  have hL' : ∀ n : ℤ, (smallEtalePushforwardAb f').rightAcyclic (L.obj.X n) := fun n => by
    have := hL n
    exact Functor.rightAcyclic_of_injective _ _
  have hys := Stacks.Cohomology.BaseChange.isIso_Q_map_comp_of_isIso_derived
    (smallEtalePushforwardAb f) (smallEtalePushforwardAb f') (smallEtalePullbackAb g)
    (smallEtalePullbackAb g') (smallEtaleBaseChangeAb g f f' g' w.symm)
    (asIso (smallEtalePullbackAb g).rightDerivedFunctorPlusUnit) K hK L hL' i' hi' hbc
  exact isIso_etaleAbelianDerivedBaseChange_app_of_isIso_Q_map_conj_comp.{u, 0} f g g' f' w
    (smallEtalePullbackAb g) (smallEtalePullbackAb g') (smallEtalePullbackAbIsoInverseImage g)
    (smallEtalePullbackAbIsoInverseImage g') (smallEtaleBaseChangeAb g f f' g' w.symm)
    (smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero g f f' g' w.symm) K.obj K.property hK
    L.obj L.property hL' i'.hom hi' hys

end Stacks.EtaleCohomology

end
