module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.PlusToUnboundedBaseChange

/-!
# The base change map for a sheaf of modules from the abelian one

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes, `Λ` a ring and `M` a sheaf of `Λ`-modules on `X_étale`. If the
abelian base change map `g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` of the bounded below derived categories
(`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, through which the base change maps on
higher direct images `Stacks.EtaleCohomology.higherBaseChangeMapAb` are defined) is invertible at
the underlying abelian sheaf of `M` placed in degree zero, then the base change map of sheaves of
`Λ`-modules (`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`) is invertible at `M[0]`.

Represent `M[0]` by a bounded below complex `I` of injective sheaves of modules. The underlying
complex of abelian sheaves of `I` represents the underlying abelian sheaf of `M`, and its terms are
acyclic for direct images; so the unbounded abelian base change map is invertible at it
(`isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb`), and the module
base change map is invertible at `I`
(`isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange`). All names are
in the namespace `Stacks.EtaleCohomology`.

The statements are made in the standard model `HasDerivedCategory.standard`, in which both base
change maps are stated.

## Main results

* `isIso_etaleModuleDerivedBaseChange_app_single_of_isIso_smallEtaleDerivedBaseChangeAb`: if the
  abelian base change map is invertible at the underlying abelian sheaf of `M` in degree zero, the
  module base change map is invertible at `M[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-- **The module base change map at `M[0]` from the abelian one.** Let the square be cartesian.
If the abelian base change map of the bounded below derived categories is invertible at the
underlying abelian sheaf of `M` placed in degree zero, the module base change map
`g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` is invertible at `M[0]`. -/
theorem isIso_etaleModuleDerivedBaseChange_app_single_of_isIso_smallEtaleDerivedBaseChangeAb
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (M : EtaleModules.{u, 0} Λ X)
    (hbc : IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' sq.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) 0).obj
        ((etaleModuleForgetAb.{u, 0} Λ X).obj M)))) :
    IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' sq.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)) := by
  have := etaleModules_enoughInjectives.{u, 0} Λ X
  have := etaleModules_enoughInjectives.{u, 0} Λ X'
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M
  obtain ⟨L₀, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K 0
  -- a bounded below complex of injectives representing `M[0]`, as an opaque variable
  obtain ⟨I, hI, ⟨e'⟩⟩ : ∃ (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
      (_ : ∀ m, Injective (I.obj.X m)),
      Nonempty (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I) ≅ K) :=
    ⟨(InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapCochainComplexPlus.obj L₀,
      fun m => (L₀.obj.X m).property,
      ⟨Functor.preimageIso (F := DerivedCategory.Plus.ι)
        (X := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          ((InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapCochainComplexPlus.obj L₀)))
        (Y := DerivedCategory.Plus.Q.obj
          ((InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapCochainComplexPlus.obj L₀))
        ((DerivedCategory.quotientCompQhIso _).app _) ≪≫ e⟩⟩
  refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
  obtain ⟨n₁, hn₁⟩ := ((etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I).property
  obtain ⟨L₁, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ((etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I) n₁
  -- a resolution of `(g')⁻¹ I` by a bounded below complex of injectives, as opaque variables
  obtain ⟨L, hL, i', hi'⟩ : ∃ (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X'))
      (_ : ∀ m, Injective (L.obj.X m))
      (i' : (etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I ⟶ L),
      QuasiIso i'.hom :=
    ⟨(InjectiveObject.ι (EtaleModules.{u, 0} Λ X')).mapCochainComplexPlus.obj L₁,
      fun m => (L₁.obj.X m).property, i, hi⟩
  let U := etaleModuleForgetAb.{u, 0} Λ X
  let eA : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
      (U.mapCochainComplexPlus.obj I)) ≅
      (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) 0).obj
        (U.obj M) :=
    (U.mapDerivedCategoryPlusFactorsh.app ((HomotopyCategory.Plus.quotient _).obj I)).symm ≪≫
      U.mapDerivedCategoryPlus.mapIso e' ≪≫ U.mapDerivedCategoryPlusObjSingleIso M
  exact isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange.{u, 0} Λ f sq
    I L i' hi' (isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb
      f g g' f' sq.w (U.mapCochainComplexPlus.obj I)
      (fun n => rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj.{u, 0} Λ f
        (I.obj.X n))
      ((NatTrans.isIso_app_iff_of_iso _ eA).2 hbc))

end Stacks.EtaleCohomology

end
