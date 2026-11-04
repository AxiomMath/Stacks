module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Base change along an open immersion for sheaves of modules, at every coefficient universe

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

attribute [-instance] Stacks.EtaleCohomology.etaleAbelianDirectImage_additive

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type w) [Ring Λ]

/-- **Base change along an open immersion for sheaves of modules**, at every coefficient
universe: for a cartesian square with `g` an open immersion and `f` arbitrary, the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` is an isomorphism for every `K ∈ D⁺(X_étale, Λ)`. It is read
on a bounded below complex of injectives representing `K`, where it is the abelian base change map
along the open immersion
(`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion`)
at the underlying complex of abelian sheaves. -/
theorem isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    [IsOpenImmersion g] (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ X)) :
    IsIso ((etaleModuleDerivedBaseChange.{u, w} Λ f f' g g' sq.w.symm).app K) := by
  have := etaleModules_enoughInjectives.{u, w} Λ X
  have := etaleModules_enoughInjectives.{u, w} Λ X'
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
  obtain ⟨L₀, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  obtain ⟨I, hI, ⟨e'⟩⟩ : ∃ (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X))
      (_ : ∀ m, Injective (I.obj.X m)),
      Nonempty (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I) ≅ K) :=
    ⟨(InjectiveObject.ι (EtaleModules.{u, w} Λ X)).mapCochainComplexPlus.obj L₀,
      fun m => (L₀.obj.X m).property,
      ⟨Functor.preimageIso (F := DerivedCategory.Plus.ι)
        (X := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          ((InjectiveObject.ι (EtaleModules.{u, w} Λ X)).mapCochainComplexPlus.obj L₀)))
        (Y := DerivedCategory.Plus.Q.obj
          ((InjectiveObject.ι (EtaleModules.{u, w} Λ X)).mapCochainComplexPlus.obj L₀))
        ((DerivedCategory.quotientCompQhIso _).app _) ≪≫ e⟩⟩
  refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
  obtain ⟨n₁, hn₁⟩ := ((etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I).property
  obtain ⟨L₁, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ((etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I) n₁
  obtain ⟨L, hL, i', hi'⟩ : ∃ (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X'))
      (_ : ∀ m, Injective (L.obj.X m))
      (i' : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L),
      QuasiIso i'.hom :=
    ⟨(InjectiveObject.ι (EtaleModules.{u, w} Λ X')).mapCochainComplexPlus.obj L₁,
      fun m => (L₁.obj.X m).property, i, hi⟩
  have := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, w} f g g' f' sq
  exact isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange.{u, w} Λ f sq
    I L i' hi' inferInstance

end Stacks.EtaleCohomology

end
