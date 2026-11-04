module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleCohomologySpectralSequence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModulePullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleDerivedGlobalSections
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# The cohomology spectral sequence of a module pulled back along a ringed augmentation

Let `S` be a simplicial-site situation (Stacks 09WE) and let
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` be a ringed augmentation of it towards a ringed site
(Stacks 0D9D), with component morphisms `a_p = a ∘ g_p : (Sh(C_p), O_p) ⟶ (Sh(D), O_D)`. For a
sheaf of `O_D`-modules `F` the spectral sequence of Stacks 0D7E, applied to `a^*F` placed in
degree zero, has first page

`E_1^{p,q} = H^q(C_p, a_p^*F)`,

since the restriction of `a^*F` to the component `C_p` is `a_p^*F`, and it converges to
`H^{p+q}(C_total, a^*F)`. If moreover cohomology of `F` on `D` agrees with cohomology of `a^*F` on
the total site, `H^n(D, F) = H^n(C_total, a^*F)` for every `n` — for instance when `a` is an fppf
hypercovering of algebraic spaces and `F` is quasi-coherent, which is Stacks 0DHG — then the
spectral sequence converges to `H^{p+q}(D, F)`. This is the deduction of Stacks 0DHH from
Stacks 0DHG and Stacks 0D7E, carried out for an arbitrary ringed augmentation.

## Main definitions

All names below are in the namespace `CategoryTheory.SimplicialSiteSituation`.

* `RingedAugmentation.pullbackSpectralSequence`: the spectral sequence, as a functor of the sheaf
  of `O_D`-modules `F`.
* `RingedAugmentation.pullbackSpectralSequencePageOneIso`: its first page
  `E_1^{p,q} = H^q(C_p, a_p^*F)`, naturally in `F`.

## Main results

* `RingedAugmentation.isZero_pullbackSpectralSequence_page_one`: the first page vanishes outside
  the first quadrant.
* `RingedAugmentation.abutsTo_pullbackSpectralSequence_total`: convergence to
  `H^{p+q}(C_total, a^*F)`.
* `RingedAugmentation.abutsTo_pullbackSpectralSequence`: convergence to `H^{p+q}(D, F)` when
  `H^n(D, F) ≅ H^n(C_total, a^*F)` for all `n`.

## Implementation notes

Cohomology `H^q(C, -)` of a sheaf of modules is the `q`-th right derived functor, in Mathlib's
sense, of global sections of the underlying abelian sheaf,
`AlgebraicGeometry.RingedTopos.moduleGlobalSections`, so that no model of the derived category
enters the statements. The abutment is indexed by all integers and is zero in negative degrees.

## References

* [Stacks Project, Tag 0D7E](https://stacks.math.columbia.edu/tag/0D7E)
* [Stacks Project, Tag 0D9D](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 0DHG](https://stacks.math.columbia.edu/tag/0DHG)
* [Stacks Project, Tag 0DHH](https://stacks.math.columbia.edu/tag/0DHH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

universe u

namespace Stacks.DerivedIndexing

attribute [local instance] HasDerivedCategory.standard

/-- **`H^n(RG(M[0])) = R^nG(M)`**: the cohomology of the right derived functor on the bounded
below derived category at an object placed in degree zero is Mathlib's right derived functor in
non-negative degrees, and zero in negative degrees. -/
def homologyRightDerivedFunctorPlusSingleIso {C : Type*} [Category* C] [Abelian C]
    [EnoughInjectives C] (G : C ⥤ AddCommGrpCat.{u}) [G.Additive] (M : C) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)) ≅
      if 0 ≤ n then (G.rightDerived n.toNat).obj M else AddCommGrpCat.of PUnit.{u + 1} := by
  haveI := Functor.isGE_rightDerivedFunctorPlus_obj G
    ((DerivedCategory.Plus.singleFunctor C 0).obj M) 0
  split_ifs with hn
  · exact eqToIso (congrArg (fun k => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} k).obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)))
        (Int.toNat_of_nonneg hn).symm) ≪≫
      ((rightDerivedIso G n.toNat).app M).symm
  · exact IsZero.iso (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n (by omega))
      (AddCommGrpCat.isZero_of_subsingleton _)

end Stacks.DerivedIndexing

namespace CategoryTheory.SimplicialSiteSituation

variable {S : SimplicialSiteSituation.{u}}

/-- **Restriction of sheaves of modules to a simplicial component is exact**: it is left exact
as a pushforward along a continuous functor, and right exact because the component inclusion is
cocontinuous. -/
theorem componentModuleRestriction_exact (O : Sheaf S.totalTopology RingCat.{u})
    (p : SimplexCategory) :
    PreservesFiniteLimits (componentModuleRestriction S O p) ∧
      PreservesFiniteColimits (componentModuleRestriction S O p) := by
  open Stacks.SheafOfModules.PushforwardRightExact in
  constructor
  · unfold componentModuleRestriction
    infer_instance
  · unfold componentModuleRestriction
    exact preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
      (componentFunctor S p) _ (isAlmostCocontinuous_of_isCocontinuous _ _ _)

/-- Restriction of sheaves of modules to the component `C_p` is an additive functor. -/
local instance (O : Sheaf S.totalTopology RingCat.{u}) (p : SimplexCategory) :
    (componentModuleRestriction S O p).Additive := ⟨rfl⟩

/-- Restriction of sheaves of modules to the component `C_p` preserves finite limits. -/
local instance (O : Sheaf S.totalTopology RingCat.{u}) (p : SimplexCategory) :
    PreservesFiniteLimits (componentModuleRestriction S O p) :=
  (componentModuleRestriction_exact O p).1

/-- Restriction of sheaves of modules to the component `C_p` preserves finite colimits. -/
local instance (O : Sheaf S.totalTopology RingCat.{u}) (p : SimplexCategory) :
    PreservesFiniteColimits (componentModuleRestriction S O p) :=
  (componentModuleRestriction_exact O p).2

attribute [local instance] HasDerivedCategory.standard

/-- **`H^q(C_p, K_p)` at an object placed in degree zero.** For a sheaf of `O`-modules `M` on the
total site, the `q`-th cohomology of `RΓ(C_p, (M[0])_p)` is `H^q(C_p, M|_{C_p})`, naturally in
`M`: restriction to the component is exact, so it commutes with placing in degree zero. -/
def singleComponentCohomologyIso (O : Sheaf S.totalTopology RingCat.{u}) (p q : ℕ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
      ((componentModuleRestriction S O ⦋p⦌).mapDerivedCategoryPlus ⋙
        (SheafOfModules.toSheaf (componentRingSheaf S O ⦋p⦌) ⋙
          Sheaf.Γ (S.componentTopology ⦋p⦌) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (q : ℤ)) ≅
      componentModuleRestriction S O ⦋p⦌ ⋙
        (SheafOfModules.toSheaf (componentRingSheaf S O ⦋p⦌) ⋙
          Sheaf.Γ (S.componentTopology ⦋p⦌) AddCommGrpCat.{u}).rightDerived q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (componentModuleRestriction S O ⦋p⦌) 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.DerivedIndexing.rightDerivedIso _ q).symm

namespace RingedAugmentation

variable {D : Cat.{u, u}} {K : GrothendieckTopology D} {a : Augmentation S D K}
  (A : RingedAugmentation S D K a)

/-- **The spectral sequence of a module pulled back along a ringed augmentation**, as a functor
of the sheaf of `O_D`-modules `F`: the spectral sequence of Stacks 0D7E for the pullback `a^*F`
placed in degree zero. -/
def pullbackSpectralSequence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O) ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u} 1 :=
  A.totalRingedHom.toModulesHom.pullbackModules ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
      moduleCohomologySpectralSequence S
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O)

/-- The first page of `pullbackSpectralSequence`, read through the identification of the first
page of Stacks 0D7E. -/
def pullbackSpectralSequencePageOneIsoAux (p q : ℕ) :
    pullbackSpectralSequence A ⋙
        (CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u} _ ((p : ℤ), (q : ℤ))) ≅
      A.totalRingedHom.toModulesHom.pullbackModules ⋙
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      ((componentModuleRestriction S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O)
          ⦋p⦌).mapDerivedCategoryPlus ⋙
        (SheafOfModules.toSheaf (componentRingSheaf S
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⦋p⦌) ⋙
          Sheaf.Γ (S.componentTopology ⦋p⦌) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (q : ℤ))) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft A.totalRingedHom.toModulesHom.pullbackModules
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          (moduleCohomologySpectralSequencePageOneIso S
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) p q))

/-- **`E_1^{p,q} = H^q(C_p, a_p^*F)`, naturally in `F`.** The restriction of `a^*F` to the
component `C_p` is the pullback `a_p^*F` along the component morphism `a_p = a ∘ g_p` of
Stacks 0D9D. -/
def pullbackSpectralSequencePageOneIso (p q : ℕ) :
    pullbackSpectralSequence A ⋙
        (CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u} _ ((p : ℤ), (q : ℤ))) ≅
      (A.componentRingedHom ⦋p⦌).toModulesHom.pullbackModules ⋙
        (S.componentRingedTopos A.O ⦋p⦌).moduleGlobalSections.rightDerived q :=
  pullbackSpectralSequencePageOneIsoAux A p q ≪≫
    Functor.isoWhiskerLeft A.totalRingedHom.toModulesHom.pullbackModules
      (singleComponentCohomologyIso _ p q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((A.componentPullbackModulesIso ⦋p⦌ ≪≫
      Functor.isoWhiskerLeft _ (componentPullbackModulesRestrictionIso S A.O ⦋p⦌)).symm) _

/-- **The first page vanishes outside the first quadrant.** In negative columns this is the
vanishing of Stacks 0D7E; in negative rows the cohomology of a module placed in degree zero
vanishes. -/
theorem isZero_pullbackSpectralSequence_page_one
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O))
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((((pullbackSpectralSequence A).obj F).page 1 le_rfl).X (p, q)) := by
  by_cases hp : p < 0
  · exact isZero_moduleCohomologySpectralSequence_page_one S
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) _ p q hp
  · have hq : q < 0 := h.resolve_left hp
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hp)
    let X := A.totalRingedHom.toModulesHom.pullbackModules.obj F
    refine IsZero.of_iso ?_ ((moduleCohomologySpectralSequencePageOneIso S
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) m q).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj X))
    refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).mapIso
      ((SheafOfModules.toSheaf (componentRingSheaf S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⦋m⦌) ⋙
        Sheaf.Γ (S.componentTopology ⦋m⦌) AddCommGrpCat.{u}).rightDerivedFunctorPlus.mapIso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (componentModuleRestriction S
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⦋m⦌) 0).app X)))
    have : ((componentModuleRestriction S
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⦋m⦌ ⋙
        DerivedCategory.Plus.singleFunctor _ 0).obj X).IsGE 0 :=
      (inferInstance : ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((componentModuleRestriction S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O)
          ⦋m⦌).obj X)).IsGE 0)
    have := Functor.isGE_rightDerivedFunctorPlus_obj
      (SheafOfModules.toSheaf (componentRingSheaf S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⦋m⦌) ⋙
        Sheaf.Γ (S.componentTopology ⦋m⦌) AddCommGrpCat.{u})
      ((componentModuleRestriction S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⦋m⦌ ⋙
        DerivedCategory.Plus.singleFunctor _ 0).obj X) 0
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq

/-- **The spectral sequence converges to `H^{p+q}(C_total, a^*F)`**, by Stacks 0D7E. -/
theorem abutsTo_pullbackSpectralSequence_total
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O)) :
    CategoryTheory.SpectralSequence.AbutsTo ((pullbackSpectralSequence A).obj F)
      (fun n => if 0 ≤ n then
        ((S.totalRingedTopos A.O).moduleGlobalSections.rightDerived n.toNat).obj
          (A.totalRingedHom.toModulesHom.pullbackModules.obj F)
        else AddCommGrpCat.of PUnit.{u + 1}) :=
  (abutsTo_moduleCohomologySpectralSequence S
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (A.totalRingedHom.toModulesHom.pullbackModules.obj F))).of_iso fun n =>
    Stacks.DerivedIndexing.homologyRightDerivedFunctorPlusSingleIso _ _ n

/-- **The spectral sequence converges to `H^{p+q}(D, F)`** as soon as cohomology of `F` on `D`
is cohomology of `a^*F` on the total site, `H^n(D, F) ≅ H^n(C_total, a^*F)` for every `n`. -/
theorem abutsTo_pullbackSpectralSequence
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O))
    (h : ∀ n : ℕ, Nonempty ((A.augmentationRingedTopos.moduleGlobalSections.rightDerived n).obj F ≅
      ((S.totalRingedTopos A.O).moduleGlobalSections.rightDerived n).obj
        (A.totalRingedHom.toModulesHom.pullbackModules.obj F))) :
    CategoryTheory.SpectralSequence.AbutsTo ((pullbackSpectralSequence A).obj F)
      (fun n => if 0 ≤ n then
        (A.augmentationRingedTopos.moduleGlobalSections.rightDerived n.toNat).obj F
        else AddCommGrpCat.of PUnit.{u + 1}) :=
  (abutsTo_pullbackSpectralSequence_total A F).of_nonempty_iso fun n => by
    split_ifs
    · exact ⟨(h n.toNat).some.symm⟩
    · exact ⟨Iso.refl _⟩

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
