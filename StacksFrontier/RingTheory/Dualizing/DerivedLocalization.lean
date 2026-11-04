module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Derived extension of scalars to a localization

Extension of scalars along `R → T⁻¹R` is the localization functor on `R`-modules, and
localization is flat, so that functor is exact. Any model of its total left derived functor is
therefore isomorphic to the functor induced on derived categories by localization of modules.

## Main definitions

* `Dualizing.extendScalarsTensorIso`: extension of scalars along `algebraMap R S` sends `M` to
  `S ⊗[R] M`.
* `Dualizing.extendScalarsIsoLocalizedModuleFunctor`: extension of scalars along
  `R → T⁻¹R` is isomorphic to localization of modules at `T`.
* `Dualizing.localizationDerivedNatIso`: a model of total derived extension of scalars along
  `R → T⁻¹R` is isomorphic, as a functor, to the functor induced on derived categories by
  localization of modules at `T`.
* `Dualizing.localizationDerivedIso`: that isomorphism read at an object of the derived
  category.

## Main results

* `Dualizing.extendScalarsTensorIso_hom_tmul`: `Dualizing.extendScalarsTensorIso` sends
  `s ⊗ₜ m` to `s ⊗ₜ m`.
* `Dualizing.localizationDerivedIso_naturality`: the object-wise isomorphism is natural.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace Dualizing

universe u v wR wA

/-- Extension of scalars along `algebraMap R S` sends `M` to the base change `S ⊗[R] M`, with its
`S`-module structure. -/
def extendScalarsTensorIso {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] (M : ModuleCat.{max u v} R) :
    (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj M ≅
      ModuleCat.of S (S ⊗[R] M) := by
  haveI : SMulCommClass R S ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) :=
    ⟨fun r s t ↦ mul_left_comm (algebraMap R S r) s (t : S)⟩
  let e : ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[R] S :=
    { AddEquiv.refl S with
      map_smul' := fun r (s : S) => (Algebra.smul_def r s).symm }
  let E := TensorProduct.congr e (LinearEquiv.refl R M)
  refine LinearEquiv.toModuleIso { E.toAddEquiv with map_smul' := ?_ }
  intro s x
  change E (s • x) = s • E x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul a m =>
    change S at a
    change E ((s * a) ⊗ₜ[R, algebraMap R S] m) = s • E (a ⊗ₜ[R, algebraMap R S] m)
    simp only [E]
    rfl

/-- `Dualizing.extendScalarsTensorIso` sends `s ⊗ₜ m` to `s ⊗ₜ m`. -/
theorem extendScalarsTensorIso_hom_tmul {R : Type u} [CommRing R] (S : Type u)
    [CommRing S] [Algebra R S] (M : ModuleCat.{max u v} R) (s : S) (m : M) :
    (extendScalarsTensorIso.{u, v} S M).hom (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := by
  simp [extendScalarsTensorIso]
  rfl

/-- Extension of scalars along `R → T⁻¹R` is isomorphic, as a functor, to localization of modules
at `T`. -/
def extendScalarsIsoLocalizedModuleFunctor {R : Type u} [CommRing R] (T : Submonoid R) :
    ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization T)) ≅
      ModuleCat.localizedModuleFunctor.{max u v} T := by
  let S := Localization T
  let E (M : ModuleCat.{max u v} R) :=
    (IsLocalizedModule.isBaseChange T S (M.localizedModuleMkLinearMap T)).equiv
  refine NatIso.ofComponents
    (fun M => extendScalarsTensorIso.{u, v} S M ≪≫ (E M).toModuleIso) ?_
  intro M N f
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change E N ((extendScalarsTensorIso.{u, v} S N).hom
      ((1 : S) ⊗ₜ[R, algebraMap R S] (f.hom m))) =
    ((ModuleCat.localizedModuleFunctor T).map f).hom
      (E M ((extendScalarsTensorIso.{u, v} S M).hom ((1 : S) ⊗ₜ[R, algebraMap R S] m)))
  rw [extendScalarsTensorIso_hom_tmul, extendScalarsTensorIso_hom_tmul]
  simp only [E, IsBaseChange.equiv_tmul, one_smul]
  exact (IsLocalizedModule.map_apply T (M.localizedModuleMkLinearMap T)
    (N.localizedModuleMkLinearMap T) f.hom m).symm

/-- Any model of total derived extension of scalars along `R → T⁻¹R` is isomorphic, as a functor,
to the functor induced on derived categories by localization of modules at `T`. -/
def localizationDerivedNatIso {R : Type u} [CommRing R] (T : Submonoid R)
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} (Localization T))]
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u, wR, wA}
      (algebraMap R (Localization T))) :
    D.functor ≅ (ModuleCat.localizedModuleFunctor.{max u v} T).mapDerivedCategory := by
  let f := algebraMap R (Localization T)
  let F := ModuleCat.extendScalars.{u, u, max u v} f
  let G := ModuleCat.localizedModuleFunctor.{max u v} T
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' f
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization T) T))
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  letI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactors
  let comparison : DerivedCategory.Q ⋙ D.functor ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  have : D.functor.IsLeftDerivedFunctor comparison W := D.isLeftDerived
  let eFD : F.mapDerivedCategory ≅ D.functor :=
    Functor.leftDerivedUnique (LF := F.mapDerivedCategory) (LF' := D.functor)
      (α := F.mapDerivedCategoryFactors.hom) (α'₂ := comparison) (W := W)
  exact eFD.symm ≪≫
    mapDerivedCategoryNatIso F G (extendScalarsIsoLocalizedModuleFunctor.{u, v} T)

/-- Any model of total derived extension of scalars along `R → T⁻¹R` agrees, at every object of
the derived category, with the functor induced on derived categories by localization of modules
at `T`. -/
def localizationDerivedIso {R : Type u} [CommRing R] (T : Submonoid R)
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} (Localization T))]
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u, wR, wA}
      (algebraMap R (Localization T)))
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    D.functor.obj K ≅
      (ModuleCat.localizedModuleFunctor.{max u v} T).mapDerivedCategory.obj K :=
  (localizationDerivedNatIso.{u, v} T D).app K

/-- `Dualizing.localizationDerivedIso` is natural in the object of the derived category. -/
theorem localizationDerivedIso_naturality {R : Type u} [CommRing R] (T : Submonoid R)
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} (Localization T))]
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u, wR, wA}
      (algebraMap R (Localization T)))
    {K L : DerivedCategory (ModuleCat.{max u v} R)} (g : K ⟶ L) :
    D.functor.map g ≫ (localizationDerivedIso.{u, v} T D L).hom =
      (localizationDerivedIso.{u, v} T D K).hom ≫
        (ModuleCat.localizedModuleFunctor.{max u v} T).mapDerivedCategory.map g :=
  (localizationDerivedNatIso.{u, v} T D).hom.naturality g

end Dualizing

end
