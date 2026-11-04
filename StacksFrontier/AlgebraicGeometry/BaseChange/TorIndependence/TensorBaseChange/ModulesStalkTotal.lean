module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModulesStalkTensor

/-!
# The stalk of a total tensor complex

The stalk at a point of the total tensor complex of two complexes of sheaves of modules on a
scheme is the total tensor complex of the stalks over the local ring, and the comparison of
Stacks 01CD for a pullback is read on stalks degreewise.

## Main results

* `Stacks.ModuleSkyscraper.stalk_pullbackTensorComparison`: the stalk at `x'` of the comparison
  `g'^*(M ⊗ N) ≅ g'^*M ⊗ g'^*N` is the base change of the stalk of `M ⊗ N` at `g' x'`.
* `Stacks.ModuleSkyscraper.modulesStalkTotalIso`: the stalk at `x` of the total tensor complex of
  `K` and `L` is isomorphic to the total tensor complex of the stalks of `K` and `L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u

namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X X' : Scheme.{u}} (g' : X' ⟶ X) (x' : X')

/-- The stalk at `z` of a sheaf of modules `M` on a scheme `Z` is a module over the local ring
`𝒪_{Z,z}`. -/
noncomputable local instance stalkModuleScheme' {Z : Scheme.{u}} (z : Z) (M : Z.Modules) :
    Module (Z.presheaf.stalk z) (grpStalk Z.toRingedSpace M.val z) :=
  stalkModule Z.toRingedSpace M.val z

/-- The stalk at `x'` of the comparison `g'^*(M ⊗ N) ≅ g'^*M ⊗ g'^*N` is the base change of the
stalk of `M ⊗ N` at `g' x'`, through the identifications of the stalk of a pullback and of the
stalk of a tensor product. -/
theorem stalk_pullbackTensorComparison (M N : X.Modules) :
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    (pullbackStalkIso g' x').hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) ≫
        (modulesStalkFunctor X' x').map
          (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso g'.toLRSHom.toShHom M N).hom ≫
        (modulesStalkTensorIso x' ((Scheme.Modules.pullback g').obj M)
          ((Scheme.Modules.pullback g').obj N)).hom ≫
        (((pullbackStalkIso g' x').inv.app M ≫
            (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).inv.app
              ((modulesStalkFunctor X (g' x')).obj M)) ⊗ₘ (pullbackStalkIso g' x').inv.app N) =
      (ModuleCat.extendScalars (g'.stalkMap x').hom).map (modulesStalkTensorIso (g' x') M N).hom ≫
        (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).inv.app _ ≫
        (bcTensorIso (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') _ _).hom ≫
        ((baseChangeFunctor (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).obj
            ((modulesStalkFunctor X (g' x')).obj M) ◁
          (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).hom.app
            ((modulesStalkFunctor X (g' x')).obj N)) := by
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  apply ((ModuleCat.extendRestrictScalarsAdj (g'.stalkMap x').hom).homEquiv _ _).injective
  apply modulesStalkTensor_hom_ext
  intro U hx a b
  have h1 := pullbackStalkIso_hom_app_one_tmul g' x'
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) U hx
    (toTensorSheafSection X.toRingedSpace M N (op U) (a ⊗ₜ b))
  have h2 := Stacks.PullbackTensorIso.tensorStalkIso_germ_comparison g'.toLRSHom.toShHom M N x' U
    hx a b
  have h3 := pullbackStalkIso_inv_app_germ g' x' M U hx a
  have h4 := pullbackStalkIso_inv_app_germ g' x' N U hx b
  have s2 : (modulesStalkTensorIso x' ((Scheme.Modules.pullback g').obj M)
        ((Scheme.Modules.pullback g').obj N)).hom.hom
        (((modulesStalkFunctor X' x').map
          (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso
            g'.toLRSHom.toShHom M N).hom).hom
          ((((Scheme.Modules.pullback g').obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N)).presheaf.germ
              (g' ⁻¹ᵁ U) x' hx)
            (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
              (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N)).val.app (op U)
              (toTensorSheafSection X.toRingedSpace M N (op U) (a ⊗ₜ b))))) =
      (show (modulesStalkFunctor X' x').obj ((Scheme.Modules.pullback g').obj M) from
        (((Scheme.Modules.pullback g').obj M).presheaf.germ (g' ⁻¹ᵁ U) x' hx)
          (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M).val.app (op U) a)) ⊗ₜ
      (show (modulesStalkFunctor X' x').obj ((Scheme.Modules.pullback g').obj N) from
        (((Scheme.Modules.pullback g').obj N).presheaf.germ (g' ⁻¹ᵁ U) x' hx)
          (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app N).val.app (op U) b)) :=
    (congrArg (TensorProduct.congr (stalkModuleEquiv x' ((Scheme.Modules.pullback g').obj M)).symm
      (stalkModuleEquiv x' ((Scheme.Modules.pullback g').obj N)).symm) h2).trans rfl
  have h5 := modulesStalkTensorIso_hom_germ (g' x') M N U hx a b
  refine Eq.trans (congrArg (fun t => ((modulesStalkFunctor X' x').map
          (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso g'.toLRSHom.toShHom M N).hom ≫
        (modulesStalkTensorIso x' ((Scheme.Modules.pullback g').obj M)
          ((Scheme.Modules.pullback g').obj N)).hom ≫
        (((pullbackStalkIso g' x').inv.app M ≫
            (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).inv.app
              ((modulesStalkFunctor X (g' x')).obj M)) ⊗ₘ
              (pullbackStalkIso g' x').inv.app N)).hom t)
    h1) ?_
  refine Eq.trans (congrArg (((pullbackStalkIso g' x').inv.app M ≫
            (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).inv.app
              ((modulesStalkFunctor X (g' x')).obj M)) ⊗ₘ
              (pullbackStalkIso g' x').inv.app N).hom s2) ?_
  refine Eq.trans (congrArg₂ (fun p q =>
    ((baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
    (X'.presheaf.stalk x')).inv.app ((modulesStalkFunctor X (g' x')).obj M)).hom p ⊗ₜ q) h3 h4) ?_
  refine Eq.trans ?_ (congrArg (fun t => ((baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x')).inv.app _ ≫
        (bcTensorIso (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') _ _).hom ≫
        ((baseChangeFunctor (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).obj
            ((modulesStalkFunctor X (g' x')).obj M) ◁
          (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).hom.app
            ((modulesStalkFunctor X (g' x')).obj N))).hom
              ((1 : X'.presheaf.stalk x') ⊗ₜ[X.presheaf.stalk (g' x'), (g'.stalkMap x').hom] t))
      h5).symm
  rfl

end Stacks.ModuleSkyscraper


namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : Scheme.{u}} (x : X)

/-- The stalk functor at `x` from sheaves of modules on `X` to modules over the local ring
`𝒪_{X,x}`. -/
abbrev tensorModulesStalkFunctor :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace ⥤
      ModuleCat.{u} (X.presheaf.stalk x) :=
  modulesStalkFunctor X x

/-- The stalk functor at `x` is additive. -/
instance : (tensorModulesStalkFunctor x).Additive :=
  inferInstanceAs (modulesStalkFunctor X x).Additive

/-- The stalk functor at `x` preserves coproducts indexed by the pairs `(p, q)` with
`p + q = n`. -/
instance tensorModulesStalkFunctor_preservesColimitsOfShape_antidiagonal (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) (tensorModulesStalkFunctor x) :=
  letI := (modulesStalkSkyAdjunction X x).leftAdjoint_preservesColimits
  inferInstanceAs (PreservesColimitsOfShape _ (modulesStalkFunctor X x))

/-- The stalk at `x` of the total tensor complex of `K` and `L` is isomorphic to the total tensor
complex, over the local ring `𝒪_{X,x}`, of the stalks of `K` and `L`. -/
def modulesStalkTotalIso
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ) :
    ((tensorModulesStalkFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        (((tensorModulesStalkFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((tensorModulesStalkFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
        (curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))) (ComplexShape.up ℤ) :=
  CategoryTheory.Functor.mapBifunctorTotalIso (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))) (tensorModulesStalkFunctor x)
    (tensorModulesStalkFunctor x) (tensorModulesStalkFunctor x) (modulesStalkTensorIso x)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun φ N => modulesStalkTensorIso_naturality_left x φ N)
    (fun M _ _ ψ => modulesStalkTensorIso_naturality_right x M ψ) K L

end Stacks.ModuleSkyscraper
