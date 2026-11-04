module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDualGroups
public import StacksFrontier.AlgebraicGeometry.Quot.RepresentabilityHelpers.TensorPullbackExtSingle

/-!
# The Ext groups of an object of `Coh_{X/B}` as Ext groups of modules

For an object `x = (T, g, ℱ)` of `Coh_{X/Y}` over an affine test scheme with ring identified with
`A`, the group `AlgebraicGeometry.Space.CoherentSituation.extGroup` is defined as shifted
morphisms `ℱ[0] ⟶ (ℱ[0] ⊗ p^*M̃[0])[n]` in the derived category of `X_T`, the form in which
Stacks 08JR is stated. This file identifies it with the Ext group
`Ext^n_{𝒪_{X_T}}(ℱ, ℱ ⊗ p^*M̃)` of the abelian category of modules on `X_T`, naturally in the
`A`-module `M`: this is the form in which the deformation theory of Stacks 08VW produces its
classes.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.extCoefficient`: the module `ℱ ⊗ p^*M̃` on `X_T`.
* `AlgebraicGeometry.Space.CoherentSituation.extGroupAbelianExtEquiv`: the identification
  `extGroup x e M n ≃+ Ext^n(ℱ, ℱ ⊗ p^*M̃)`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.extGroupAbelianExtEquiv_extGroupMap`: it carries the
  map induced by a module map `M ⟶ N` to composition with the induced map of coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

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

/-- **The coefficient module `ℱ ⊗ p^*M̃`** on `X_T`, for an `A`-module `M`. -/
abbrev extCoefficient (M : ModuleCat.{u} A) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.space x.T)) :=
  ((tensorPullbackBifunctor (D.baseProjection x)).obj x.F).obj
    ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e M))

/-- The map of coefficient modules induced by a map of `A`-modules. -/
abbrev extCoefficientMap {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    D.extCoefficient x e M ⟶ D.extCoefficient x e N :=
  ((tensorPullbackBifunctor (D.baseProjection x)).obj x.F).map
    ((representedAffineAssociated B S hS x.T.left).map
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g))

/-- The module of `x`, as an object of the category of modules on `X_T`. -/
abbrev objectModule : Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2 := x.F

/-- The coefficient module `ℱ ⊗ p^*M̃`, as an object of the category of modules on `X_T`. -/
abbrev extCoefficientModule (M : ModuleCat.{u} A) :
    Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2 :=
  D.extCoefficient x e M

/-- The map of coefficient modules induced by a map of `A`-modules, in the category of modules on
`X_T`. -/
abbrev extCoefficientModuleMap {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    D.extCoefficientModule x e M ⟶ D.extCoefficientModule x e N :=
  D.extCoefficientMap x e g

/-- `ℱ[0] ⊗ p^*M̃[0] ≅ (ℱ ⊗ p^*M̃)[0]` in the derived category of `X_T`. -/
def extCoefficientIso (M : ModuleCat.{u} A) :
    tensorPullbackComplexDerived (D.baseProjection x) (D.singleComplex x)
      ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
          ((representedAffineAssociated B S hS x.T.left).obj (D.baseModule x e M))) ≅
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2) 0).obj
        (D.extCoefficientModule x e M) :=
  DerivedCategory.Q.mapIso (tensorPullbackComplexSingleSingleIso (D.baseProjection x) x.F _)

/-- `ℱ[0] ⊗ p^*M̃[0] ≅ (ℱ ⊗ p^*M̃)[0]` is natural in the `A`-module `M`. -/
theorem extCoefficientIso_hom_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
        (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map
              ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g)))) ≫
        (D.extCoefficientIso x e N).hom =
      (D.extCoefficientIso x e M).hom ≫
        (DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2) 0).map
          (D.extCoefficientModuleMap x e g) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
    (tensorPullbackComplexSingleSingleIso_hom_naturality (D.baseProjection x) x.F _)).trans
      (DerivedCategory.Q.map_comp _ _))

variable [HasExt.{w} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)]

/-- **`Ext^n_{X_T}(ℱ, ℱ ⊗ p^*M̃)`, as shifted morphisms and as Ext of modules.** -/
def extGroupAbelianExtEquiv (M : ModuleCat.{u} A) (n : ℕ) :
    D.extGroup x e M n ≃+
      Abelian.Ext.{w} (D.objectModule x) (D.extCoefficientModule x e M) n where
  toFun c := Abelian.Ext.homAddEquiv.symm
    (D.extGroupEquiv x e M n c ≫ (D.extCoefficientIso x e M).hom⟦(n : ℤ)⟧')
  invFun α := (D.extGroupEquiv x e M n).symm
    (Abelian.Ext.homAddEquiv α ≫ (D.extCoefficientIso x e M).inv⟦(n : ℤ)⟧')
  left_inv c := by
    simp only [AddEquiv.apply_symm_apply, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
    exact (D.extGroupEquiv x e M n).symm_apply_apply c
  right_inv α := by
    simp only [AddEquiv.apply_symm_apply, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id, AddEquiv.symm_apply_apply]
  map_add' c c' := by
    simp only [map_add, Preadditive.add_comp]

/-- The shifted morphism underlying the image of `c` in `Ext^n(ℱ, ℱ ⊗ p^*M̃)`. -/
theorem extGroupAbelianExtEquiv_hom (M : ModuleCat.{u} A) (n : ℕ) (c : D.extGroup x e M n) :
    (D.extGroupAbelianExtEquiv x e M n c).hom =
      D.extGroupEquiv x e M n c ≫ (D.extCoefficientIso x e M).hom⟦(n : ℤ)⟧' := by
  show Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) = _
  exact AddEquiv.apply_symm_apply _ _

omit [HasExt.{w} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)] in
/-- The map induced by a module map, followed by the coefficient identification. -/
theorem extGroupEquiv_extGroupMap_comp_extCoefficientIso {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (n : ℤ) (c : D.extGroup x e M n) :
    D.extGroupEquiv x e N n (D.extGroupMap x e g n c) ≫ (D.extCoefficientIso x e N).hom⟦n⟧' =
      D.extGroupEquiv x e M n c ≫ ((D.extCoefficientIso x e M).hom ≫
        (DerivedCategory.singleFunctor
          (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2) 0).map
          (D.extCoefficientModuleMap x e g))⟦n⟧' := by
  rw [extGroupMap_apply, AddEquiv.apply_symm_apply, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  congr 2
  exact D.extCoefficientIso_hom_naturality x e g

/-- **The identification carries the map induced by a module map to composition with the
induced map of coefficients.** -/
theorem extGroupAbelianExtEquiv_extGroupMap {M N : ModuleCat.{u} A} (g : M ⟶ N) (n : ℕ)
    (c : D.extGroup x e M n) :
    D.extGroupAbelianExtEquiv x e N n (D.extGroupMap x e g n c) =
      (D.extGroupAbelianExtEquiv x e M n c).comp
        (Abelian.Ext.mk₀ (D.extCoefficientModuleMap x e g)) (add_zero n) := by
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, extGroupAbelianExtEquiv_hom,
    extGroupAbelianExtEquiv_hom, ShiftedHom.comp_mk₀, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  exact D.extGroupEquiv_extGroupMap_comp_extCoefficientIso x e g n c

end CoherentSituation

end AlgebraicGeometry.Space

end
