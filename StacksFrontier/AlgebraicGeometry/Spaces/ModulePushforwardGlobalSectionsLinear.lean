module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRightDerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# Linearity of the global sections of a direct image

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  The identification
`Γ(Y, f_*𝓜) = Γ(X, 𝓜)` of `AlgebraicGeometry.Space.globalSectionsModulePushforwardIso` is an
isomorphism of abelian groups natural in the `𝒪_X`-module `𝓜`.  The two sides are modules over
`Γ(Y, 𝒪_Y)` and over `Γ(X, 𝒪_X)`, and the identification is linear for any pair of global
functions `b` on `Y` and `a` on `X` such that `a` is the pullback of `b`: the direct image of
multiplication by `a` is multiplication by `b`, and the identification is natural.

So for a ring `A` acting compatibly on the global functions of `Y` and of `X`, through ring maps
`ψ_Y : A ⟶ Γ(Y, 𝒪_Y)` and `ψ_X : A ⟶ Γ(X, 𝒪_X)` whose values are related by pullback, the
identification is an isomorphism of functors to `A`-modules, and it induces an isomorphism of
`A`-modules between the right derived functors

`Rⁿ(Γ(Y, f_* −))(𝓜) ≅ Hⁿ(X, 𝓜)`.

## Main definitions

* `AlgebraicGeometry.Space.IsPullbackSection`: a global function `a` on `X` is the pullback of
  a global function `b` on `Y` along `f`, chart by chart.
* `AlgebraicGeometry.Space.globalSectionsModulePushforwardIsoOfIsPullbackSection`:
  `Γ(Y, f_* −) ≅ Γ(X, −)` as functors to `A`-modules.
* `AlgebraicGeometry.Space.rightDerivedGlobalSectionsModulePushforwardIsoOfIsPullbackSection`:
  `Rⁿ(Γ(Y, f_* −))(𝓜) ≅ Hⁿ(X, 𝓜)` as `A`-modules.

## Main results

* `AlgebraicGeometry.Space.moduleChartProjectionApp_smul`: the chart projections of a direct
  image are semilinear over the pullback of functions.
* `AlgebraicGeometry.Space.modulePushforward_map_globalSmul`: the direct image of
  multiplication by the pullback of `b` is multiplication by `b`.
* `AlgebraicGeometry.Space.modulePushforwardSectionsEquiv_smul`: the identification
  `Γ(Y, f_*𝓜) = Γ(X, 𝓜)` carries `b • s` to `a • s` when `a` is the pullback of `b`.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Pullback of regular functions from an étale chart `V` of `Y` to an étale chart of `X` over
`X ×_Y V`, as a homomorphism into the ring over which the sections of an `𝒪_X`-module over that
chart are a module.  It is `AlgebraicGeometry.Space.chartPullback`, with its target spelled as
the structure ring. -/
def chartBaseChangeRingPullback (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
        (op V) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        j.right :=
  (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j)).op)

/-- The chart projection of a section of a direct image of modules, with its value spelled as a
section of the module. -/
def moduleChartProjectionApp (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) : F.val.obj j.right :=
  (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x

/-- **The chart projections of a direct image are semilinear over the pullback of functions.**
The scalar action on the sections of `f_*𝓕` over an étale chart `V` of `Y` is the transported
action read through `f♯`, so a chart projection carries it to the action through the pullback
of functions. -/
theorem moduleChartProjectionApp_smul (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
      (op V))
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    moduleChartProjectionApp B S hS f F V j (r • x) =
      (chartBaseChangeRingPullback B S hS f V j).hom r •
        moduleChartProjectionApp B S hS f F V j x := by
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) := inferInstance
  have hQ : PreservesFiniteProducts (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1)
      j.right) := inferInstance
  have hR : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget RingCat.{u}) := inferInstance
  have hA : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
  refine Eq.trans (@moduleSMulObj_naturality _ _ _ hR hA
    (structureRingSheaf B S hS X) F _ hP _ hQ (moduleChartProjection B S hS f V j)
    (show ((smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)).obj
      (structureSetSheaf B S hS X)) from
      ((structureSharp B S hS f).hom.app (op V)).hom r) x) ?_
  rw [moduleChartProjection_app_structureSharp]
  exact sectionsFunctor_map_moduleSMulHom
    (structureRingSheaf B S hS X) F j.right
    (chartPullback B S hS f V j r)
    ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x)

/-- A global function `a` on `X` is **the pullback of a global function `b` on `Y`** along
`f : X ⟶ Y` when, for every étale chart `V` of `Y` and every étale chart of `X` over
`X ×_Y V`, the value of `a` on the chart of `X` is the pullback of the value of `b` on `V`. -/
def IsPullbackSection (f : X ⟶ Y)
    (a : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (b : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :
    Prop :=
  ∀ (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op),
    a.1 j.right = (chartBaseChangeRingPullback B S hS f V j).hom (b.1 (op V))

/-- **The direct image of multiplication by a pullback is multiplication by the function
pulled back.**  If `a` is the pullback of `b` along `f`, then `f_*(a · −) = b · −` on
`f_*𝓜`. -/
theorem modulePushforward_map_globalSmul (f : X ⟶ Y)
    {a : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)}
    {b : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)}
    (h : IsPullbackSection B S hS f a b)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).map (globalSmul _ a M) =
      globalSmul _ b ((modulePushforward B S hS f).obj M) := by
  ext V x
  refine moduleChartProjection_ext B S hS f V.unop (moduleSetSheaf B S hS X M) fun j => ?_
  refine (Functor.natTrans_app_map_apply (moduleChartProjection B S hS f V.unop j)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (globalSmul _ a M)) x).trans ?_
  refine Eq.trans ?_ (moduleChartProjectionApp_smul B S hS f M V.unop j (b.1 V) x).symm
  change a.1 j.right • moduleChartProjectionApp B S hS f M V.unop j x = _
  rw [h V.unop j]

/-- **The identification `Γ(Y, f_*𝓜) = Γ(X, 𝓜)` is linear over pulled-back functions**: it
carries `b • s` to `a • s` when `a` is the pullback of `b` along `f`. -/
theorem modulePushforwardSectionsEquiv_smul (f : X ⟶ Y)
    {a : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)}
    {b : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)}
    (h : IsPullbackSection B S hS f a b)
    (M : Modules.{u, u} B S hS X.1 X.2) (s : ((modulePushforward B S hS f).obj M).sections) :
    modulePushforwardSectionsEquiv B S hS f M (b • s) =
      a • modulePushforwardSectionsEquiv B S hS f M s := by
  have hb : b • s = SheafOfModules.sectionsMap
      ((modulePushforward B S hS f).map (globalSmul _ a M)) s := by
    rw [modulePushforward_map_globalSmul B S hS f h]
    rfl
  rw [hb, modulePushforwardSectionsEquiv_naturality]
  rfl

section Linear

variable {A : Type*} [Ring A]

/-- **`Γ(Y, f_* −) ≅ Γ(X, −)` as functors to `A`-modules**, for a ring `A` acting on the global
functions of `Y` and of `X` through ring maps `ψ_Y` and `ψ_X` whose values are related by
pullback along `f`. -/
def globalSectionsModulePushforwardIsoOfIsPullbackSection (f : X ⟶ Y)
    (ψY : A →+* GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (ψX : A →+* GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hψ : ∀ c : A, IsPullbackSection B S hS f (ψX c) (ψY c)) :
    modulePushforward B S hS f ⋙
        globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⋙
        ModuleCat.restrictScalars ψY ≅
      globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        ModuleCat.restrictScalars ψX :=
  NatIso.ofComponents
    (fun M => LinearEquiv.toModuleIso (show
      ((ModuleCat.restrictScalars ψY).obj ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj
            ((modulePushforward B S hS f).obj M))) ≃ₗ[A]
        ((ModuleCat.restrictScalars ψX).obj ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
            M)) from
      { toFun := modulePushforwardSectionsEquiv B S hS f M
        invFun := (modulePushforwardSectionsEquiv B S hS f M).symm
        left_inv := (modulePushforwardSectionsEquiv B S hS f M).left_inv
        right_inv := (modulePushforwardSectionsEquiv B S hS f M).right_inv
        map_add' := (Stacks.Cohomology.naturalTransformationAddHom _ _
          (modulePushforwardSectionsNatTrans B S hS f) M).map_add
        map_smul' := fun c s => modulePushforwardSectionsEquiv_smul B S hS f (hψ c) M s }))
    (fun {M N} q => by
      ext s
      exact modulePushforwardSectionsEquiv_naturality B S hS f q s)

/-- **`Rⁿ(Γ(Y, f_* −))(𝓜) ≅ Hⁿ(X, 𝓜)` as `A`-modules**, for a ring `A` acting compatibly on
the global functions of `Y` and of `X`: the right derived functors of the two sides of
`AlgebraicGeometry.Space.globalSectionsModulePushforwardIsoOfIsPullbackSection`, restriction of
scalars being exact. -/
def rightDerivedGlobalSectionsModulePushforwardIsoOfIsPullbackSection (f : X ⟶ Y)
    (ψY : A →+* GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (ψX : A →+* GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hψ : ∀ c : A, IsPullbackSection B S hS f (ψX c) (ψY c))
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (ModuleCat.restrictScalars ψY).obj
        (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived n).obj M) ≅
      (ModuleCat.restrictScalars ψX).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj M) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS f
  have := ModuleRightDerivedLimit.restrictScalars_preservesHomology.{u + 1} ψY
  have := ModuleRightDerivedLimit.restrictScalars_preservesHomology.{u + 1} ψX
  ((Functor.rightDerivedCompIso (modulePushforward B S hS f ⋙
      globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (ModuleCat.restrictScalars ψY) n).app M).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (globalSectionsModulePushforwardIsoOfIsPullbackSection B S hS f ψY ψX hψ) n).app M ≪≫
    (Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (ModuleCat.restrictScalars ψX) n).app M

end Linear

end AlgebraicGeometry.Space
