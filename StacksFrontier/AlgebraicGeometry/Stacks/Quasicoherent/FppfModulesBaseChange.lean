module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleDirectImageBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProductTerminal

/-!
# The fppf direct image of modules at module universe `u`, through right Kan extensions

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, the direct image of modules on the fppf sites
at module universe `u` is `AlgebraicGeometry.Stack.fppfModulesPushforward`. This file identifies it
with the canonical direct image `AlgebraicGeometry.Stack.moduleDirectImage` along the cocontinuous
functor underlying `f` (both are right adjoint to the inverse image of Stacks 06WE), and reads off
its sections over an object `y` of `𝒴` for which `CostructuredArrow f y` has a terminal object.

## Main results

* `AlgebraicGeometry.Stack.fppfModulesPushforwardIsoModuleDirectImage`: the fppf direct image of
  modules at module universe `u` is `AlgebraicGeometry.Stack.moduleDirectImage`.
* `AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoOfIsTerminal`:
  `Γ(y, f_* M) ≅ Γ(x₀, M)` for a terminal arrow `f x₀ ⟶ y`, naturally in `M`.
* `AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoOfRepresentable`: the same over a
  scheme-valued point of `𝒴` at which the base change of `f` is represented.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- Right Kan extensions along the functor underlying a 1-morphism of algebraic stacks exist for
presheaves valued in a category with `u`-small limits. -/
instance hasPointwiseRightKanExtension_homFunctor_of_hasLimitsOfSize (C : Type*) [Category C]
    [HasLimitsOfSize.{u, u} C] (G : 𝒳.val.val.objᵒᵖ ⥤ C) :
    (CatFiberedInGroupoids.homFunctor f.hom).op.HasPointwiseRightKanExtension G := fun Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u}
    (StructuredArrow Y (CatFiberedInGroupoids.homFunctor f.hom).op) C
  infer_instance

/-- The functor underlying a 1-morphism of algebraic stacks is cocontinuous for the associated
topologies (Stacks 06NW). -/
instance isCocontinuous_homFunctor (τ : GrothendieckTopology B.Schemes) :
    (CatFiberedInGroupoids.homFunctor f.hom).IsCocontinuous
      (associatedTopology B S hS 𝒳.val.val.p τ) (associatedTopology B S hS 𝒴.val.val.p τ) :=
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  let h := 𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  (h.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2

/-- The fppf direct image of modules at module universe `u` is the canonical direct image
`moduleDirectImage` along the cocontinuous functor underlying the 1-morphism. -/
def fppfModulesPushforwardIsoModuleDirectImage :
    fppfModulesPushforward B S hS f ≅
      moduleDirectImage.{u, u + 1, u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        B.topology le_rfl :=
  (fppfModulesPullbackPushforwardAdjunction B S hS f).rightAdjointUniq
    (moduleDirectImageAdjunction.{u, u + 1, u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      B.topology le_rfl)

/-- Sections of the fppf direct image over an object with a terminal arrow: if `(x₀, f x₀ ⟶ y)`
is terminal in `CostructuredArrow f y`, then `Γ(y, f_* M) ≅ Γ(x₀, M)` as abelian groups,
naturally in the module `M`. -/
def fppfModulesPushforwardSectionsIsoOfIsTerminal {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t) :
    fppfModulesPushforward B S hS f ⋙
        Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
          (evaluation 𝒴.val.val.objᵒᵖ AddCommGrpCat.{u}).obj (op y) ≅
      Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
        (evaluation 𝒳.val.val.objᵒᵖ AddCommGrpCat.{u}).obj (op t.left) :=
  Functor.isoWhiskerRight (fppfModulesPushforwardIsoModuleDirectImage B S hS f) _ ≪≫
    Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoOfIsTerminal _ ht

/-- The arrow into a scheme-valued point attached to a representation of the base change is
terminal. -/
def isTerminalRepresentingArrowStack (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj) (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    {W : BigFppfOver B U.left.1 U.left.2}
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p) :
    IsTerminal (TwoFibreProductOver.TerminalArrow.toCostructuredArrow (𝒞 := B.Schemes)
      (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) y
      (TwoFibreProductOver.TerminalArrow.representingObject U.hom 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) y e)) :=
  TwoFibreProductOver.TerminalArrow.isTerminalRepresentingArrow U.hom 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) y e (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    hy 𝒴.val.isFiberedInGroupoids

/-- Sections of the fppf direct image over a scheme-valued point at which the base change is
represented. Let `y : (Sch/U) ⥤ 𝒴` be a scheme-valued point of `𝒴` and suppose the 2-fibre
product `(Sch/U) ×_{y, 𝒴, f} 𝒳` is represented by `W ∈ (Sch/U)`, through `e`. Then
`Γ(y(U), f_* M) ≅ Γ(x₀, M)` naturally in `M`, where `x₀` is the object of `𝒳` corresponding to
`id_W`; it lies over `W`
(`CategoryTheory.TwoFibreProductOver.TerminalArrow.p𝒳_obj_representingObject_y`). -/
def fppfModulesPushforwardSectionsIsoOfRepresentable (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj) (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    {W : BigFppfOver B U.left.1 U.left.2}
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p) :
    fppfModulesPushforward B S hS f ⋙
        Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
          (evaluation 𝒴.val.val.objᵒᵖ AddCommGrpCat.{u}).obj (op (y.obj (Over.mk (𝟙 U.left)))) ≅
      Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
        (evaluation 𝒳.val.val.objᵒᵖ AddCommGrpCat.{u}).obj
          (op (TwoFibreProductOver.TerminalArrow.toCostructuredArrow (𝒞 := B.Schemes)
            (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) y
            (TwoFibreProductOver.TerminalArrow.representingObject U.hom 𝒳.val.val.p 𝒴.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom) y e)).left) :=
  fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f
    (isTerminalRepresentingArrowStack B S hS f U y hy e)

end AlgebraicGeometry.Stack
