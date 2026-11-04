module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageSheafification
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange

/-!
# Sections of the direct image of modules along a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `τ` one of the topologies of
**Stacks 06TP**. The direct image `f_*` of modules on the `τ`-sites at the module universe `u`
of the schemes, `AlgebraicGeometry.Stack.stackModuleDirectImage`, is computed by a right Kan
extension along `f`. So if an object `y` of `𝒴` has a *terminal* arrow `f(x₀) ⟶ y` in the comma
category `CostructuredArrow f y` — as it does when `𝒳` and `𝒴` are representable by schemes and
`x₀` is the fibre product `y ×_𝒴 𝒳` — then

`Γ(y, f_* G) = Γ(x₀, G)`,

naturally in the module `G`. This is the sections formula behind **Stacks 075Z** (step (4) of its
proof, via **Stacks 075P**) and **Stacks 0765**.

## Main definitions

* `AlgebraicGeometry.Stack.stackModuleDirectImageIsoModuleDirectImage`: the direct image
  `stackModuleDirectImage` is the canonical direct image `moduleDirectImage` along the
  cocontinuous functor `f`; both are right adjoint to the inverse image of **Stacks 06WE**.
* `AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal`: the sections formula.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (τ : SiteKind)

/-- The two spellings of the inverse image of **Stacks 06WE** at module universe `u` agree. -/
def stackModuleInverseImageIsoModulePullback :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        τ ≅
      modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  eqToIso (modulePullback_eq_pushforward_ringStructureSheafCoreHom B S hS _ _ _ _ _ _ _ _).symm

/-- **The direct image at module universe `u` is the canonical direct image along `f`**:
`AlgebraicGeometry.Stack.stackModuleDirectImage` (built through the universe lift) and
`AlgebraicGeometry.Stack.moduleDirectImage` (the right Kan extension along the cocontinuous functor
`f`) are both right adjoint to the inverse image, hence canonically isomorphic. -/
def stackModuleDirectImageIsoModuleDirectImage :
    stackModuleDirectImage B S hS f τ ≅
      moduleDirectImage.{u, u + 1, u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  ((stackModuleInverseDirectImageAdjunction B S hS f τ).ofNatIsoLeft
    (stackModuleInverseImageIsoModulePullback B S hS f τ)).rightAdjointUniq
    (moduleDirectImageAdjunction.{u, u + 1, u, u + 1, u, u} B S hS _ _ _ _ _ _ _ _)

/-- **Sections of the direct image over an object with a terminal arrow.** If
`t = (x₀, f(x₀) ⟶ y)` is terminal in `CostructuredArrow f y`, then `Γ(y, f_* G) ≅ Γ(x₀, G)`,
naturally in the `𝒪_𝒳`-module `G`, for the direct image of modules on the `τ`-sites at module
universe `u`. -/
def stackModuleDirectImageSectionsIsoOfIsTerminal {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t) :
    stackModuleDirectImage B S hS f τ ⋙ Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
        (evaluation 𝒴.val.val.objᵒᵖ AddCommGrpCat.{u}).obj (op y) ≅
      Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
        (evaluation 𝒳.val.val.objᵒᵖ AddCommGrpCat.{u}).obj (op t.left) :=
  Functor.isoWhiskerRight (stackModuleDirectImageIsoModuleDirectImage B S hS f τ) _ ≪≫
    Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoOfIsTerminal _ ht

end AlgebraicGeometry.Stack
