module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStackPointwise
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousTerminalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalObjectCovering

/-!
# Global sections of the direct image along `[S/(ℤ/pℤ)] ⟶ S`

Let `k` be a field, `S = Spec k[x]`, `𝒳 = [S/(ℤ/pℤ)]` and `f : 𝒳 ⟶ S` the structure morphism.
The final object of the total category of `S` is `S` itself, and every object of `𝒳` maps to it
in a unique way. So the sections over it of the direct image `f_* M` of a sheaf of
`𝒪_𝒳`-modules are the compatible families of sections of `M` on the whole of `𝒳`, that is the
global sections `Γ(𝒳, M)`. This file records that identification, naturally in `M` and linearly
over `Γ(S, 𝒪_S)`, which acts on `Γ(𝒳, M)` through the ring map
`Stacks.Examples.UnboundedDerivedPushforward.cyclicStackBaseRingHom`.

## Main results

* `AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoGlobalSections`: for a
  `1`-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and a final object `y` of `𝒴`,
  `Γ(y, f_* -) ≅ Γ(𝒳, -)`, linearly over `𝒪_𝒴(y)`.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPushforwardSectionsIso`:
  `Γ(S, f_* -) ≅ Γ(𝒳, -)` as functors to `Γ(S, 𝒪_S)`-modules.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) {y : 𝒴.val.val.obj} (ht : IsTerminal y)

/-- The structure map `𝒪_𝒴 ⟶ f_* 𝒪_𝒳` of the direct image of modules on the fppf sites along a
`1`-morphism of algebraic stacks. -/
abbrev fppfDirectImageStructureMap :=
  moduleDirectImageStructureMap.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    B.topology le_rfl

/-- The ring map `𝒪_𝒴(y) ⟶ Γ(𝒳, 𝒪_𝒳)` at a final object `y` of `𝒴` that the structure map of
the direct image cuts out on the legs. -/
abbrev fppfDirectImageBaseRingHom :=
  Stacks.SheafOfModules.pushforwardCocontinuousBaseRingHom (fppfDirectImageStructureMap B S hS f)
    ht

/-- The component at `U` of `fppfDirectImageBaseRingHom` is restriction of the structure sheaf
of `𝒴` along the unique arrow `f(U) ⟶ y`, read through the identification `𝒪_𝒳 = f⁻¹𝒪_𝒴`. -/
theorem fppfDirectImageBaseRingHom_apply
    (a : (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids B.topology
      le_rfl).obj.obj (op y)) (U : 𝒳.val.val.objᵒᵖ) :
    (fppfDirectImageBaseRingHom B S hS f ht a).1 U =
      ((ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids B.topology
          le_rfl).obj.map (ht.from ((CatFiberedInGroupoids.homFunctor f.hom).obj U.unop)).op ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
          B.topology le_rfl).symm).app U).hom a :=
  congrArg (fun g => RingCat.Hom.hom g a)
    (scalarπ_moduleDirectImageStructureMap B S hS _ _ _ _ _ _ B.topology le_rfl (op y)
      (Stacks.SheafOfModules.structuredArrowOfIsTerminal ht U))

/-- When `y` lies over a final object of the site, the component at `U` of
`fppfDirectImageBaseRingHom` is restriction of functions along the unique arrow from the scheme
under `U` to the one under `y`. -/
theorem fppfDirectImageBaseRingHom_apply_of_isTerminal (hT : IsTerminal (𝒴.val.val.p.obj y))
    (a : (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids B.topology
      le_rfl).obj.obj (op y)) (U : 𝒳.val.val.objᵒᵖ) :
    (fppfDirectImageBaseRingHom B S hS f ht a).1 U =
      ((BigFppfOver.structureSheaf B S hS).obj.map (hT.from (𝒳.val.val.p.obj U.unop)).op).hom
        a := by
  rw [fppfDirectImageBaseRingHom_apply, eqToHom_app, RingCat.comp_apply]
  change RingCat.Hom.hom (eqToHom (C := RingCat.{u}) _)
    (((BigFppfOver.structureSheaf B S hS).obj.map
      (𝒴.val.val.p.map (ht.from ((CatFiberedInGroupoids.homFunctor f.hom).obj U.unop))).op).hom
        a) = _
  have key : ∀ {A : BigFppfOver B S hS} (_ : A = 𝒳.val.val.p.obj U.unop)
      (g : A ⟶ 𝒴.val.val.p.obj y)
      (h' : (BigFppfOver.structureSheaf B S hS).obj.obj (op A) =
        (BigFppfOver.structureSheaf B S hS).obj.obj (op (𝒳.val.val.p.obj U.unop))),
      (eqToHom h').hom (((BigFppfOver.structureSheaf B S hS).obj.map g.op).hom a) =
        ((BigFppfOver.structureSheaf B S hS).obj.map (hT.from (𝒳.val.val.p.obj U.unop)).op).hom
          a := by
    rintro A rfl g h'
    rw [eqToHom_refl, RingCat.id_apply, hT.hom_ext g (hT.from _)]
  exact key (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f.hom) U.unop) _ _

/-- **Sections of the fppf direct image over a final object are global sections**: for a final
object `y` of `𝒴`, `Γ(y, f_* -) ≅ Γ(𝒳, -)`, naturally in the module and linearly over `𝒪_𝒴(y)`,
which acts on global sections through `fppfDirectImageBaseRingHom`. The left side is lifted to
the universe of the objects of `𝒳`. -/
def fppfModulesPushforwardSectionsIsoGlobalSections :
    fppfModulesPushforward B S hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y) ⋙ ModuleCat.uliftFunctor.{u + 1} _ ≅
      globalSectionsFunctor _ ⋙
        ModuleCat.restrictScalars (fppfDirectImageBaseRingHom B S hS f ht) :=
  Functor.isoWhiskerRight (fppfModulesPushforwardIsoModuleDirectImage B S hS f) _ ≪≫
    Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoGlobalSections _ ht

end AlgebraicGeometry.Stack

namespace Stacks.Examples.UnboundedDerivedPushforward

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- The final object `S → S` of the total category of `S` is final. -/
def isTerminalCyclicBaseStackTerminal :
    IsTerminal (C := (baseStack.{u, w} 𝒞 hS).val.val.obj) (cyclicBaseStackTerminal 𝒞 hS) :=
  Over.mkIdTerminal

/-- The ring map `Γ(S, 𝒪_S) ⟶ Γ(𝒳, 𝒪_𝒳)` that the structure map of the direct image along
`f : [S/(ℤ/pℤ)] ⟶ S` cuts out at the final object is `cyclicStackBaseRingHom`, restriction along
the unique maps to `S`. -/
theorem fppfDirectImageBaseRingHom_cyclicStructureMorphism :
    Stack.fppfDirectImageBaseRingHom 𝒞 _ hS (cyclicStructureMorphism.{u, w} p 𝒞 hS)
        (isTerminalCyclicBaseStackTerminal.{u, w} 𝒞 hS) =
      cyclicStackBaseRingHom p 𝒞 hS := by
  ext a U
  exact Stack.fppfDirectImageBaseRingHom_apply_of_isTerminal 𝒞 _ hS
    (cyclicStructureMorphism.{u, w} p 𝒞 hS) (isTerminalCyclicBaseStackTerminal.{u, w} 𝒞 hS)
    (isTerminalCyclicBaseObject 𝒞 hS) a U

/-- **`Γ(S, f_* -) ≅ Γ(𝒳, -)`** for the structure morphism `f : [S/(ℤ/pℤ)] ⟶ S`: the sections
of the direct image over the final object `S` of the total category of `S` are the global
sections on `𝒳`, naturally in the module and linearly over `Γ(S, 𝒪_S)`, after the universe lift
from the universe of the schemes to that of the objects of `𝒳`. -/
def cyclicPushforwardSectionsIso :
    cyclicPushforwardSections.{u, w} p 𝒞 hS ⋙ ModuleCat.uliftFunctor.{u + 1} (cyclicBaseRing 𝒞 hS) ≅
      Stacks.CechTop.globalSectionsOverBase (cyclicStackRing p 𝒞 hS)
        (cyclicStackBaseRingHom p 𝒞 hS) :=
  Stack.fppfModulesPushforwardSectionsIsoGlobalSections 𝒞 _ hS
      (cyclicStructureMorphism.{u, w} p 𝒞 hS) (isTerminalCyclicBaseStackTerminal.{u, w} 𝒞 hS) ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsCongr
      (fppfDirectImageBaseRingHom_cyclicStructureMorphism.{u, w} p 𝒞 hS))

end Stacks.Examples.UnboundedDerivedPushforward
