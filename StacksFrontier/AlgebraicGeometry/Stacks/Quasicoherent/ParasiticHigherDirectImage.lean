module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatRepresentedPresheafCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesULiftComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSheafification
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedFactorizations
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.TensorSheafExtComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction
public import StacksFrontier.CategoryTheory.Sites.PushforwardSections

/-!
# Higher direct images of parasitic modules are parasitic

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, `τ` the étale or the fppf topology and `ℱ`
a parasitic sheaf of `𝒪_𝒳`-modules on `𝒳_τ` (**Stacks 0773**). Part (2) of **Stacks 0775**
asserts that every higher direct image `R^if_*ℱ` is parasitic. This file proves it, at the module
universe `u + 1` of the objects of the site and at the module universe `u` of the schemes.

## The argument

For an object `y` of `𝒴` lying over `V`, the sections over `y` of the direct image are the
sections over the 2-fibre product `V ×_{y, 𝒴} 𝒳` (**Stacks 06W6**), that is the morphisms out of
`Ψ_y`, the presheaf of sets on `𝒳` represented by the projection `pr : V ×_{y, 𝒴} 𝒳 ⟶ 𝒳`. So
the sections over `y` of the direct image are corepresented by the sheaf of modules
`𝒪_{Ψ_y} = (𝒪_𝒳 ⊗_ℤ ℤ_{Ψ_y})^#`, and their derived functors are
`Ext^n(𝒪_{Ψ_y}, -) = Ext^n(ℤ_{Ψ_y}^#, (-)_ab)`, the cohomology of `pr^{-1}(-)` on the 2-fibre
product (**Stacks 03FD**, `ℤ_{Ψ_y}` being torsion-free). When `y` is a flat object, `pr` is flat
(**Stacks 06PY**), and this cohomology vanishes on a parasitic module by the argument of part (1):
restriction to the flat objects of `𝒳` does not change it (**Stacks 07AK**), and the restriction
of a parasitic module is zero
(`AlgebraicGeometry.Stack.ext_freeAbelianSheaf_eq_zero_of_flatRepresented`).

On the other hand `R^if_*ℱ` is the sheafification of the presheaf of modules whose sections over
`y` are those derived functors: the direct image is the sheafification of its underlying presheaf
of modules, and sheafification and evaluation at `y` are exact. The sheafification of a presheaf
of modules vanishing at the flat objects is parasitic
(`AlgebraicGeometry.Stack.isParasitic_sheafification`). This is the proof in the source, which
writes `R^if_*ℱ` as the sheafification of `y ↦ H^i(V ×_{y, 𝒴} 𝒳, pr^{-1}ℱ)`.

The result at the module universe `u` follows by the universe lift
(`AlgebraicGeometry.Stack.stackModuleHigherDirectImageULiftIso`).

## Main results

* `AlgebraicGeometry.Stack.isParasitic_moduleSheafHigherDirectImage`: **Stacks 0775** part (2) at
  the module universe `u + 1`.
* `AlgebraicGeometry.Stack.isParasitic_stackModuleHigherDirectImage`: **Stacks 0775** part (2)
  at the module universe `u`.
* `AlgebraicGeometry.Stack.isParasitic_fppfModulesHigherDirectImage`: the fppf case at the module
  universe `u`.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w m

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (k : 𝒳 ⟶ 𝒴)

/-- The projection `V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` of the 2-fibre product at an object `y` of `𝒴` lying
over `V` is faithful: a morphism of the 2-fibre product is determined by its component in `𝒳`,
since its component in the slice over `V` lies over the same morphism of schemes. -/
theorem faithful_ambientSquare_snd {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    (CatFiberedInGroupoids.homFunctor (ambientSquare B S hS k y).snd.hom).Faithful := by
  refine ⟨fun {P P'} f g h => TwoFibreProductOver.Hom.ext' ?_ h⟩
  have hb : f.hbase = g.hbase := by
    have hf := f.hb
    have hg := g.hb
    have e : 𝒳.val.val.p.map f.b = 𝒳.val.val.p.map g.b := congrArg _ h
    rwa [IsHomLift.fac' 𝒳.val.val.p f.hbase f.b, IsHomLift.fac' 𝒳.val.val.p g.hbase g.b,
      cancel_epi, cancel_mono] at e
  have : (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj)).val.val.p.Faithful :=
    inferInstanceAs (Over.forget _).Faithful
  apply (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj)).val.val.p.map_injective
  have hf := f.ha
  have hg := g.ha
  rw [IsHomLift.fac' (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj)).val.val.p f.hbase f.a,
    IsHomLift.fac' (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y.obj)).val.val.p g.hbase g.a]
  exact congrArg (fun m => eqToHom _ ≫ m ≫ eqToHom _) hb

/-- The presheaf on `𝒳` represented by the projection `V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` at a flat object `y`
of `𝒴` is represented by a flat 1-morphism with faithful underlying functor. -/
theorem flatRepresented_ambientSquare_snd (y : FlatFppf B S hS 𝒴) :
    FlatRepresented 𝒳
      (componentPresheaf (CatFiberedInGroupoids.homFunctor (ambientSquare B S hS k y).snd.hom)) :=
  ⟨_, (ambientSquare B S hS k y).snd, faithful_ambientSquare_snd k y,
    FlatFppf.isFlat_ambientSquare_snd B S hS k y, rfl⟩

section SiteKind

variable (τ : SiteKind)

attribute [local instance] hasSheafify_associatedTopology_succ
  wEqualsLocallyBijective_associatedTopology_succ

/-- The presheaf of sets `Ψ_y` on `𝒳` represented by the projection `V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` of the
2-fibre product at an object `y` of `𝒴` lying over `V`. -/
abbrev ambientComponentPresheaf {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    𝒳.val.val.objᵒᵖ ⥤ Type (u + 1) :=
  componentPresheaf (CatFiberedInGroupoids.homFunctor (ambientSquare B S hS k y).snd.hom)

/-- The sheaf of `𝒪_𝒳`-modules `𝒪_{Ψ_y} = (𝒪_𝒳 ⊗_ℤ ℤ_{Ψ_y})^#` freely generated by the presheaf
`Ψ_y`. -/
abbrev ambientTensorSheaf {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ) :=
  Stacks.Cohomology.TensorSheafComparison.tensorSheaf
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)
    (Presheaf.freeAbelian.obj (ambientComponentPresheaf k y))

/-- The sections over an object `y` of `𝒴` of the direct image at module universe `u + 1`, as a
functor to abelian groups. -/
abbrev directImageSectionsFunctor (y : 𝒴.val.val.obj) :
    SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ) ⥤ AddCommGrpCat.{u + 1} :=
  stackModuleDirectImageSucc B S hS k τ ⋙ SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op y) ⋙ forget₂ (ModuleCat _) AddCommGrpCat

/-- The compatible families of sections of a module over the image of the projection
`V ×_{y, 𝒴} 𝒳 ⥤ 𝒳`, as a functor to types. -/
abbrev ambientSectionsFunctor {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ) ⥤ Type (u + 1) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (CatFiberedInGroupoids.homFunctor (ambientSquare B S hS k y).snd.hom).op ⋙
    Functor.sectionsFunctor _

/-- **The sections over `y` of the direct image are the sections over `V ×_{y, 𝒴} 𝒳`**, naturally
in the module: the formula `f_*ℱ(y) = Γ(V ×_{y, 𝒴} 𝒳, pr^{-1}ℱ)` of **Stacks 06W6**, on
underlying sets. -/
def directImageSectionsIso {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    directImageSectionsFunctor k τ y.obj ⋙ CategoryTheory.forget AddCommGrpCat ≅
      ambientSectionsFunctor k τ y :=
  have hF := (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p k.hom))
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).1
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).2
  SheafOfModules.directImageOfEqSectionsIso (CatFiberedInGroupoids.homFunctor k.hom) _ _ _
      (Stacks.RelativeCech.ringStructureSheafCore_eq_pushforward B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor k.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p k.hom) τ) (op y.obj) ≪≫
    NatIso.ofComponents (fun _ => Equiv.toIso
      ((Presheaf.pushforwardCostrSectionsEquiv _ y.obj _).trans
        (Presheaf.pushforwardIndexSectionsEquiv 𝒳.val.val.p 𝒴.val.val.p _
          ((ambientChoiceOfPullbacks B S hS 𝒴).sliceDatum y.obj) 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor_comp_p k.hom) _))) (fun _ => rfl)

/-- Morphisms of abelian presheaves `ℤ_{Ψ_y} ⟶ ℱ` are the compatible families of sections of `ℱ`
over the image of the projection `V ×_{y, 𝒴} 𝒳 ⥤ 𝒳`, naturally in the module `ℱ`: such a morphism
is a morphism of presheaves of sets `Ψ_y ⟶ ℱ`
(`Stacks.Sites.CoverDescent.componentPresheafHomEquiv`). -/
def freeAbelianHomSectionsIso {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    (SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _ ⋙
        preadditiveCoyoneda.obj (op (Presheaf.freeAbelian.obj (ambientComponentPresheaf k y)))) ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      ambientSectionsFunctor k τ y :=
  NatIso.ofComponents (fun N => Equiv.toIso
      ((Presheaf.freeAbelianAdj.homEquiv (ambientComponentPresheaf k y)
          ((SheafOfModules.toSheaf _).obj N).obj).trans
        (componentPresheafHomEquiv _ _))) (fun {N N'} g => by
      refine TypeCat.homEquiv.injective (funext fun φ => ?_)
      refine Subtype.ext (funext fun ζ => ?_)
      have h := Presheaf.freeAbelianAdj.homEquiv_naturality_right φ
        ((SheafOfModules.toSheaf _).map g).hom
      exact (congrArg (fun η => (componentPresheafHomEquiv
        (CatFiberedInGroupoids.homFunctor (ambientSquare B S hS k y).snd.hom) _ η).1 ζ) h).trans
        rfl)

/-- **Morphisms out of `𝒪_{Ψ_y}` are the sections over `V ×_{y, 𝒴} 𝒳`**, naturally in the module:
a morphism `𝒪_{Ψ_y} ⟶ ℱ` is a morphism of abelian presheaves `ℤ_{Ψ_y} ⟶ ℱ`
(`Stacks.SheafOfModules.tensorSheafHomIso` and the sheafification adjunction), and those are
`AlgebraicGeometry.Stack.freeAbelianHomSectionsIso`. -/
def tensorSheafSectionsIso {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    preadditiveCoyoneda.obj (op (ambientTensorSheaf k τ y)) ⋙
        CategoryTheory.forget AddCommGrpCat ≅
      ambientSectionsFunctor k τ y :=
  Functor.isoWhiskerRight
      (Stacks.SheafOfModules.tensorSheafHomIso.{u + 1, u, u, u + 1}
          (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
          (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)
          (Presheaf.freeAbelian.obj (ambientComponentPresheaf k y)) ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.toSheaf _)
          (Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso
            (sheafificationAdjunction (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
              AddCommGrpCat.{u + 1})
            (Presheaf.freeAbelian.obj (ambientComponentPresheaf k y))).symm)
      (CategoryTheory.forget AddCommGrpCat) ≪≫
    freeAbelianHomSectionsIso k τ y

/-- **The sections over `y` of the direct image are corepresented by `𝒪_{Ψ_y}`**, as a functor to
abelian groups. -/
def directImageSectionsCoyonedaIso {Q : ObjectProperty 𝒴.val.val.obj} (y : Q.FullSubcategory) :
    preadditiveCoyoneda.obj (op (ambientTensorSheaf k τ y)) ≅
      directImageSectionsFunctor k τ y.obj :=
  haveI : (stackModuleDirectImageSucc B S hS k τ).Additive :=
    Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) τ
  preadditiveCoyonedaIsoOfForget _ _
    (tensorSheafSectionsIso k τ y ≪≫ (directImageSectionsIso k τ y).symm)

/-- A module isomorphic to a parasitic module is parasitic, in any module universe. -/
theorem isParasitic_of_iso {𝒵 : AlgebraicStacks.{u, w} B S hS} {τ : SiteKind}
    {M M' : SheafOfModules.{m} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids τ)} (e : M ≅ M') (h : IsParasitic B S hS 𝒵 τ M.val) :
    IsParasitic B S hS 𝒵 τ M'.val := fun x hx =>
  @Equiv.subsingleton _ _ ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op x) ⋙
    CategoryTheory.forget _).mapIso e).toEquiv.symm (h x hx)

/-- Modules at the universe `u + 1` on the `τ`-site of an algebraic stack have enough
injectives. -/
private theorem enoughInjectives_stackModules_succ_aux (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒵.val.val.p 𝒵.val.isFiberedInGroupoids τ)) :=
  enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS 𝒵.val.val.p
    𝒵.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ)

/-- The direct image at module universe `u + 1` is additive. -/
private theorem additive_stackModuleDirectImageSucc_aux :
    (stackModuleDirectImageSucc B S hS k τ).Additive :=
  Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) τ

/-- **The higher derived functors of the sections over a flat object of the direct image vanish on
a parasitic module**, for `τ` the étale or the fppf topology. At a flat object `y` of `𝒴` the
sections of the direct image are `Hom(𝒪_{Ψ_y}, -)`
(`AlgebraicGeometry.Stack.directImageSectionsCoyonedaIso`), whose derived functors are
`Ext^n(ℤ_{Ψ_y}^#, (-)_ab)` because `ℤ_{Ψ_y}` is torsion-free
(`Stacks.Cohomology.TensorSheafComparison.isZero_rightDerived_of_iso_preadditiveCoyoneda`), and
those vanish on a module vanishing at the flat objects of `𝒳` because `Ψ_y` is represented by the
flat projection `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳`
(`AlgebraicGeometry.Stack.ext_freeAbelianSheaf_eq_zero_of_flatRepresented`). -/
theorem isZero_rightDerived_directImageSectionsFunctor (hτ : τ = .etale ∨ τ = .fppf)
    (y : FlatFppf B S hS 𝒴)
    (N : SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) (hN : IsParasitic B S hS 𝒳 τ N.val) (n : ℕ) :
    letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ)
    haveI : (stackModuleDirectImageSucc B S hS k τ).Additive :=
      Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u} B S hS
        𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) τ
    IsZero (((directImageSectionsFunctor k τ y.obj).rightDerived n).obj N) := by
  let := enoughInjectives_stackModules_succ_aux τ 𝒳
  have := additive_stackModuleDirectImageSucc_aux k τ
  refine Stacks.Cohomology.TensorSheafComparison.isZero_rightDerived_of_iso_preadditiveCoyoneda
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)
    (directImageSectionsFunctor k τ y.obj)
    (Presheaf.freeAbelian.obj (ambientComponentPresheaf k y))
    (Stacks.Cohomology.TensorSheafComparison.isTorsionFree_freeAbelian _)
    (directImageSectionsCoyonedaIso k τ y).symm N n (fun x =>
      ext_freeAbelianSheaf_eq_zero_of_flatRepresented 𝒳 hτ (flatRepresented_ambientSquare_snd k y)
        ((SheafOfModules.toSheaf _).obj N) (fun x hx => hN x hx) n x)

/-- Modules at the universe `u + 1` on the `τ`-site of an algebraic stack have enough
injectives, stated so that it can serve as an instance. -/
theorem enoughInjectives_stackModules_succ (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒵.val.val.p 𝒵.val.isFiberedInGroupoids τ)) :=
  enoughInjectives_stackModules_succ_aux τ 𝒵

/-- The direct image at module universe `u + 1` is additive, stated so that it can serve as an
instance. -/
theorem additive_stackModuleDirectImageSucc : (stackModuleDirectImageSucc B S hS k τ).Additive :=
  additive_stackModuleDirectImageSucc_aux k τ

/-- Sheafification of presheaves of modules at the universe `u + 1` on the `τ`-site of an
algebraic stack. -/
abbrev stackModuleSheafificationSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    PresheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids τ).obj ⥤
      SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids τ) :=
  PresheafOfModules.sheafification.{u + 1} (𝟙 _)

/-- Sheafification of presheaves of modules is additive, being a left adjoint. -/
theorem additive_stackModuleSheafificationSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    (stackModuleSheafificationSucc τ 𝒵).Additive :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive

/-- Sheafification of presheaves of modules is exact: it preserves finite limits, and colimits
as a left adjoint. -/
theorem preservesHomology_stackModuleSheafificationSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    (stackModuleSheafificationSucc τ 𝒵).PreservesHomology :=
  have := additive_stackModuleSheafificationSucc τ 𝒵
  have : PreservesFiniteColimits (stackModuleSheafificationSucc τ 𝒵) :=
    have : PreservesColimitsOfSize.{0, 0} (stackModuleSheafificationSucc τ 𝒵) :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).leftAdjoint_preservesColimits
    inferInstance
  Functor.preservesHomologyOfExact _

attribute [local instance] enoughInjectives_stackModules_succ additive_stackModuleDirectImageSucc
  additive_stackModuleSheafificationSucc preservesHomology_stackModuleSheafificationSucc

/-- The counit of the sheafification adjunction for modules at the universe `u + 1` on the
`τ`-site of an algebraic stack is invertible. -/
theorem isIso_sheafificationAdjunctionSucc_counit (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    IsIso (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids τ).obj)).counit :=
  inferInstance

/-- The counit of the sheafification adjunction for modules at the universe `u + 1` on the
`τ`-site of an algebraic stack is invertible: a sheaf of modules is the sheafification of its
underlying presheaf of modules. -/
def forgetCompSheafificationSuccIso (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    SheafOfModules.forget (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids τ) ⋙ stackModuleSheafificationSucc τ 𝒵 ≅ 𝟭 _ :=
  @asIso _ _ _ _ (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids τ).obj)).counit (isIso_sheafificationAdjunctionSucc_counit τ 𝒵)

/-- **The higher direct images at module universe `u + 1` are sheafified derived presheaf
direct images**: `R^nf_* ≅ a ∘ R^n(f_*^{pre})`, for `f_*^{pre}` the direct image followed by the
underlying presheaf of modules and `a` sheafification. The direct image of a sheaf is the
sheafification of its underlying presheaf, and the exact functor `a` can be pulled out of the
derived functor (`CategoryTheory.Functor.rightDerivedCompIso`). -/
def stackModuleDirectImageSuccRightDerivedIso (n : ℕ) :
    (stackModuleDirectImageSucc B S hS k τ).rightDerived n ≅
      (stackModuleDirectImageSucc B S hS k τ ⋙ SheafOfModules.forget _).rightDerived n ⋙
        stackModuleSheafificationSucc τ 𝒴 :=
  (Functor.rightDerivedIsoOfNatIso (Functor.isoWhiskerLeft (stackModuleDirectImageSucc B S hS k τ)
      (forgetCompSheafificationSuccIso τ 𝒴) ≪≫
        (stackModuleDirectImageSucc B S hS k τ).rightUnitor) n).symm ≪≫
    Functor.rightDerivedCompIso (stackModuleDirectImageSucc B S hS k τ ⋙ SheafOfModules.forget _)
      (stackModuleSheafificationSucc τ 𝒴) n

/-- The sections over a flat object of `𝒴` of the derived presheaf direct images of a parasitic
module vanish, for `τ` the étale or the fppf topology: evaluation followed by the underlying
abelian group is exact, so these sections are the derived functors of the sections of the direct
image (`AlgebraicGeometry.Stack.isZero_rightDerived_directImageSectionsFunctor`). -/
theorem subsingleton_rightDerived_forget_obj (hτ : τ = .etale ∨ τ = .fppf)
    (y : FlatFppf B S hS 𝒴)
    (N : SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) (hN : IsParasitic B S hS 𝒳 τ N.val) (n : ℕ) :
    Subsingleton ((((stackModuleDirectImageSucc B S hS k τ ⋙ SheafOfModules.forget _).rightDerived
      n).obj N).obj (op y.obj)) :=
  have : (PresheafOfModules.evaluation.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ).obj (op y.obj)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have h := ((Functor.rightDerivedCompIso (stackModuleDirectImageSucc B S hS k τ ⋙
      SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation.{u + 1} _ (op y.obj))
    (forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}) n).app N).isZero_iff.1
      (isZero_rightDerived_directImageSectionsFunctor k τ hτ y N hN n)
  @Equiv.subsingleton _ _ ((CategoryTheory.forget _).mapIso
    ((Functor.rightDerivedCompIso (stackModuleDirectImageSucc B S hS k τ ⋙ SheafOfModules.forget _)
      (PresheafOfModules.evaluation.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
        𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ).obj (op y.obj)) n).app N)).toEquiv.symm
    (AddCommGrpCat.subsingleton_of_isZero h)

/-- **Stacks 0775 (2) at the module universe `u + 1`, for the derived functors of the direct
image `AlgebraicGeometry.Stack.stackModuleDirectImageSucc`.** The higher direct images of a
parasitic module are parasitic, for `τ` the étale or the fppf topology.

By `AlgebraicGeometry.Stack.stackModuleDirectImageSuccRightDerivedIso`, `R^nf_*ℱ` is the
sheafification of a presheaf of modules whose sections over the flat objects of `𝒴` vanish
(`AlgebraicGeometry.Stack.subsingleton_rightDerived_forget_obj`), and such a sheafification is
parasitic (`AlgebraicGeometry.Stack.isParasitic_sheafification`). -/
theorem isParasitic_rightDerived_stackModuleDirectImageSucc (hτ : τ = .etale ∨ τ = .fppf)
    (N : SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) (hN : IsParasitic B S hS 𝒳 τ N.val) (n : ℕ) :
    IsParasitic B S hS 𝒴 τ (((stackModuleDirectImageSucc B S hS k τ).rightDerived n).obj N).val :=
  isParasitic_of_iso ((stackModuleDirectImageSuccRightDerivedIso k τ n).app N).symm
    (isParasitic_sheafification.{u, w, u + 1} B S hS 𝒴 τ _ (fun y hy =>
      subsingleton_rightDerived_forget_obj k τ hτ ⟨y, hy⟩ N hN n))

/-- **Stacks 0775 (2) at the module universe `u + 1` of the objects of the site.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, `τ` the étale or the fppf topology, and `ℱ` a
parasitic sheaf of `𝒪_𝒳`-modules on `𝒳_τ` (**Stacks 0773**). Then every higher direct image
`R^nf_*ℱ` (**Stacks 06WE**, `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`) is a
parasitic sheaf of `𝒪_𝒴`-modules.

This is `AlgebraicGeometry.Stack.isParasitic_rightDerived_stackModuleDirectImageSucc` moved along
`AlgebraicGeometry.AlgebraicStacks.moduleDirectImageRightDerivedIso`. -/
@[stacks 0775 "part (2), for τ the étale or the fppf topology, at the module universe u + 1 of \
the objects of the site: R^if_*ℱ is parasitic for a parasitic ℱ"]
theorem isParasitic_moduleSheafHigherDirectImage (hτ : τ = .etale ∨ τ = .fppf)
    (N : SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) (hN : IsParasitic B S hS 𝒳 τ N.val) (n : ℕ) :
    IsParasitic B S hS 𝒴 τ ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
      (B.baseTopology τ) (B.baseTopology_le_topology τ) n).obj N).val :=
  isParasitic_of_iso ((AlgebraicStacks.moduleDirectImageRightDerivedIso B S hS 𝒳.val.val.p
      𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
      τ n).app N)
    (isParasitic_rightDerived_stackModuleDirectImageSucc k τ hτ N hN n)

/-- **Stacks 0775 (2)**, for `τ` the étale or the fppf topology, at the module universe `u` of the
schemes. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `ℱ` a parasitic sheaf of
`𝒪_𝒳`-modules on `𝒳_τ` (**Stacks 0773**). Then every higher direct image `R^nf_*ℱ`
(`AlgebraicGeometry.Stack.stackModuleHigherDirectImage`) is parasitic.

The universe lift carries `R^nf_*ℱ` to `R^nf_*` at `u + 1` of the lift of `ℱ`
(`AlgebraicGeometry.Stack.stackModuleHigherDirectImageULiftIso`), the lift of a parasitic module
is parasitic, and at `u + 1` this is
`AlgebraicGeometry.Stack.isParasitic_moduleSheafHigherDirectImage`. -/
@[stacks 0775 "part (2), for τ the étale or the fppf topology, at the module universe u of the \
schemes: R^if_*ℱ is parasitic for a parasitic ℱ"]
theorem isParasitic_stackModuleHigherDirectImage (hτ : τ = .etale ∨ τ = .fppf)
    (N : SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) (hN : IsParasitic B S hS 𝒳 τ N.val) (n : ℕ) :
    IsParasitic B S hS 𝒴 τ ((stackModuleHigherDirectImage B S hS k τ n).obj N).val :=
  fun y hy => @Equiv.subsingleton _ _ Equiv.ulift.symm
    (isParasitic_of_iso ((stackModuleHigherDirectImageULiftIso τ k n).app N).symm
      (isParasitic_moduleSheafHigherDirectImage k τ hτ ((stackModuleULift B S hS τ 𝒳).obj N)
        (fun x hx => @Equiv.subsingleton _ _ Equiv.ulift (hN x hx)) n) y hy)

/-- **Stacks 0775 (2) for the fppf topology at the module universe `u`**: for every 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, the higher direct images
`AlgebraicGeometry.Stack.fppfModulesHigherDirectImage` of a parasitic module are parasitic. This
is `AlgebraicGeometry.Stack.isParasitic_stackModuleHigherDirectImage` at `τ = fppf`. -/
@[stacks 0775 "part (2) for τ = fppf at the module universe u of the schemes: R^if_*ℱ is \
parasitic for a parasitic ℱ, with R^if_* as in fppfModulesHigherDirectImage"]
theorem isParasitic_fppfModulesHigherDirectImage
    (N : SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)) (hN : IsParasitic B S hS 𝒳 .fppf N.val) (n : ℕ) :
    IsParasitic B S hS 𝒴 .fppf ((fppfModulesHigherDirectImage B S hS k n).obj N).val :=
  isParasitic_stackModuleHigherDirectImage k .fppf (Or.inr rfl) N hN n

end SiteKind

end AlgebraicGeometry.Stack

end
