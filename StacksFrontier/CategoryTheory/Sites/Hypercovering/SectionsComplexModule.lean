module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence

/-!
# The complex of sections of a hypercovering with coefficients in a sheaf of modules

Let `C` be a site, `X` an object of `C`, `R` a sheaf of rings on `C` and
`K` a simplicial object of `FormalCoproduct (Over X)` -- a simplicial semi-representable object
over `X`.  For a sheaf `F` of `R`-modules the complex of sections
```
s(F(K)) = ( ∏_{i ∈ I₀} F(U_i) → ∏_{i ∈ I₁} F(U_i) → ∏_{i ∈ I₂} F(U_i) → … )
```
is a complex of modules over the ring `R(X)` of sections of `R` on `X`: every term and every
differential is `R(X)`-linear, because the whole construction takes place over the slice
`Over X`, whose terminal object is `X` itself.  This file builds that complex, functorially in
`F` and contravariantly in `K`, and identifies the underlying complex of abelian groups with
`Stacks.CategoryTheory.Hypercovering.SectionsOver.sectionsComplex`.

## Main definitions

* `SectionsOver.sectionsModulePresheafFunctor`: a sheaf of `R`-modules restricted to the objects
  over `X`, as a presheaf of `R(X)`-modules.
* `SectionsOver.sectionsModuleComplexFunctor`: the complex `s(-(K))` of `R(X)`-modules, as a
  functor of the coefficient sheaf of modules; `SectionsOver.sectionsModuleComplex` is its
  object part.
* `SectionsOver.sectionsModuleComplexMap`: the morphism of complexes induced by a morphism of
  simplicial semi-representable objects over `X`.
* `SectionsOver.sectionsModuleComplexHypercoveringFunctor`: the resulting functor on the
  opposite category of simplicial semi-representable objects over `X`.

## Main results

* `SectionsOver.sectionsModuleComplex_X`: the degree-`n` term is the product, over the summands
  of the `n`-th level of `K`, of the modules of sections of `F` on those summands.
* `SectionsOver.sectionsModuleComplex_d`: the differential is the alternating sum of the coface
  maps.
* `SectionsOver.sectionsModuleComplexFunctor_additive`: the complex is an additive functor of
  the coefficient sheaf of modules.
* `SectionsOver.sectionsModuleComplexForgetIso`: forgetting the `R(X)`-module structure gives
  the complex of sections of `K` with coefficients in the underlying abelian sheaf, naturally in
  the coefficient sheaf of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe uM uR w v u

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.CategoryTheory.Hypercovering.SectionsOver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{uR}) (X : C)

/-- **A sheaf of `R`-modules restricted to the objects over `X`, as a presheaf of modules over
the ring `R(X)` of sections of `R` on `X`**, functorially in the sheaf of modules.  The module
structure on the sections over `U → X` is restriction of scalars along the unique map
`R(X) ⟶ R(U)`, `Over.mk (𝟙 X)` being the terminal object of `Over X`. -/
def sectionsModulePresheafFunctor :
    SheafOfModules.{uM} R ⥤ ((Over X)ᵒᵖ ⥤ ModuleCat.{uM} (R.obj.obj (op X))) :=
  SheafOfModules.overFunctor R X ⋙ SheafOfModules.forget (R.over X) ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 X))) Over.mkIdTerminal.op

/-- The underlying type of the module of sections of `F` over an object `U → X` is the type of
sections of `F` over `U`. -/
lemma sectionsModulePresheafFunctor_obj_obj_coe (F : SheafOfModules.{uM} R) (U : Over X) :
    (((sectionsModulePresheafFunctor R X).obj F).obj (op U) : Type uM) =
      F.val.obj (op U.left) :=
  rfl

/-- Restricting a sheaf of modules to the objects over `X` is additive. -/
instance : (SheafOfModules.overFunctor.{uM} R X).Additive where

/-- Reading a presheaf of modules as a presheaf of modules over the sections on the terminal
object is additive. -/
instance : (PresheafOfModules.forgetToPresheafModuleCat (R := (R.over X).obj)
    (op (Over.mk (𝟙 X))) Over.mkIdTerminal.op).Additive where

/-- The sections of a sheaf of `R`-modules over the objects over `X` are an additive functor of
the sheaf of modules. -/
instance sectionsModulePresheafFunctor_additive :
    (sectionsModulePresheafFunctor.{uM} R X).Additive :=
  inferInstanceAs (SheafOfModules.overFunctor R X ⋙ SheafOfModules.forget (R.over X) ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 X)))
      Over.mkIdTerminal.op).Additive

variable [UnivLE.{w, uM}]

/-- **The complex of sections `s(-(K))` of a simplicial semi-representable object `K` over `X`,
as a complex of `R(X)`-modules**, functorially in the coefficient sheaf of `R`-modules. -/
def sectionsModuleComplexFunctor (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    SheafOfModules.{uM} R ⥤ CochainComplex (ModuleCat.{uM} (R.obj.obj (op X))) ℕ :=
  sectionsModulePresheafFunctor R X ⋙ FormalCoproduct.cochainComplexFunctor K

/-- The complex of sections `s(F(K))`, as a complex of `R(X)`-modules. -/
def sectionsModuleComplex (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : SheafOfModules.{uM} R) :
    CochainComplex (ModuleCat.{uM} (R.obj.obj (op X))) ℕ :=
  (FormalCoproduct.cochainComplexFunctor K).obj ((sectionsModulePresheafFunctor R X).obj F)

/-- The value of `sectionsModuleComplexFunctor` at `F` is `sectionsModuleComplex`. -/
@[simp]
lemma sectionsModuleComplexFunctor_obj
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (F : SheafOfModules.{uM} R) :
    (sectionsModuleComplexFunctor R X K).obj F = sectionsModuleComplex R X K F :=
  rfl

/-- **The degree-`n` term of the complex of sections is the product, over the summands of the
`n`-th level of `K`, of the modules of sections of `F` on those summands.** -/
lemma sectionsModuleComplex_X (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : SheafOfModules.{uM} R) (n : ℕ) :
    (sectionsModuleComplex R X K F).X n =
      ∏ᶜ fun i : (K.obj (op ⦋n⦌)).I ↦
        ((sectionsModulePresheafFunctor R X).obj F).obj (op ((K.obj (op ⦋n⦌)).obj i)) :=
  rfl

/-- **The differential of the complex of sections is the alternating sum of the coface maps**,
`R(X)`-linearly. -/
lemma sectionsModuleComplex_d (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : SheafOfModules.{uM} R) (n : ℕ) :
    (sectionsModuleComplex R X K F).d n (n + 1) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor K).obj
          ((sectionsModulePresheafFunctor R X).obj F)).δ j :
          (sectionsModuleComplex R X K F).X n ⟶ (sectionsModuleComplex R X K F).X (n + 1)) :=
  Stacks.CechPushforward.alternatingCofaceMapComplex_obj_d
    ((FormalCoproduct.cosimplicialObjectFunctor K).obj
      ((sectionsModulePresheafFunctor R X).obj F)) n

/-- The complex of sections of `K` is an additive functor of the coefficient sheaf of modules. -/
instance sectionsModuleComplexFunctor_additive
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    (sectionsModuleComplexFunctor.{uM} R X K).Additive :=
  have : HasProducts.{w} (ModuleCat.{uM} (R.obj.obj (op X))) :=
    fun _ => ModuleCat.hasLimitsOfShape
  inferInstanceAs (sectionsModulePresheafFunctor R X ⋙
    FormalCoproduct.cochainComplexFunctor K).Additive

/-- **The complex of sections of `K` with module coefficients is contravariantly functorial in
`K`.**  A morphism `ψ : K ⟶ K'` of simplicial semi-representable objects over `X` pulls sections
on `K'` back to sections on `K`, `R(X)`-linearly and naturally in the coefficient sheaf of
modules. -/
def sectionsModuleComplexMap {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (ψ : K ⟶ K') :
    sectionsModuleComplexFunctor.{uM} R X K' ⟶ sectionsModuleComplexFunctor.{uM} R X K :=
  Functor.whiskerLeft (sectionsModulePresheafFunctor R X) (cochainComplexFunctorMap.{w} ψ)

/-- `sectionsModuleComplexMap` takes an identity to an identity. -/
@[simp]
lemma sectionsModuleComplexMap_id (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    sectionsModuleComplexMap.{uM} R X (𝟙 K) = 𝟙 _ := by
  rw [sectionsModuleComplexMap, cochainComplexFunctorMap_id]
  rfl

/-- `sectionsModuleComplexMap` reverses composition. -/
lemma sectionsModuleComplexMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    sectionsModuleComplexMap.{uM} R X (ψ ≫ φ) =
      sectionsModuleComplexMap.{uM} R X φ ≫ sectionsModuleComplexMap.{uM} R X ψ := by
  rw [sectionsModuleComplexMap, cochainComplexFunctorMap_comp]
  rfl

/-- **The complex of sections with module coefficients, as a functor of the simplicial
semi-representable object over `X`.** -/
@[simps]
def sectionsModuleComplexHypercoveringFunctor :
    (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ ⥤
      (SheafOfModules.{uM} R ⥤ CochainComplex (ModuleCat.{uM} (R.obj.obj (op X))) ℕ) where
  obj K := sectionsModuleComplexFunctor R X K.unop
  map ψ := sectionsModuleComplexMap R X ψ.unop
  map_id _ := sectionsModuleComplexMap_id R X _
  map_comp ψ φ := sectionsModuleComplexMap_comp R X φ.unop ψ.unop

/-! ### Forgetting the module structure -/

section Forget

/-- **The sections of a sheaf of `R`-modules over the objects over `X`, with the module
structure forgotten, are the sections of the underlying abelian sheaf.**  The comparison is the
identity on each group of sections. -/
def sectionsModulePresheafForgetIso :
    sectionsModulePresheafFunctor.{uM} R X ⋙
        (Functor.whiskeringRight (Over X)ᵒᵖ (ModuleCat.{uM} (R.obj.obj (op X)))
          AddCommGrpCat.{uM}).obj
            (forget₂ (ModuleCat.{uM} (R.obj.obj (op X))) AddCommGrpCat.{uM}) ≅
      SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{uM} ⋙
        (Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{uM}).obj (Over.forget X).op :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun _ ↦ NatTrans.ext (funext fun _ ↦
      (Category.comp_id _).trans (Category.id_comp _).symm))

/-- **The complex of sections of `K` with coefficients in a sheaf of `R`-modules, with the
module structure forgotten, is the complex of sections of `K` with coefficients in the
underlying abelian sheaf**, naturally in the coefficient sheaf of modules. -/
def sectionsModuleComplexForgetIso (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    sectionsModuleComplexFunctor.{max u v w} R X K ⋙
        (forget₂ (ModuleCat.{max u v w} (R.obj.obj (op X)))
          AddCommGrpCat.{max u v w}).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      SheafOfModules.toSheaf R ⋙ sectionsComplexFunctor.{w} J K :=
  Functor.isoWhiskerLeft (sectionsModulePresheafFunctor.{max u v w} R X)
      (Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIso.{w}
        (forget₂ (ModuleCat.{max u v w} (R.obj.obj (op X))) AddCommGrpCat.{max u v w}) K) ≪≫
    Functor.isoWhiskerRight (sectionsModulePresheafForgetIso.{max u v w} R X)
      (FormalCoproduct.cochainComplexFunctor K)

end Forget

end Stacks.CategoryTheory.Hypercovering.SectionsOver

end
