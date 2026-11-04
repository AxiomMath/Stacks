module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules

/-!
# Functors to torsion abelian sheaves, read as functors to sheaves of `ℤ/mℤ`-modules

This file continues `StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules`. A
functor to abelian presheaves (resp. sheaves) all of whose values are annihilated by `m` is read
as a functor to presheaves (resp. sheaves) of modules over the constant presheaf (resp. sheaf) of
rings `ℤ/mℤ`, objectwise by `Stacks.Cohomology.ZModSheaf.torsionPresheafToModules` (resp.
`Stacks.Cohomology.ZModSheaf.torsionSheafToModules`). Additivity is inherited, and the underlying
abelian presheaves (resp. sheaves) are unchanged.

## Main definitions

* `Stacks.Cohomology.ZModSheaf.torsionPresheafToModulesFunctor` and
  `Stacks.Cohomology.ZModSheaf.torsionSheafToModulesFunctor` — the functors.
* `Stacks.Cohomology.ZModSheaf.torsionPresheafToModulesFunctorCompToPresheaf` and
  `Stacks.Cohomology.ZModSheaf.torsionSheafToModulesFunctorCompToSheaf` — their underlying
  abelian presheaves, resp. sheaves, are those of the given functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t s v u

namespace Stacks.Cohomology.ZModSheaf

section Scalars

variable {m : ℕ}

variable {C : Type u} [Category.{v} C]

/-- An additive morphism of abelian presheaves annihilated by `m`, read as a morphism of the
attached presheaves of modules over the constant presheaf of rings `ℤ/mℤ`: it is automatically
linear (`map_smul_of_isAddHom`). -/
public def torsionPresheafToModulesMap {M N : Cᵒᵖ ⥤ AddCommGrpCat.{t}}
    (hM : ∀ (X : Cᵒᵖ) (x : ToType (M.obj X)), m • x = 0)
    (hN : ∀ (X : Cᵒᵖ) (x : ToType (N.obj X)), m • x = 0) (φ : M ⟶ N) :
    torsionPresheafToModules.{t, s} M hM ⟶ torsionPresheafToModules.{t, s} N hN :=
  PresheafOfModules.homMk φ (fun X r x ↦ by
    let := uliftZModModule.{s} (hM X)
    let := uliftZModModule.{s} (hN X)
    exact map_smul_of_isAddHom (φ.app X).hom r x)

/-- A functor to abelian presheaves all of whose values are annihilated by `m`, read as a functor
to presheaves of modules over the constant presheaf of rings `ℤ/mℤ`. -/
public def torsionPresheafToModulesFunctor {A : Type*} [Category A]
    (F : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (hF : ∀ (a : A) (X : Cᵒᵖ) (x : ToType ((F.obj a).obj X)), m • x = 0) :
    A ⥤ PresheafOfModules.{t} (zmodPresheaf.{s} C m) where
  obj a := torsionPresheafToModules.{t, s} (F.obj a) (hF a)
  map φ := torsionPresheafToModulesMap.{t, s} (hF _) (hF _) (F.map φ)
  map_id a := (PresheafOfModules.toPresheaf _).map_injective (by
    change F.map (𝟙 a) = 𝟙 (F.obj a)
    exact F.map_id a)
  map_comp φ ψ := (PresheafOfModules.toPresheaf _).map_injective (by
    change F.map (φ ≫ ψ) = F.map φ ≫ F.map ψ
    exact F.map_comp φ ψ)

/-- Reading an additive functor to abelian presheaves annihilated by `m` as a functor to
presheaves of modules gives an additive functor. -/
public instance torsionPresheafToModulesFunctor_additive {A : Type*} [Category A] [Preadditive A]
    (F : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{t}) [F.Additive]
    (hF : ∀ (a : A) (X : Cᵒᵖ) (x : ToType ((F.obj a).obj X)), m • x = 0) :
    (torsionPresheafToModulesFunctor.{t, s} F hF).Additive where
  map_add {_ _ φ ψ} := (PresheafOfModules.toPresheaf _).map_injective (by
    rw [(PresheafOfModules.toPresheaf _).map_add]
    change F.map (φ + ψ) = F.map φ + F.map ψ
    exact F.map_add)

/-- Reading a functor to abelian presheaves annihilated by `m` as a functor to presheaves of
modules does not change the underlying abelian presheaves. -/
public def torsionPresheafToModulesFunctorCompToPresheaf {A : Type*} [Category A]
    (F : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (hF : ∀ (a : A) (X : Cᵒᵖ) (x : ToType ((F.obj a).obj X)), m • x = 0) :
    torsionPresheafToModulesFunctor.{t, s} F hF ⋙ PresheafOfModules.toPresheaf _ ≅ F :=
  Iso.refl _

end Scalars

section RingSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (m : ℕ)
  [HasSheafify J CommRingCat.{s}]

variable [J.WEqualsLocallyBijective CommRingCat.{s}]

variable [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **A functor to abelian sheaves all of whose values are annihilated by `m`, read as a functor
to sheaves of modules over the constant sheaf of rings `ℤ/mℤ`**: the value at `a` is
`torsionSheafToModules J m (F.obj a)`. -/
public def torsionSheafToModulesFunctor {A : Type*} [Category A]
    (F : A ⥤ Sheaf J AddCommGrpCat.{t})
    (hF : ∀ (a : A) (X : Cᵒᵖ) (x : ToType ((F.obj a).obj.obj X)), m • x = 0) :
    A ⥤ SheafOfModules.{t} (zmodRingSheaf.{s} J m) :=
  torsionPresheafToModulesFunctor.{t, s} (F ⋙ sheafToPresheaf J AddCommGrpCat.{t}) hF ⋙
    PresheafOfModules.sheafification (zmodRingMap.{s} J m)

/-- Reading an additive functor to abelian sheaves annihilated by `m` as a functor to sheaves of
modules gives an additive functor. -/
public instance torsionSheafToModulesFunctor_additive {A : Type*} [Category A] [Preadditive A]
    (F : A ⥤ Sheaf J AddCommGrpCat.{t}) [F.Additive]
    (hF : ∀ (a : A) (X : Cᵒᵖ) (x : ToType ((F.obj a).obj.obj X)), m • x = 0) :
    (torsionSheafToModulesFunctor.{t, s} J m F hF).Additive :=
  have : (PresheafOfModules.sheafification (zmodRingMap.{s} J m)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (zmodRingMap.{s} J m)).left_adjoint_additive
  inferInstanceAs (torsionPresheafToModulesFunctor.{t, s} (F ⋙ sheafToPresheaf J AddCommGrpCat.{t})
    hF ⋙ PresheafOfModules.sheafification (zmodRingMap.{s} J m)).Additive

/-- **The underlying abelian sheaves of `torsionSheafToModulesFunctor J m F hF` are those of `F`,
naturally**: sheafification undoes the inclusion of sheaves into presheaves. -/
public def torsionSheafToModulesFunctorCompToSheaf {A : Type*} [Category A]
    (F : A ⥤ Sheaf J AddCommGrpCat.{t})
    (hF : ∀ (a : A) (X : Cᵒᵖ) (x : ToType ((F.obj a).obj.obj X)), m • x = 0) :
    torsionSheafToModulesFunctor.{t, s} J m F hF ⋙ SheafOfModules.toSheaf _ ≅ F :=
  Functor.isoWhiskerLeft F (sheafificationNatIso J AddCommGrpCat.{t}).symm

end RingSheaf

end Stacks.Cohomology.ZModSheaf

end
