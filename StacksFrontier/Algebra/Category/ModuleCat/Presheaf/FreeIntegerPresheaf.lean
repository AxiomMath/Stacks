module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.Grp.FreeAbelianAsFreeIntModule
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeSplitUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleFreeSum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The free presheaf of modules over the constant integers is a free abelian presheaf

Over the constant presheaf of rings `ℤ` on a category `C`, the free presheaf of modules
`PresheafOfModules.freeObj E` on a presheaf of types `E` has the same underlying presheaf of
abelian groups as the free abelian presheaf on `E`, namely `E ⋙ AddCommGrpCat.free`. Sheafifying,
the underlying abelian sheaf of the sheafification of `freeObj E` is the sheafification of the
free abelian presheaf on `E`.

This is what lets the projection formula of Stacks 0D9E be run inside sheaves of modules. The
object it is about, the lower shriek image `g_{n!}Z` of a constant integer sheaf, is produced by
the integral resolution of Stacks 09WI as the sheafification of a *free abelian* presheaf, while
the tensor product it has to be fed to is the tensor product of sheaves of *modules*, whose free
objects are `PresheafOfModules.freeObj`. The comparison of the two notions of freeness is
`AddCommGrpCat.freeIsoFreeIntModule`; this file carries it through the presheaf of modules and
its sheafification.

## Main definitions

* `PresheafOfModules.intRingPresheaf`: the constant presheaf of rings `ℤ`, at the universe of the
  sections. This is the presheaf of rings whose sheafification is the constant sheaf of rings `ℤ`
  over which abelian sheaves are sheaves of modules.

## Main results

* `PresheafOfModules.freeObjToPresheafIso`: the underlying presheaf of abelian groups of
  `freeObj E` is `E ⋙ AddCommGrpCat.freeIntModule`.
* `PresheafOfModules.freeObjToFreeAbIso`: **it is the free abelian presheaf on `E`.**
* `PresheafOfModules.sheafifyFreeObjIso`: **the underlying abelian sheaf of the sheafification of
  `freeObj E` is the sheafification of the free abelian presheaf on `E`.**

## Implementation notes

`intRingPresheaf` is an `abbrev`, so that it unifies with the constant presheaf of rings written
out — which is how the scalars of the constant sheaf of rings `ℤ` are spelled where they are
constructed — without a rewrite.

`freeObjToPresheafIso` is the identity on sections: the two presheaves differ only in how their
restriction maps are written, `freeObj` taking its from the universal property of the free module
and the whiskered functor taking its from `Finsupp.lmapDomain`, and the two agree on the summand
inclusions.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace PresheafOfModules

section Const

variable {C : Type u} [Category.{v} C]

/-- The constant presheaf of rings `ℤ`, at the universe of the sections. -/
@[sga "3 I 3.1.3"]
abbrev intRingPresheaf (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u} ℤ))

/-- The underlying presheaf of abelian groups of the free presheaf of modules on `E` over the
constant presheaf of rings `ℤ` is the free module over the integers on the sections of `E`, taken
objectwise. It is the identity on sections; the two restriction maps agree on the summand
inclusions. -/
def freeObjToPresheafIso (E : Cᵒᵖ ⥤ Type u) :
    (toPresheaf (intRingPresheaf C)).obj (freeObj E) ≅ E ⋙ AddCommGrpCat.freeIntModule.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro x n
    change ModuleCat.Hom.hom ((freeObj E).map f) (Finsupp.single x n) =
      AddCommGrpCat.Hom.hom (AddCommGrpCat.freeIntModule.map (E.map f)) (Finsupp.single x n)
    rw [AddCommGrpCat.freeIntModule_map_single, freeObj_map_single]
    rfl)

/-- **The free presheaf of modules on `E` over the constant presheaf of rings `ℤ` is the free
abelian presheaf on `E`**, on underlying presheaves of abelian groups. -/
def freeObjToFreeAbIso (E : Cᵒᵖ ⥤ Type u) :
    (toPresheaf (intRingPresheaf C)).obj (freeObj E) ≅ E ⋙ AddCommGrpCat.free.{u} :=
  freeObjToPresheafIso E ≪≫
    (Functor.isoWhiskerLeft E AddCommGrpCat.freeIsoFreeIntModule.{u}).symm

end Const

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (α : intRingPresheaf C ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **The underlying abelian sheaf of the sheafification of the free presheaf of modules on `E` is
the sheafification of the free abelian presheaf on `E`.** -/
def sheafifyFreeObjIso (E : Cᵒᵖ ⥤ Type u) :
    (SheafOfModules.toSheaf R).obj ((sheafification α).obj (freeObj E)) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj (E ⋙ AddCommGrpCat.free.{u}) :=
  (sheafificationCompToSheaf α).app (freeObj E) ≪≫
    (presheafToSheaf J AddCommGrpCat.{u}).mapIso (freeObjToFreeAbIso E)

end Sheafify

end PresheafOfModules

end
