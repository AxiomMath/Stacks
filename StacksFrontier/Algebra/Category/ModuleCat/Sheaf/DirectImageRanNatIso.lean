module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage

/-!
# The underlying abelian presheaf of a direct image of modules is a right Kan extension

Let `f : C ⥤ D` be a functor and `R` a presheaf of rings on `D`. The direct image
`PresheafOfModules.directImage f R` of presheaves of modules has, as underlying presheaf of
abelian groups, the right Kan extension along `f.op` of the underlying presheaf of abelian groups
(`PresheafOfModules.directImageRanIso`). This file makes that identification natural in the
module, on presheaves and on sheaves of modules.

## Main definitions

* `PresheafOfModules.directImageCompToPresheafIso`: `f_* ⋙ forget ≅ forget ⋙ Ran_{f.op}`, on
  presheaves of modules.
* `SheafOfModules.directImageOfEqCompToPresheafIso`: the same for the direct image of sheaves of
  modules along a continuous and cocontinuous functor, followed by the underlying presheaf of
  abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe r w vC vD uC uD

namespace PresheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{r})

/-- The counit of the direct image, with source and target written through `toPresheaf`. -/
abbrev directImageCounitToPresheaf (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R)) :
    f.op ⋙ (toPresheaf R).obj ((directImage.{r, w} f R).obj N) ⟶ (toPresheaf (f.op ⋙ R)).obj N :=
  directImageCounit.{r, w} f R N

/-- `PresheafOfModules.directImageRanIso`, with source and target written through `toPresheaf`. -/
abbrev directImageRanIsoToPresheaf (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R)) :
    (toPresheaf R).obj ((directImage.{r, w} f R).obj N) ≅
      f.op.ran.obj ((toPresheaf (f.op ⋙ R)).obj N) :=
  directImageRanIso.{r, w} f R N

/-- The counit of the direct image of presheaves of modules is natural in the module. -/
lemma directImageCounitToPresheaf_naturality {N N' : PresheafOfModules.{max uC vD w} (f.op ⋙ R)}
    (g : N ⟶ N') :
    Functor.whiskerLeft f.op ((toPresheaf R).map ((directImage.{r, w} f R).map g)) ≫
        directImageCounitToPresheaf.{r, w} f R N' =
      directImageCounitToPresheaf.{r, w} f R N ≫ (toPresheaf (f.op ⋙ R)).map g := by
  ext x s
  rfl

/-- `PresheafOfModules.directImageRanIso_fac`, through `toPresheaf`. -/
lemma directImageRanIsoToPresheaf_fac (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R)) :
    Functor.whiskerLeft f.op (directImageRanIsoToPresheaf.{r, w} f R N).hom ≫
        f.op.ranCounit.app ((toPresheaf (f.op ⋙ R)).obj N) =
      directImageCounitToPresheaf.{r, w} f R N :=
  directImageRanIso_fac.{r, w} f R N

/-- **The underlying presheaf of abelian groups of the direct image is the right Kan extension of
the underlying presheaf, naturally in the module**: `f_* ⋙ forget ≅ forget ⋙ Ran_{f.op}`. Its
components are `PresheafOfModules.directImageRanIso`. -/
def directImageCompToPresheafIso :
    directImage.{r, w} f R ⋙ toPresheaf R ≅ toPresheaf (f.op ⋙ R) ⋙ f.op.ran :=
  NatIso.ofComponents (fun N => directImageRanIsoToPresheaf.{r, w} f R N) (fun {N N'} g => by
    apply Functor.hom_ext_of_isRightKanExtension _
      (f.op.ranCounit.app ((toPresheaf (f.op ⋙ R)).obj N'))
    have h3 : Functor.whiskerLeft f.op (f.op.ran.map ((toPresheaf (f.op ⋙ R)).map g)) ≫
        f.op.ranCounit.app ((toPresheaf (f.op ⋙ R)).obj N') =
          f.op.ranCounit.app ((toPresheaf (f.op ⋙ R)).obj N) ≫ (toPresheaf (f.op ⋙ R)).map g :=
      (f.op.ranCounit).naturality ((toPresheaf (f.op ⋙ R)).map g)
    simp only [Functor.comp_map, Functor.whiskerLeft_comp, Category.assoc,
      directImageRanIsoToPresheaf_fac, h3, directImageCounitToPresheaf_naturality]
    rw [← Category.assoc, directImageRanIsoToPresheaf_fac])

end PresheafOfModules

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})

/-- **The underlying presheaf of abelian groups of the direct image of a sheaf of modules is the
right Kan extension of the underlying presheaf**, naturally in the module, for the direct image
`SheafOfModules.directImageOfEq` along a continuous and cocontinuous functor `f`. -/
def directImageOfEqCompToPresheafIso {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    directImageOfEq.{r, w} f J K O hT ⋙ SheafOfModules.forget O ⋙
        PresheafOfModules.toPresheaf O.obj ≅
      SheafOfModules.forget T ⋙ PresheafOfModules.toPresheaf T.obj ⋙ f.op.ran := by
  subst hT
  exact Functor.isoWhiskerLeft
    (SheafOfModules.forget.{max uC vD w} ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O))
    (PresheafOfModules.directImageCompToPresheafIso.{r, w} f O.obj)

end SheafOfModules

end
