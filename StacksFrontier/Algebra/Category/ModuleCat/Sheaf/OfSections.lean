module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-!
# Sheaves of modules from module structures on sections

Let `R` be a sheaf of rings on a site and `T` a sheaf of sets. A module structure over the
sections of `R` on the sections of `T` over every object, for which every restriction map is
additive and semilinear, makes `T` the underlying sheaf of sets of a sheaf of `R`-modules.

## Main definitions

* `CategoryTheory.Sheaf.sheafOfModulesOfSections`: the sheaf of modules.

## References

* [Stacks Project, Tag 03CW](https://stacks.math.columbia.edu/tag/03CW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (T : Sheaf J (Type w))
  [∀ X : Cᵒᵖ, AddCommGroup (T.obj.obj X)] [∀ X : Cᵒᵖ, Module (R.obj.obj X) (T.obj.obj X)]

/-- The presheaf of abelian groups of sections of a sheaf of sets whose sections carry additive
group structures preserved by restriction. -/
def abPresheafOfSections
    (hadd : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (x y : T.obj.obj X),
      T.obj.map g (x + y) = T.obj.map g x + T.obj.map g y) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of (T.obj.obj X)
  map {X Y} g := AddCommGrpCat.ofHom (AddMonoidHom.mk' (T.obj.map g) (hadd g))
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
    change T.obj.map (𝟙 X) x = x
    exact T.obj.map_id_apply X x
  map_comp {X Y Z} g h := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
    change T.obj.map (g ≫ h) x = T.obj.map h (T.obj.map g x)
    exact T.obj.map_comp_apply g h x

/-- **A sheaf of modules from module structures on the sections of a sheaf of sets**, for which
every restriction map is additive and semilinear. -/
def sheafOfModulesOfSections
    (hadd : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (x y : T.obj.obj X),
      T.obj.map g (x + y) = T.obj.map g x + T.obj.map g y)
    (hsmul : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (r : R.obj.obj X) (x : T.obj.obj X),
      T.obj.map g (r • x) = R.obj.map g r • T.obj.map g x) :
    SheafOfModules.{w} R where
  val :=
    letI : ∀ X : Cᵒᵖ, Module (R.obj.obj X) ((abPresheafOfSections T hadd).obj X) := fun X ↦
      inferInstanceAs (Module (R.obj.obj X) (T.obj.obj X))
    PresheafOfModules.ofPresheaf (abPresheafOfSections T hadd) (fun {_X _Y} g r m ↦ hsmul g r m)
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{w}) T.property

/-- The underlying sheaf of sets of the sheaf of modules defined by module structures on
sections is the given sheaf of sets. -/
lemma moduleSheaf_sheafOfModulesOfSections [J.HasSheafCompose (forget RingCat.{w})] (hadd)
    (hsmul) : moduleSheaf R (sheafOfModulesOfSections R T hadd hsmul) = T := rfl

end CategoryTheory.Sheaf

end
