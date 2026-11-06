module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# The inverse image of sheaves of modules and multiplication by global sections

Let `Φ : Sh(D) ⥤ Sh(C)` be a finite-product-preserving functor between categories of sheaves of
sets — for instance the inverse image of a morphism of topoi — and let `O` be a sheaf of rings on
`D`.  The inverse image `Φ O` of `O` and of its modules carry the transported algebraic
structures of Stacks 03D2 (`Stacks.Sheaves.ToposPullback.pullbackRingSheaf`,
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor`).  A global section `a` of `O`, that is a
morphism `* ⟶ O` from the terminal sheaf, is carried by `Φ` to a global section `Φ a` of `Φ O`,
and this file records that the inverse image of multiplication by `a` on an `O`-module `M` is
multiplication by `Φ a` on `Φ M`.

## Main definitions

* `Stacks.Sheaves.ToposPullback.globalSectionHom`: a global section of a sheaf of rings as a
  morphism from the terminal sheaf of sets.
* `Stacks.Sheaves.ToposPullback.pullbackGlobalSectionHom`: the ring homomorphism
  `Γ(O) ⟶ Γ(Φ O)` on global sections.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackModuleFunctor_map_globalSmul`: the inverse image of
  multiplication by `a` is multiplication by the transported section.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor Opposite
open scoped IsMulCommutative

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- A global section of a sheaf of rings, as a morphism from the terminal sheaf of sets to its
underlying sheaf of sets. -/
def globalSectionHom (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O) :
    ⊤_ (Sheaf K (Type ww')) ⟶ ringSheaf O :=
  constHom (E := ringSheaf O) (fun X ↦ a.1 X) (fun g ↦ a.2 g)

/-- Over `X`, the morphism `globalSectionHom O a` sends the section of the terminal sheaf to the
value of `a` over `X`. -/
@[simp]
lemma sectionsFunctor_map_globalSectionHom (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O)
    (X : Dᵒᵖ) (p : (sectionsFunctor K X).obj (⊤_ (Sheaf K (Type ww')))) :
    (sectionsFunctor K X).map (globalSectionHom O a) p = a.1 X := rfl

/-- The section over `X` of `Φ O` obtained by applying `Φ` to a global section of `O`. -/
def pullbackGlobalSectionApp (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O) (X : Cᵒᵖ) :
    (pullbackRingSheaf J Φ O).obj.obj X :=
  (Φ ⋙ sectionsFunctor J X).map (globalSectionHom O a) default

/-- **The global section of `Φ O` transported from a global section of `O`.** -/
def pullbackGlobalSection (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O) :
    Stacks.Cohomology.SiteModules.GlobalSectionRing (pullbackRingSheaf J Φ O) :=
  ⟨pullbackGlobalSectionApp J Φ O a, fun {X Y} g ↦ by
    change (whiskerLeft Φ (sectionsRestrict g)).app (ringSheaf O)
        ((Φ ⋙ sectionsFunctor J X).map (globalSectionHom O a) default) =
      (Φ ⋙ sectionsFunctor J Y).map (globalSectionHom O a) default
    rw [natTrans_app_map_apply]
    exact congrArg _ (Subsingleton.elim _ _)⟩

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The value over `X` of `pullbackGlobalSection J Φ O a` is the image of the section of the
terminal sheaf under `Φ (globalSectionHom O a)`. -/
lemma pullbackGlobalSection_apply (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O)
    (X : Cᵒᵖ) :
    (pullbackGlobalSection J Φ O a).1 X =
      (Φ ⋙ sectionsFunctor J X).map (globalSectionHom O a) default := rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- The morphism of a product of global sections `a * b` is the pairing of the morphisms of `a`
and `b` followed by the multiplication of `O`. -/
lemma globalSectionHom_mul (a b : Stacks.Cohomology.SiteModules.GlobalSectionRing O) :
    globalSectionHom O (a * b) =
      prod.lift (globalSectionHom O a) (globalSectionHom O b) ≫ ringMulHom O := by
  refine hom_ext_sections fun X p ↦ ?_
  rw [Functor.map_comp_apply, map_lift_apply, sectionsFunctor_map_ringMulHom]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- The morphism of a sum of global sections `a + b` is the pairing of the morphisms of `a` and
`b` followed by the addition of `O`. -/
lemma globalSectionHom_add (a b : Stacks.Cohomology.SiteModules.GlobalSectionRing O) :
    globalSectionHom O (a + b) =
      prod.lift (globalSectionHom O a) (globalSectionHom O b) ≫ ringAddHom O := by
  refine hom_ext_sections fun X p ↦ ?_
  rw [Functor.map_comp_apply, map_lift_apply, sectionsFunctor_map_ringAddHom]
  rfl

/-- The morphism of the global section `1` is the unit `ringOneHom O` of `O`. -/
lemma globalSectionHom_one :
    globalSectionHom O (1 : Stacks.Cohomology.SiteModules.GlobalSectionRing O) = ringOneHom O :=
  hom_ext_sections fun _ _ ↦ rfl

/-- The morphism of the global section `0` is the zero `ringZeroHom O` of `O`. -/
lemma globalSectionHom_zero :
    globalSectionHom O (0 : Stacks.Cohomology.SiteModules.GlobalSectionRing O) = ringZeroHom O :=
  hom_ext_sections fun _ _ ↦ rfl

/-- **The ring homomorphism `Γ(O) ⟶ Γ(Φ O)` on global sections.** -/
def pullbackGlobalSectionHom :
    Stacks.Cohomology.SiteModules.GlobalSectionRing O →+*
      Stacks.Cohomology.SiteModules.GlobalSectionRing (pullbackRingSheaf J Φ O) where
  toFun := pullbackGlobalSection J Φ O
  map_one' := Subtype.ext (funext fun X ↦ by
    change (Φ ⋙ sectionsFunctor J X).map (globalSectionHom O 1) default = ringOneObj O _
    rw [globalSectionHom_one]
    rfl)
  map_mul' a b := Subtype.ext (funext fun X ↦ by
    change (Φ ⋙ sectionsFunctor J X).map (globalSectionHom O (a * b)) default =
      ringMulObj O _ ((Φ ⋙ sectionsFunctor J X).map (globalSectionHom O a) default)
        ((Φ ⋙ sectionsFunctor J X).map (globalSectionHom O b) default)
    rw [globalSectionHom_mul, Functor.map_comp, types_comp_apply, map_lift_apply]
    rfl)
  map_zero' := Subtype.ext (funext fun X ↦ by
    change (Φ ⋙ sectionsFunctor J X).map (globalSectionHom O 0) default = ringZeroObj O _
    rw [globalSectionHom_zero]
    rfl)
  map_add' a b := Subtype.ext (funext fun X ↦ by
    change (Φ ⋙ sectionsFunctor J X).map (globalSectionHom O (a + b)) default =
      ringAddObj O _ ((Φ ⋙ sectionsFunctor J X).map (globalSectionHom O a) default)
        ((Φ ⋙ sectionsFunctor J X).map (globalSectionHom O b) default)
    rw [globalSectionHom_add, Functor.map_comp, types_comp_apply, map_lift_apply]
    rfl)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- `pullbackGlobalSectionHom J Φ O` sends `a` to `pullbackGlobalSection J Φ O a`. -/
lemma pullbackGlobalSectionHom_apply (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O) :
    pullbackGlobalSectionHom J Φ O a = pullbackGlobalSection J Φ O a := rfl

variable [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  [∀ X : Dᵒᵖ, IsMulCommutative (O.obj.obj X)]
  [∀ X : Cᵒᵖ, IsMulCommutative ((pullbackRingSheaf J Φ O).obj.obj X)]

/-- Multiplication by a global section, on the underlying sheaf of sets of a module: it is the
scalar multiplication map precomposed with the section. -/
lemma moduleSheafFunctor_map_globalSmul (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O)
    (M : SheafOfModules.{ww'} O) :
    (moduleSheafFunctor O).map (Stacks.Cohomology.SiteModules.globalSmul O a M) =
      prod.lift (terminal.from _ ≫ globalSectionHom O a) (𝟙 _) ≫ moduleSMulHom O M := by
  refine hom_ext_sections fun X s ↦ ?_
  rw [Functor.map_comp_apply, map_lift_apply, sectionsFunctor_map_moduleSMulHom]
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- **The inverse image of multiplication by a global section `a` is multiplication by the
transported section `Φ a`.** -/
theorem pullbackModuleFunctor_map_globalSmul
    (a : Stacks.Cohomology.SiteModules.GlobalSectionRing O) (M : SheafOfModules.{ww'} O) :
    (pullbackModuleFunctor J Φ O).map (Stacks.Cohomology.SiteModules.globalSmul O a M) =
      Stacks.Cohomology.SiteModules.globalSmul (pullbackRingSheaf J Φ O)
        (pullbackGlobalSectionHom J Φ O a) ((pullbackModuleFunctor J Φ O).obj M) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun X ↦ ?_))
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine (pullbackModuleMap_val_app_apply J Φ O _ X x).trans ?_
  have key (y : (Φ ⋙ sectionsFunctor J X).obj (moduleSheaf O M)) :
      (Φ ⋙ sectionsFunctor J X).map
          ((moduleSheafFunctor O).map (Stacks.Cohomology.SiteModules.globalSmul O a M)) y =
        moduleSMulObj O M (Φ ⋙ sectionsFunctor J X) (pullbackGlobalSectionApp J Φ O a X) y := by
    rw [moduleSheafFunctor_map_globalSmul, Functor.map_comp_apply, map_lift_apply,
      Functor.map_comp_apply, map_terminalFrom_apply, Functor.map_id_apply]
    rfl
  exact key x

end Stacks.Sheaves.ToposPullback

end
