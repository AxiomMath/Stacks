module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso

/-!
# The two spellings of the direct image of modules and composition

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` be morphisms of ringed topoi in the sense of
Stacks 01D3, part (2), and let `τ : f_* ⋙ g_* ≅ h_*` be a comparison of the geometric direct
images carrying the composite structure map to that of `h`.  The direct image of sheaves of
modules exists in two spellings, `AlgebraicGeometry.RingedToposHom.pushforwardModules` and the
direct image of the four-field morphism of ringed topoi of the modules development, compared by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`.  Each spelling has a comparison of the
iterated direct image with the direct image along `h`; this file proves that the comparisons
correspond, whenever the comparison in the first spelling is `τ` on underlying sheaves of sets.

## Main results

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso_comp_comparison`: the two comparisons
  `g_*(f_*M) ⟶ h_*M` agree after the identification of the two spellings.

## Implementation notes

Both sides are compared on underlying sheaves of sets, where each identification of spellings
is the identity.  Each step is a separate declaration: the kernel identifies the underlying
sheaf of a direct image with the direct image of an underlying sheaf at every step, each such
identification is affordable on its own, and a single chain of them is not.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

section Key

variable (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

private theorem map_pushforwardModules_map_eq :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toRingedToposModulesHom).map
        (f.pushforwardModulesIso.hom.app M)) =
      g.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (f.pushforwardModulesIso.hom.app M)) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModules_map
    g.toRingedToposModulesHom (f.pushforwardModulesIso.hom.app M)

omit [Z.J.HasSheafCompose (forget AddCommGrpCat)] in
private theorem map_moduleSheafFunctor_map_pushforwardModulesIso :
    g.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (f.pushforwardModulesIso.hom.app M)) =
      g.toToposHom.pushforward.map
        (𝟙 (f.toToposHom.pushforward.obj (Sheaf.moduleSheaf _ M))) :=
  congrArg g.toToposHom.pushforward.map (moduleSheafFunctor_map_pushforwardModulesIso f M)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [Z.J.HasSheafCompose (forget AddCommGrpCat)] in
private theorem map_id_pushforward_pushforward :
    g.toToposHom.pushforward.map
        (𝟙 (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) =
      𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) :=
  g.toToposHom.pushforward.map_id _

private theorem map_pushforwardModules_map_pushforwardModulesIso :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toRingedToposModulesHom).map
        (f.pushforwardModulesIso.hom.app M)) =
      𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) :=
  (map_pushforwardModules_map_eq f g M).trans
    ((map_moduleSheafFunctor_map_pushforwardModulesIso f g M).trans
      (map_id_pushforward_pushforward f g M))

private theorem map_pushforwardModulesIso_pushforward :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      (g.pushforwardModulesIso.hom.app (f.pushforwardModules.obj M)) =
      𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) :=
  moduleSheafFunctor_map_pushforwardModulesIso g (f.pushforwardModules.obj M)

private theorem map_pushforwardModulesIso_comp :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toRingedToposModulesHom).map
        (f.pushforwardModulesIso.hom.app M)) ≫
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      (g.pushforwardModulesIso.hom.app (f.pushforwardModules.obj M)) =
      (𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) ≫
       𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)))) :=
  congrArg₂ (· ≫ ·) (map_pushforwardModules_map_pushforwardModulesIso f g M)
    (map_pushforwardModulesIso_pushforward f g M)

end Key

section KeyFinal

variable (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (h : RingedToposHom X Z)
    (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ h.toToposHom.pushforward)
    (hτ : Stacks.Sheaves.RingedToposModules.fSharpSetComp f.toRingedToposModulesHom
        g.toRingedToposModulesHom ≫
      τ.hom.app (Stacks.SheafOfModules.Tensor.ringSheaf X.O).ringSheaf =
        Stacks.Sheaves.RingedToposModules.fSharpSet h.toRingedToposModulesHom)
    (T : f.pushforwardModules ⋙ g.pushforwardModules ≅ h.pushforwardModules)
    (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hT : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (T.hom.app M) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))

include hT in
private theorem map_pushforwardModulesIso_comp_comp :
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toRingedToposModulesHom).map
        (f.pushforwardModulesIso.hom.app M)) ≫
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      (g.pushforwardModulesIso.hom.app (f.pushforwardModules.obj M))) ≫
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map (T.hom.app M) =
      (𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) ≫
       𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)))) ≫
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
  congrArg₂ (· ≫ ·) (map_pushforwardModulesIso_comp f g M) hT

private theorem map_pushforwardModulesCompIso_comp :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f.toRingedToposModulesHom
        g.toRingedToposModulesHom h.toRingedToposModulesHom τ hτ).hom.app M) ≫
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (h.pushforwardModulesIso.hom.app M) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) ≫
        𝟙 (h.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :=
  congrArg₂ (· ≫ ·)
    (Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
      f.toRingedToposModulesHom g.toRingedToposModulesHom h.toRingedToposModulesHom τ hτ M)
    (moduleSheafFunctor_map_pushforwardModulesIso h M)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [Z.J.HasSheafCompose (forget AddCommGrpCat)] in
private theorem id_comp_id_comp_eq :
    (𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) ≫
       𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)))) ≫
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) =
    τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) ≫
        𝟙 (h.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) := by
  simp

end KeyFinal

/-- **The two comparisons `g_*(f_*M) ⟶ h_*M` agree.**  Let `τ : f_* ⋙ g_* ≅ h_*` compare the
geometric direct images compatibly with the structure maps, and let
`T : f_* ⋙ g_* ≅ h_*` be a comparison of the direct images of sheaves of modules of Stacks 01D3
which is `τ` on the underlying sheaf of sets of `M`.  Then `T` at `M`, read through the
identification `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso` of the two spellings of
the direct image, is the comparison
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso` of the modules development. -/
theorem pushforwardModulesIso_comp_comparison (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom X Z)
    (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ h.toToposHom.pushforward)
    (hτ : Stacks.Sheaves.RingedToposModules.fSharpSetComp f.toRingedToposModulesHom
        g.toRingedToposModulesHom ≫
      τ.hom.app (Stacks.SheafOfModules.Tensor.ringSheaf X.O).ringSheaf =
        Stacks.Sheaves.RingedToposModules.fSharpSet h.toRingedToposModulesHom)
    (T : f.pushforwardModules ⋙ g.pushforwardModules ≅ h.pushforwardModules)
    (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hT : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (T.hom.app M) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :
    ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toRingedToposModulesHom).map
        (f.pushforwardModulesIso.hom.app M) ≫
      g.pushforwardModulesIso.hom.app (f.pushforwardModules.obj M)) ≫ T.hom.app M =
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f.toRingedToposModulesHom
        g.toRingedToposModulesHom h.toRingedToposModulesHom τ hτ).hom.app M ≫
        h.pushforwardModulesIso.hom.app M := by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  exact ((map_pushforwardModulesIso_comp_comp f g h τ T M hT).trans
    (id_comp_id_comp_eq f g h τ M)).trans (map_pushforwardModulesCompIso_comp f g h τ hτ M).symm


end AlgebraicGeometry.RingedToposHom

end
