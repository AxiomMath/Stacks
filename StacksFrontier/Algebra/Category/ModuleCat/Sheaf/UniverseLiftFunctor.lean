module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift

/-!
# The universe lift of sheaves of modules as a fully faithful functor

The sectionwise `ULift` of sheaves of modules over a ringed site, from the modules over its
structure sheaf to the modules over the universe lift of the structure sheaf, as a functor, and
the proof that it is fully faithful.

## Main definitions

* `Stacks.SheafOfModules.CoherentLift.liftModuleFunctor`: the universe lift as a functor.
* `Stacks.SheafOfModules.CoherentLift.fullyFaithfulLiftModuleFunctor`: it is fully faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.CoherentLift

universe u v w

attribute [local implicit_reducible] liftRingedSite CategoryTheory.sheafCompose

/-- The sectionwise `ULift` of a morphism of sheaves of modules, as a morphism of the universe
lifts. -/
noncomputable def liftModuleMap (X : AlgebraicGeometry.RingedSite.{u, v, w})
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ N) :
    liftModule.{u, v, w} X M ⟶ liftModule.{u, v, w} X N where
  val :=
    { app V := ModuleCat.ofHom
        { toFun x := ULift.up (φ.val.app V x.down)
          map_add' x y := congrArg ULift.up (map_add (φ.val.app V).hom x.down y.down)
          map_smul' r x := congrArg ULift.up ((φ.val.app V).hom.map_smul r.down x.down) }
      naturality {V W} f := by
        ext x
        exact congrArg ULift.up (PresheafOfModules.naturality_apply φ.val f x.down) }

/-- The sectionwise `ULift` of sheaves of modules, from the modules over the structure sheaf of a
ringed site to the modules over its universe lift, as a functor. -/
noncomputable def liftModuleFunctor (X : AlgebraicGeometry.RingedSite.{u, v, w}) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O) where
  obj M := liftModule X M
  map φ := liftModuleMap X φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The universe lift functor sends a sheaf of modules `M` to its universe lift
`liftModule X M`. -/
@[simp]
theorem liftModuleFunctor_obj (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (liftModuleFunctor X).obj M = liftModule X M := rfl

/-- The universe lift of sheaves of modules is fully faithful: a morphism of the lifts is the
lift of the morphism it induces on `ULift.down` of sections. -/
noncomputable def fullyFaithfulLiftModuleFunctor (X : AlgebraicGeometry.RingedSite.{u, v, w}) :
    (liftModuleFunctor.{u, v, w} X).FullyFaithful where
  preimage {M N} ψ :=
    { val :=
        { app V := ModuleCat.ofHom
            { toFun x := (ψ.val.app V (ULift.up x)).down
              map_add' x y := congrArg ULift.down
                (map_add (ψ.val.app V).hom (ULift.up x) (ULift.up y))
              map_smul' r x := congrArg ULift.down
                ((ψ.val.app V).hom.map_smul (ULift.up r) (ULift.up x)) }
          naturality {V W} f := by
            ext x
            exact congrArg ULift.down (PresheafOfModules.naturality_apply ψ.val f (ULift.up x)) } }
  map_preimage ψ := rfl
  preimage_map φ := rfl

end Stacks.SheafOfModules.CoherentLift

end
