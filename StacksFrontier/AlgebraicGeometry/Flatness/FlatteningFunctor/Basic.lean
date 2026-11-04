module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The flatness functor of a quasi-coherent module

For a morphism of schemes `f : X ⟶ S` and a quasi-coherent `𝒪_X`-module `F`, pull `F` back to
`X ×_S T` for every scheme `T` over `S`. Flatness of this pullback over `T` is stable under a
further base change, and hence defines a subterminal set-valued functor on schemes over `S`:
the *flatness functor* of `F`. Its representability is what the flattening problem asks about.

## Main definitions

* `AlgebraicGeometry.FlatnessSituation` bundles the morphism and the quasi-coherent module.
* `AlgebraicGeometry.FlatnessSituation.baseChange` and
  `AlgebraicGeometry.FlatnessSituation.baseChangeModule` give the base-changed scheme and the
  base-changed module.
* `AlgebraicGeometry.FlatnessSituation.IsFlatAfterBaseChange` is the flatness condition.
* `AlgebraicGeometry.FlatnessSituation.flatFunctor` is the associated functor.

## Main results

* `AlgebraicGeometry.FlatnessSituation.isFlatAfterBaseChange_of_hom` is stability of flatness
  under a further base change.
* `AlgebraicGeometry.FlatnessSituation.flatFunctor_obj_nonempty_iff` characterizes the
  nonempty values of the functor.

## Implementation notes

Schemes over `S` form `Over S`. The base-changed module is the canonical pullback along the
first projection of the fibre product. The functor takes values in `PLift` of the flatness
proposition, a singleton when flatness holds and the empty type otherwise; its action on
morphisms is base-change stability.

Base-change stability is deduced from `AlgebraicGeometry.modulePullback_isFlatOver` applied to
the square comparing the two fibre products, followed by the transfer of flatness along the
comparison isomorphism `AlgebraicGeometry.schemeModulePullbackCompIso`.

## References

* [Stacks Project, Tag 05MW](https://stacks.math.columbia.edu/tag/05MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes together with a quasi-coherent module on its source. -/
@[stacks 05MW "the situation"]
public structure FlatnessSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The scheme morphism. -/
  f : X ⟶ S
  /-- The module whose base changes are tested for flatness. -/
  F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)
  [isQuasicoherent : F.IsQuasicoherent]

namespace FlatnessSituation

attribute [instance] isQuasicoherent

/-- The fibre product `X ×_S T`. -/
@[stacks 05MW "the base-changed scheme"]
public noncomputable abbrev baseChange (D : FlatnessSituation.{u})
    (T : Over D.S) : Scheme.{u} :=
  pullback D.f T.hom

/-- The pullback of the module to `X ×_S T`. -/
@[stacks 05MW "the base-changed module"]
public noncomputable abbrev baseChangeModule (D : FlatnessSituation.{u})
    (T : Over D.S) :
    SheafOfModules.{u} (structureSheafRing (D.baseChange T).toRingedSpace) :=
  (modulePullback (pullback.fst D.f T.hom).toLRSHom.toShHom).obj D.F

/-- The base-changed module is flat over `T`. -/
@[stacks 05MW "the flatness condition"]
public abbrev IsFlatAfterBaseChange (D : FlatnessSituation.{u})
    (T : Over D.S) : Prop :=
  IsFlatOver (pullback.snd D.f T.hom).toLRSHom.toShHom (D.baseChangeModule T)

/-- Flatness over the base of the pullback of a quasi-coherent module to a fibre product is
inherited by the fibre product over a scheme mapping to the base. -/
private theorem isFlatOver_schemeBaseChange
    {X S T T' : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (g : T' ⟶ T) (hg : g ≫ t = t')
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (h : IsFlatOver (pullback.snd f t).toLRSHom.toShHom
      ((modulePullback (pullback.fst f t).toLRSHom.toShHom).obj F)) :
    IsFlatOver (pullback.snd f t').toLRSHom.toShHom
      ((modulePullback (pullback.fst f t').toLRSHom.toShHom).obj F) := by
  let p1 := pullback.fst f t
  let p2 := pullback.snd f t
  let p1' := pullback.fst f t'
  let p2' := pullback.snd f t'
  have hright : IsPullback p1 p2 f t := IsPullback.of_hasPullback _ _
  let g' : pullback f t' ⟶ pullback f t := hright.lift p1' (p2' ≫ g) (by
    rw [Category.assoc, hg]
    exact pullback.condition)
  have houter : IsPullback p1' p2' f (g ≫ t) := by
    rw [hg]
    exact IsPullback.of_hasPullback f t'
  have : ((modulePullback p1.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent p1.toLRSHom.toShHom F
  have hcomp : g' ≫ p1 = p1' := hright.lift_fst p1' (p2' ≫ g) _
  have ecomp :
      (modulePullback g'.toLRSHom.toShHom).obj
          ((modulePullback p1.toLRSHom.toShHom).obj F) ≅
        (modulePullback p1'.toLRSHom.toShHom).obj F := by
    simpa only [hcomp, Functor.comp_obj] using (schemeModulePullbackCompIso g' p1).app F
  exact isFlatOver_of_moduleIso p2'.toLRSHom.toShHom ecomp
    (modulePullback_isFlatOver (houter.of_right' hright)
      ((modulePullback p1.toLRSHom.toShHom).obj F) h)

/-- Flatness of the pulled-back module persists under further base change. -/
@[stacks 05MW "base-change stability"]
public theorem isFlatAfterBaseChange_of_hom (D : FlatnessSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) (h : D.IsFlatAfterBaseChange T) :
    D.IsFlatAfterBaseChange T' :=
  isFlatOver_schemeBaseChange D.f T.hom T'.hom g.left g.w D.F h

/-- The subterminal functor recording flatness of the base-changed module. -/
@[stacks 05MW "the functor"]
public noncomputable def flatFunctor (D : FlatnessSituation.{u}) :
    (Over D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsFlatAfterBaseChange T.unop)
  map g := ↾fun h ↦ ⟨D.isFlatAfterBaseChange_of_hom g.unop h.down⟩
  map_id := by
    intro T
    ext h
    exact Subsingleton.elim _ _
  map_comp := by
    intro T T' T'' g h
    ext x
    exact Subsingleton.elim _ _

/-- The functor takes a scheme over `S` to the lifted flatness proposition. -/
@[simp] public theorem flatFunctor_obj (D : FlatnessSituation.{u})
    (T : Over D.S) :
    D.flatFunctor.obj (Opposite.op T) = PLift (D.IsFlatAfterBaseChange T) := rfl

/-- The functorial map is induced by stability of flatness under base change. -/
@[simp] public theorem flatFunctor_map (D : FlatnessSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T)
    (h : PLift (D.IsFlatAfterBaseChange T)) :
    D.flatFunctor.map (Quiver.Hom.op g) h =
      ⟨D.isFlatAfterBaseChange_of_hom g h.down⟩ := rfl

/-- Every value of the flatness functor has at most one element. -/
public instance flatFunctor_obj_subsingleton (D : FlatnessSituation.{u})
    (T : (Over D.S)ᵒᵖ) : Subsingleton (D.flatFunctor.obj T) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => by congr⟩

/-- A value of the flatness functor is nonempty exactly when the pullback is flat. -/
@[simp] public theorem flatFunctor_obj_nonempty_iff (D : FlatnessSituation.{u})
    (T : Over D.S) :
    Nonempty (D.flatFunctor.obj (Opposite.op T)) ↔
      D.IsFlatAfterBaseChange T :=
  ⟨fun ⟨⟨h⟩⟩ => h, fun h => ⟨⟨h⟩⟩⟩

end FlatnessSituation

end AlgebraicGeometry
