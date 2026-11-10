module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of modules after base change

Pulling a quasi-coherent module back along a base change preserves flatness over the base,
both at an individual point and globally.

## Main results

* `AlgebraicGeometry.modulePullback_isFlatOverAt` states preservation of flatness at a point
  under base change.
* `AlgebraicGeometry.modulePullback_isFlatOver` states preservation of flatness over the whole
  base.

## Implementation notes

The base-changed scheme is presented by an arbitrary pullback square rather than by Mathlib's
chosen pullback object. The map to the original scheme is the map along which the module is
pulled back, while the map to the new base is the new structural morphism. Flatness is expressed
using the stalkwise predicates `AlgebraicGeometry.IsFlatOverAt` and
`AlgebraicGeometry.IsFlatOver`.

## References

* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Pulling back along a composite of morphisms of schemes agrees with pulling back
successively, for the pullback of sheaves of modules on the underlying ringed spaces. -/
private noncomputable def schemeModulePullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g.toLRSHom.toShHom ⋙ modulePullback f.toLRSHom.toShHom ≅
      modulePullback (f ≫ g).toLRSHom.toShHom :=
  Scheme.Modules.pullbackComp f g

/-- Flatness over the base at a point is preserved by pullback along the first projection of
Mathlib's chosen pullback of schemes. -/
private theorem pullback_module_flatOverAt
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (t : (Limits.pullback f g).carrier)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F
      ((Limits.pullback.fst f g).base t)) :
    AlgebraicGeometry.IsFlatOverAt (Limits.pullback.snd f g).toLRSHom.toShHom
      ((modulePullback (Limits.pullback.fst f g).toLRSHom.toShHom).obj F) t := by
  let pX : Limits.pullback f g ⟶ X := Limits.pullback.fst f g
  let pY : Limits.pullback f g ⟶ S' := Limits.pullback.snd f g
  let x := pX.base t
  let y := pY.base t
  let hxy : (pX ≫ f).base t = (pY ≫ g).base t :=
    congrArg (fun k : Limits.pullback f g ⟶ S => k.base t) Limits.pullback.condition
  let s := (pX ≫ f).base t
  let R := S.presheaf.stalk s
  let A := X.presheaf.stalk x
  let B := S'.presheaf.stalk y
  let C := (Limits.pullback f g).presheaf.stalk t
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R B :=
    ((eqToHom (congrArg S.presheaf.stalk hxy)) ≫ g.stalkMap y).hom.toAlgebra
  obtain ⟨φ, hleft, hright, W, hlocal⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g t
  let T := TensorProduct R A B
  let : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra R T := inferInstance
  let : IsScalarTower R A T := inferInstance
  let : IsScalarTower R B T := inferInstance
  let : Algebra T C := φ.toAlgebra
  let : IsLocalization W C := hlocal
  let : Algebra A C := (pX.stalkMap t).hom.toAlgebra
  let : Algebra B C := (pY.stalkMap t).hom.toAlgebra
  let : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' (by
    change (pX.stalkMap t).hom = φ.comp Algebra.TensorProduct.includeLeftRingHom
    exact hleft.symm)
  let : IsScalarTower B T C := IsScalarTower.of_algebraMap_eq' (by
    change (pY.stalkMap t).hom = φ.comp Algebra.TensorProduct.includeRight.toRingHom
    exact hright.symm)
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (by
    ext z
    change (algebraMap A C) ((algebraMap R A) z) =
      (algebraMap B C) ((algebraMap R B) z)
    change (pX.stalkMap t).hom ((f.stalkMap x).hom z) =
      (pY.stalkMap t).hom (((eqToHom (congrArg S.presheaf.stalk hxy) ≫
        g.stalkMap y).hom) z)
    have heq := Scheme.Hom.stalkMap_congr_hom (pX ≫ f) (pY ≫ g)
      Limits.pullback.condition t
    rw [stalkCongr_of_eq S.presheaf hxy] at heq
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at heq
    exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp heq) z)
  let Mpre : PresheafOfModules
      (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Mpre.presheaf x
  let : Module A M := inferInstance
  let : Module R M := Module.compHom M (f.stalkMap x).hom
  let : IsScalarTower R A M := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    rfl
  have hFM : Module.Flat R M := hF
  let N := TensorProduct A C M
  let : Module C N := inferInstance
  let : Module B N := Module.compHom N (algebraMap B C)
  let : Module R N := Module.compHom N (algebraMap R C)
  let : IsScalarTower A C N := inferInstance
  let : IsScalarTower B C N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R C N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hTower : IsScalarTower B C N := inferInstance
  let baseMap : M →ₗ[A] N := (TensorProduct.mk A C M) 1
  have hbase : IsBaseChange C baseMap := TensorProduct.isBaseChange A M C
  have hmain := @Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization
    R A B T C M N
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance hTower
    W inferInstance baseMap hbase
  have hN : Module.Flat B N := hmain.1 hFM
  let e := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      pX.toLRSHom.toShHom F t)
  let Ppre : PresheafOfModules
      ((pullback f g).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    ((modulePullback pX.toLRSHom.toShHom).obj F).val
  let P := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Ppre.presheaf t
  let : Module C P := inferInstance
  let : Module B P := Module.compHom P (pY.stalkMap t).hom
  let : IsScalarTower B C P := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change Module.Flat B
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Ppre.presheaf t)
  exact (Module.Flat.equiv_iff (e.restrictScalars B)).mpr hN

/-- The pullback of a quasi-coherent module which is flat over the base at the image of a point is
flat over the new base at that point. -/
@[stacks 01U8 "flatness at a point",
  ega "IV 2.1.4" "pointwise statement",
  sga "3 V 7.4" "(i) base change"]
public lemma modulePullback_isFlatOverAt
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (x' : X') (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F (g' x')) :
    AlgebraicGeometry.IsFlatOverAt f'.toLRSHom.toShHom
      ((modulePullback g'.toLRSHom.toShHom).obj F) x' := by
  let e := h.isoPullback
  let t := e.hom x'
  have hfst : e.hom ≫ Limits.pullback.fst f g = g' := by
    simp [e]
  have hsnd : e.hom ≫ Limits.pullback.snd f g = f' := by
    simp [e]
  have hpoint : g' x' = (Limits.pullback.fst f g) t := by
    have hpoint' := congrArg (fun k : X' ⟶ X => k x') hfst
    simpa [t] using hpoint'.symm
  rw [hpoint] at hF
  have hcanonical := pullback_module_flatOverAt f g t F hF
  have hflatAt : AlgebraicGeometry.IsFlatOverAt
      (e.hom ≫ Limits.pullback.snd f g).toLRSHom.toShHom
      ((modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback (Limits.pullback.fst f g).toLRSHom.toShHom).obj F)) x' := by
    have heFlat : AlgebraicGeometry.IsFlatAt e.hom.toLRSHom.toShHom x' :=
      (Flat.iff_flat_stalkMap e.hom).mp inferInstance x'
    apply (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt
      e.hom (Limits.pullback.snd f g)
      ((modulePullback (Limits.pullback.fst f g).toLRSHom.toShHom).obj F)
      x' heFlat).mp
    simpa [t] using hcanonical
  rw [hsnd] at hflatAt
  have ecomp := (schemeModulePullbackComp e.hom (Limits.pullback.fst f g)).app F
  have ecomp' :
      (modulePullback e.hom.toLRSHom.toShHom).obj
          ((modulePullback (Limits.pullback.fst f g).toLRSHom.toShHom).obj F) ≅
        (modulePullback g'.toLRSHom.toShHom).obj F := by
    simpa only [hfst, Functor.comp_obj] using ecomp
  exact isFlatOverAt_of_moduleIso f'.toLRSHom.toShHom ecomp' x' hflatAt

/-- The pullback of a quasi-coherent module flat over the base is flat over the new base. -/
@[stacks 01U8 "global flatness", ega "IV 2.1.4" "global module case"]
public lemma modulePullback_isFlatOver
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) :
    AlgebraicGeometry.IsFlatOver f'.toLRSHom.toShHom
      ((modulePullback g'.toLRSHom.toShHom).obj F) := by
  intro x'
  exact modulePullback_isFlatOverAt h F x' (hF (g' x'))

end AlgebraicGeometry
