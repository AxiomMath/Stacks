module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness and pullback along a flat morphism

Let `X ⟶ Y ⟶ S` be morphisms of schemes and let `G` be a module on `Y`.
At a point where `X ⟶ Y` is flat, flatness of `G` over `S`
is equivalent to flatness of its pullback. For a surjective flat morphism this
equivalence holds globally.

## Main results

* `AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt` gives the pointwise
  equivalence.
* `AlgebraicGeometry.isFlatOver_iff_modulePullback_isFlatOver` gives the global
  equivalence along a surjective flat morphism.

## Implementation notes

The morphism from `X` to `S` is represented by the composite of the displayed
morphisms. Pullback is the canonical left adjoint
`RingedSpaceModuleAdjunction.modulePullback`. The pointwise argument works for
all modules, so quasi-coherence is not needed for either equivalence.

## References

* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

open RingedSpaceModuleAdjunction

universe u

/-- **Stacks Project, Tag 02JZ (pointwise assertion).** If `f : X ⟶ Y` is
flat at `x`, then a module `G` on `Y` is flat over `S` at
`f(x)` if and only if its pullback to `X` is flat over `S` at `x`. -/
@[stacks 02JZ "pointwise equivalence"]
public theorem isFlatOverAt_iff_modulePullback_isFlatOverAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (x : X) (hf : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x) :
      AlgebraicGeometry.IsFlatOverAt q.toLRSHom.toShHom G (f.base x) ↔
      AlgebraicGeometry.IsFlatOverAt (f ≫ q).toLRSHom.toShHom
        ((modulePullback f.toLRSHom.toShHom).obj G) x := by
  let A := S.presheaf.stalk (q.base (f.base x))
  let B := Y.presheaf.stalk (f.base x)
  let C := X.presheaf.stalk x
  let GM : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G.val
  let PM : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    ((modulePullback f.toLRSHom.toShHom).obj G).val
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) GM.presheaf (f.base x)
  let P := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) PM.presheaf x
  let h : A →+* B := (q.stalkMap (f.base x)).hom
  let g : B →+* C := (f.stalkMap x).hom
  have hcomp : ((f ≫ q).stalkMap x).hom = g.comp h := by
    simpa [h, g, RingHom.comp_apply] using
      congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f q x)
  let : Algebra A B := h.toAlgebra
  let : Algebra B C := g.toAlgebra
  let k : A →+* C := ((f ≫ q).stalkMap x).hom
  let : Algebra A C := k.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra, k, hcomp]
  let : Module A M := Module.compHom _ h
  let : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  let : Module A P := Module.compHom _ k
  let : IsScalarTower A C P := IsScalarTower.of_compHom A C P
  have : Module.Flat B C := hf
  have : IsLocalHom (algebraMap B C) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨e, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom G x
  change Module.Flat A M ↔ Module.Flat A P
  exact (Module.Flat.tensorProduct_iff_of_faithfullyFlat (R := A) (S := B)
    (S' := C) (M := M)).symm.trans (Module.Flat.equiv_iff (e.restrictScalars A)).symm

/-- **Stacks Project, Tag 02JZ (first global consequence).** Pullback along a
surjective flat morphism detects whether a module is flat over
the base. -/
@[stacks 02JZ "global equivalence"]
public theorem isFlatOver_iff_modulePullback_isFlatOver
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [Surjective f] [Flat f] :
    AlgebraicGeometry.IsFlatOver q.toLRSHom.toShHom G ↔
      AlgebraicGeometry.IsFlatOver (f ≫ q).toLRSHom.toShHom
        ((modulePullback f.toLRSHom.toShHom).obj G) := by
  refine ⟨fun h x => (isFlatOverAt_iff_modulePullback_isFlatOverAt f q G x
    (Flat.stalkMap f x)).mp (h (f.base x)), fun h y => ?_⟩
  obtain ⟨x, rfl⟩ := f.surjective y
  exact (isFlatOverAt_iff_modulePullback_isFlatOverAt f q G x (Flat.stalkMap f x)).mpr (h x)

end AlgebraicGeometry
