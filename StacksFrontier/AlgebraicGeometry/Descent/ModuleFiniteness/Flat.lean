module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatPoint
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Flatness descends along fpqc coverings

A quasi-coherent module on a scheme is flat as soon as its pullback to every member of an
fpqc covering family is flat.

## Main results

* `AlgebraicGeometry.isFlat_of_pullback_fpqc`: flatness of a quasi-coherent module descends
  along an fpqc covering family.

## Implementation notes

The covering family is expressed as membership of its presieve in Mathlib's fpqc
precoverage. Pullback is the canonical pullback functor
`RingedSpaceModuleAdjunction.modulePullback` on sheaves of modules over ringed spaces, and
flatness is the exactness predicate `AlgebraicGeometry.SheafOfModules.IsFlat`.

## References

* [Stacks Project, Tag 05B1](https://stacks.math.columbia.edu/tag/05B1)
-/

@[expose] public section

noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

universe u v

namespace AlgebraicGeometry

/-- A flat morphism of schemes induces a faithfully flat map on stalks: its stalk map is a
flat local homomorphism of local rings. -/
private lemma faithfullyFlat_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A quasi-coherent module whose pullback to each member of an fpqc covering family is flat is
itself flat. -/
@[stacks 05B1]
public lemma isFlat_of_pullback_fpqc {S : Scheme.{u}} {I : Type v}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) [F.IsQuasicoherent]
    (hF : ∀ i, SheafOfModules.IsFlat.{u, u, u, u} (O := (X i).toRingedSpace.sheaf)
      ((modulePullback (f i).toLRSHom.toShHom).obj F)) :
      SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) F := by
  apply (SheafOfModules.isFlat_iff_stalk_flat (X := S.toRingedSpace.carrier)
    (O := S.toRingedSpace.sheaf) F).2
  intro x
  let A := TopCat.Presheaf.stalk (C := CommRingCat.{u}) S.toRingedSpace.sheaf.obj x
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x
  let : Module A M := inferInstanceAs (Module A
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := S.toRingedSpace.carrier)
      ((id F.val : PresheafOfModules.{u}
        (S.toRingedSpace.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) x))
  have hflatcov' :=
    (Scheme.ofArrows_mem_precoverage_iff (P := (@Flat : MorphismProperty Scheme.{u}))).mp
      (show Presieve.ofArrows X f ∈
          Scheme.precoverage (@Flat : MorphismProperty Scheme.{u}) S from by
        change Presieve.ofArrows X f ∈
          Scheme.propQCPrecoverage (@Flat : MorphismProperty Scheme.{u}) S at hfpqc
        exact hfpqc.2)
  obtain ⟨i, y, hy⟩ := hflatcov'.1 x
  have hy' : (f i) y = x := by simpa only [Scheme.forget_map'] using hy
  subst x
  let α := (f i).stalkMap y
  let : Algebra A (TopCat.Presheaf.stalk (C := CommRingCat.{u})
    (X i).toRingedSpace.sheaf.obj y) := α.hom.toAlgebra
  let B := TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X i).toRingedSpace.sheaf.obj y
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    ((modulePullback (f i).toLRSHom.toShHom).obj F).val.presheaf y
  let F' := (modulePullback (f i).toLRSHom.toShHom).obj F
  let : Module B N := inferInstanceAs (Module B
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := (X i).toRingedSpace.carrier)
      ((id F'.val : PresheafOfModules.{u}
        ((X i).toRingedSpace.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) y))
  have : Flat (f i) := hflatcov'.2 i
  have : Module.FaithfullyFlat A B := faithfullyFlat_stalkMap (f i) y
  have : Module.Flat B N :=
    (SheafOfModules.isFlat_iff_stalk_flat (X := (X i).toRingedSpace.carrier)
      (O := (X i).toRingedSpace.sheaf) F').mp (hF i) y
  obtain ⟨e₀, _⟩ := exists_modulePullbackStalkLinearEquiv (f i).toLRSHom.toShHom F y
  -- Typed over `B` so that the structure sheaf is not unfolded below.
  let e : N ≃ₗ[B] TensorProduct A B M := e₀
  have : Module.Flat B (TensorProduct A B M) := Module.Flat.of_linearEquiv e.symm
  exact Module.Flat.of_flat_tensorProduct (R := A) (M := M) (S := B)

end AlgebraicGeometry
