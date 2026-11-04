module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.RingedSpace.OfSheaf

/-!
# Flatness of a module on a ringed space is detected on stalks

A sheaf of modules over the structure sheaf of a ringed space is flat exactly when its module
stalk at every point is flat over the stalk of the structure sheaf.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`: flatness of a sheaf of modules on
  a ringed space is equivalent to flatness of all of its stalks.

## References

* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public section
noncomputable section

open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafOfModules

open Stacks.SheafOfModules.TensorStalkRingedSpace

noncomputable local instance (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

noncomputable local instance (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _


/-- A sheaf of modules `F` over a sheaf of commutative rings is flat exactly when tensoring with
`F` preserves monomorphisms. -/
public theorem sheafTensorRight_exact_iff_preservesMonomorphisms
    {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) :
    IsFlat F ↔
      ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F).PreservesMonomorphisms := by
  show exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F) ↔ _
  rw [exactFunctor_iff]
  constructor
  · rintro ⟨_, _⟩
    infer_instance
  · intro
    let T := (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F
    let : T.PreservesZeroMorphisms :=
      Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesZeroMorphisms _ O F
    let : PreservesFiniteColimits T :=
      Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits _ O F
    let : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
    let : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
    exact ⟨Functor.preservesFiniteLimits_of_preservesHomology T, inferInstance⟩

/-- A module sheaf on a ringed space is flat precisely when each of its
stalks is flat over the corresponding stalk of the structure sheaf. -/
@[stacks 05NE]
public theorem isFlat_iff_stalk_flat {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) :
    IsFlat F ↔
      ∀ x : X,
        letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) O.obj x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) F.val.presheaf x) :=
          inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) O.obj x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
              ((id F.val : _root_.PresheafOfModules.{u}
                (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) x))
        Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) O.obj x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) F.val.presheaf x) := by
  show IsFlat F ↔ OXModule.FlatStalkwise (X := ringedSpaceOfSheaf O) F
  exact (sheafTensorRight_exact_iff_preservesMonomorphisms O F).trans
    (OXModule.flat_iff_flat_stalk (X := ringedSpaceOfSheaf O) F)

end AlgebraicGeometry.SheafOfModules
