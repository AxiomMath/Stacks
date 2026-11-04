module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# The stalk of a tensor product of sheaves of modules, in the K-flatness spelling

On a ringed space `(X, 𝒪_X)`, the sheafified tensor product
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, whose stalks are
`F_x ⊗_{𝒪_{X,x}} G_x`, is definitionally the value of the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`. The `RingCat`-valued stalk of a sheaf of commutative
rings is a commutative ring.

## Main results

* `StacksDraft.StalkTensor.tensorSheaf_eq_sheafTensor`: the two tensor products of sheaves of
  modules agree definitionally.
* `StacksDraft.StalkTensor.commRing_stalk`,
  `StacksDraft.StalkTensor.commRing_stalk_ringSheaf`: the `RingCat`-valued stalk of a sheaf of
  commutative rings is a commutative ring.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace StacksDraft.StalkTensor

/-- The tensor product `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` of two
sheaves of modules on a ringed space is the value of the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
theorem tensorSheaf_eq_sheafTensor (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj F).obj G :=
  rfl

/-- The `RingCat`-valued stalk of a presheaf of commutative rings is a commutative ring. -/
instance commRing_stalk {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)) :=
  { (inferInstance : Ring (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x))) with
    mul_comm := fun a b => (SemilinearStalk.commStalkRingEquiv R x).injective
      (by rw [map_mul, map_mul, mul_comm]) }

/-- The `RingCat`-valued stalk of the underlying sheaf of rings
`(Stacks.SheafOfModules.Tensor.ringSheaf R).obj` of a sheaf of commutative rings `R` is a
commutative ring. -/
instance commRing_stalk_ringSheaf {X : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X) :
    CommRing ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj x : RingCat.{u}) : Type u) :=
  commRing_stalk R.obj x

end StacksDraft.StalkTensor

end

end
