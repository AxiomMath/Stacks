module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite

/-!
# K-flat complexes on a ringed space

A ringed space is the ringed site `Opens X` with its Grothendieck topology. This file
specializes K-flatness of complexes of sheaves of modules on a ringed site to a ringed space
`X`: a complex `K` of `O_X`-modules is K-flat when `Tot(G ⊗_{O_X} K)` is acyclic for every
acyclic complex `G`. It proves that every complex has a K-flat resolution, that bounded above
complexes of flat modules are K-flat, and that K-flatness is preserved by mapping cones.

## Main definitions

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat`: K-flatness of a cochain complex of
  `O_X`-modules on a ringed space.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution`: every complex of
  `O_X`-modules is the target of a termwise surjective quasi-isomorphism from a K-flat complex with
  flat terms.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat`: a bounded
  above complex of flat `O_X`-modules is K-flat.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_mappingCone`: the mapping cone of a map
  of K-flat complexes is K-flat.

## Implementation notes

The canonical bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` has independent site, ring
and module universes; here all five are pinned to the universe of the ringed space before
additivity in each variable and existence of the total tensor complex are synthesized.

The predicate is `CochainComplex.KFlatBifunctor.KFlat` at
`Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` rather than `Stacks.SheafOfModules.IsKFlat`,
although the two are the same by definition: the bifunctor form carries the triangulated
two-out-of-three API that the mapping cone needs.

One spelling is used for the category of `O_X`-modules, `StrictlyPerfect.OXMod X`, which is
`SheafOfModules (structureSheafOfRings X)`; `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` is
the same sheaf of rings by `rfl`, but writing both in one statement makes instance search attempt
the same goal twice at two spellings.

## References

* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

variable (X : RingedSpace.{u, u})

/-- `⊗_{O_X}` is additive in its first variable. -/
instance sheafTensor_additive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u}
    (C := Opens X.carrier) X.sheaf

/-- `M ⊗_{O_X} -` is additive. -/
instance sheafTensor_obj_additive
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (C := Opens X.carrier) X.sheaf M

/-- The total complex of the tensor double complex of two complexes of `O_X`-modules exists. -/
instance hasMapBifunctor_sheafTensor
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ℤ) :
    letI : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
      Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} X.sheaf
    letI : ∀ left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf),
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj left).Additive :=
      Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.sheaf
    HomologicalComplex.HasMapBifunctorReg K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u}
    (C := Opens X.carrier) X.sheaf K L

/-- The category of `O_X`-modules, in the spelling the tensor product of sheaves of modules is
stated at. It is `StrictlyPerfect.OXMod X` by `rfl`, but every statement about the tensor product
has to be written at this spelling: the instance arguments of the tensor product fix its ring
sheaf as `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, and a complex whose type is given at
the other spelling leaves them to be synthesized before the two are unified, which fails. -/
abbrev Modules : Type (u + 1) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)

/-- A complex of `O_X`-modules is **K-flat** when `Tot(G ⊗_{O_X} K)` is acyclic for every
acyclic complex `G` of `O_X`-modules. -/
abbrev KFlat (K : CochainComplex (Modules X) ℤ) : Prop :=
  letI : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} X.sheaf
  letI : ∀ left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj left).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.sheaf
  CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) K

/-- The two spellings of the category of `O_X`-modules agree. -/
theorem modules_eq_OXMod : Modules X = OXMod.{u, u} X := rfl

/-- Every complex of `O_X`-modules is the target of a termwise surjective quasi-isomorphism from a
K-flat complex with flat terms. -/
theorem exists_kFlatResolution (G : CochainComplex (Modules X) ℤ) :
    ∃ (K : CochainComplex (Modules X) ℤ) (p : K ⟶ G), KFlat X K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i)) ∧
      QuasiIso p ∧ ∀ i : ℤ, Epi (p.f i) :=
  Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution.{u} (R := X.sheaf) G

/-- A bounded above complex of flat `O_X`-modules is K-flat. -/
theorem kFlat_of_boundedAbove_of_flat (K : CochainComplex (Modules X) ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) (K.X i)) :
    KFlat X K :=
  let : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} X.sheaf
  let : ∀ left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj left).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.sheaf
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat (R := X.sheaf) K hbound hflat

/-- The mapping cone of a morphism of K-flat complexes is K-flat. -/
theorem kFlat_mappingCone {K L : CochainComplex (Modules X) ℤ} (α : K ⟶ L)
    (hK : KFlat X K) (hL : KFlat X L) : KFlat X (CochainComplex.mappingCone α) :=
  CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang _ _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished α) hK hL

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
