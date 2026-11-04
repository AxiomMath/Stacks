module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance

/-!
# A tensor product of finite locally free modules on an algebraic space is finite locally free

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The tensor
product of two finite locally free `𝒪_F`-modules on the small étale site of `F` is finite
locally free.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorModule`: the tensor product
  `AlgebraicGeometry.Space.tensorModule` of two finite locally free `𝒪_F`-modules is finite
  locally free.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorObj`: the same for the tensor
  product of `AlgebraicGeometry.Space.modulesMonoidalCategory`.

## Implementation notes

Nothing is proved here: both statements are
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite`, Stacks
03L6 (2) on an arbitrary ringed site, read on the small étale ringed site of `F` and
transported along an isomorphism.

The two transports are the two spellings of the tensor product of `𝒪_F`-modules.
`AlgebraicGeometry.Space.tensorModule` raises the universe of the sections of the objectwise
tensor product before sheafifying, so that the two factors may have their sections in
independent universes; at the single module universe `u` nothing is raised and
`PresheafOfModules.uliftSectionsSelfIso` undoes the lift, which is the comparison already used
for coherence in `AlgebraicGeometry.Space.isCoherentOnSite_tensorModule`.  The tensor product
of `AlgebraicGeometry.Space.modulesMonoidalCategory` is compared with the same sheafification
by `AlgebraicGeometry.Space.modulesTensorObjIso`.

The module universe is the universe `u` of the schemes.  That is where Mathlib's monoidal
structure on presheaves of modules lives — the monoidal unit is the structure sheaf itself —
and hence where `Stacks.SheafOfModules.Tensor.sheafTensor` is defined.  Unlike the
quasi-coherence clause of Stacks 03M1, the finite local freeness clause of Stacks 03L6 leaves
the object and morphism universes of the site free, so the small étale ringed site
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` of an algebraic space is covered by it directly
and no universe lift of the site is needed.

Stacks 0FDK uses this for a scheme: it is what makes `[ℰ] · [ℱ] = [ℰ ⊗ ℱ]` a product on
`K₀(Vect(X))`.  The scheme case is `AlgebraicGeometry.isFiniteLocallyFree_tensorObj`, proved
stalkwise; the small étale site of an algebraic space has no stalks, so the route here is the
site-level Stacks 03L6 (2) instead.  No declaration below carries the `0FDK` tag: none of them
is a statement about a K-group.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 03DL (2) for a tensor product, on an algebraic space.**  The tensor product
`AlgebraicGeometry.Space.tensorModule` of two finite locally free `𝒪_F`-modules is finite
locally free.

This is Stacks 03L6 (2) on the small étale ringed site of `F`, transported along the
isomorphism that undoes the universe lift of the sections. -/
theorem isFiniteLocallyFreeOnSite_tensorModule (M N : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (hN : SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (tensorModule B S hS F hF M N) := by
  let _ := (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat
  let _ := SheafOfModules.isLocallyInjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
  let _ := SheafOfModules.isLocallySurjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
  refine Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso
    (((PresheafOfModules.sheafification
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj)).mapIso
          (PresheafOfModules.uliftSectionsSelfIso _)).symm) ?_
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS F hF) M N hM hN

/-- **Stacks 03DL (2) for a tensor product, on an algebraic space.**  The tensor product of two
finite locally free `𝒪_F`-modules, formed by
`AlgebraicGeometry.Space.modulesMonoidalCategory`, is finite locally free.

This is Stacks 03L6 (2) on the small étale ringed site of `F`, transported along
`AlgebraicGeometry.Space.modulesTensorObjIso`. -/
theorem isFiniteLocallyFreeOnSite_tensorObj (M N : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (hN : SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (M ⊗ N) := by
  let _ := (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat
  refine Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso
    (modulesTensorObjIso B S hS F hF M N).symm ?_
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS F hF) M N hM hN

end AlgebraicGeometry.Space

end
