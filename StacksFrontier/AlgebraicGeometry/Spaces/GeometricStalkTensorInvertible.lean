module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf

/-!
# Tensoring by an invertible module does not change geometric stalks

Let `X` be an algebraic space, `ℒ` an invertible `𝒪_X`-module and `M` an arbitrary
`𝒪_X`-module.  At every geometric point `x̄` of `X` the stalk of `M ⊗ ℒ` is isomorphic to the
stalk of `M`, as a module over the étale local ring `𝒪_{X, x̄}`:

`(M ⊗ ℒ)_{x̄} ≅ M_{x̄} ⊗_{𝒪_{X, x̄}} ℒ_{x̄} ≅ M_{x̄} ⊗_{𝒪_{X, x̄}} 𝒪_{X, x̄} ≅ M_{x̄}`,

the first by the compatibility of stalks with tensor products and the second because the stalk
of an invertible module at a point of the small étale site is free of rank one.

Consequently the support of `M ⊗ ℒ` is the support of `M` (Stacks 04KA), and for a morphism
`f : X ⟶ Y` and a quasi-coherent `M`, the module `M ⊗ ℒ` is flat over `Y` exactly when `M` is
(Stacks 05VV, read through condition (2) of Stacks 05VU).

## Main definitions

* `AlgebraicGeometry.Space.moduleStalkTensorInvertibleIso`: `(M ⊗ ℒ)_{x̄} ≅ M_{x̄}` on the stalks
  at the point of the small étale site attached to `x̄`.
* `AlgebraicGeometry.Space.geometricModuleStalkTensorInvertibleIso`: the same for the geometric
  stalks of Stacks 05VQ.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_tensor_invertible`: `Supp(M ⊗ ℒ) = Supp(M)`.
* `AlgebraicGeometry.Space.isFlatOver_tensor_invertible_iff`: `M ⊗ ℒ` is flat over `Y` exactly
  when `M` is.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Tensoring by an invertible module does not change stalks.**  For an invertible
`𝒪_X`-module `ℒ`, an `𝒪_X`-module `M` and a geometric point `x̄`, the stalk of `M ⊗ ℒ` at the
point of the small étale site attached to `x̄` is the stalk of `M`. -/
def moduleStalkTensorInvertibleIso (x : GeometricPoint B S hS X.1)
    (M L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj L) ≅
      Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O M :=
  geometricModuleStalkTensorIso B S hS X.1 X.2 (smallEtaleRingedTopos B S hS X).O x M L ≪≫
    (((Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O L).symm.trans
      (nonempty_linearEquiv_moduleStalkLarge_of_isInvertibleModule B S hS X x L hL).some
      |>.lTensor _).trans (TensorProduct.rid _ _)).toModuleIso

/-- **Tensoring by an invertible module does not change geometric stalks** (Stacks 05VQ): for an
invertible `𝒪_X`-module `ℒ` and any `𝒪_X`-module `M`, `(M ⊗ ℒ)_{x̄} ≅ M_{x̄}` over the étale
local ring `𝒪_{X, x̄}`. -/
def geometricModuleStalkTensorInvertibleIso (x : GeometricPoint B S hS X.1)
    (M L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    geometricModuleStalk B S hS X x
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj L) ≅
      geometricModuleStalk B S hS X x M :=
  (ModuleCat.extendScalars (pointStalkRingEquiv B S hS X x).toRingHom).mapIso
    (Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O _ ≪≫
      moduleStalkTensorInvertibleIso B S hS X x M L hL ≪≫
      (Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O M).symm)

/-- **Stacks 04KA.**  Tensoring by an invertible module does not change the support. -/
theorem supportOfSheaf_tensor_invertible (M L : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj L)) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj M) :=
  Set.ext fun x ↦
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj L) x).trans
      ((exists_congr fun xbar ↦ and_congr_right fun _ ↦
        (geometricModuleStalkTensorInvertibleIso B S hS X xbar M L
          hL).toLinearEquiv.nontrivial_congr).trans
        (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X M x).symm)

/-- Flatness of the geometric stalk over the étale local ring of the target (condition (2) of
Stacks 05VU) depends on the geometric stalk only up to isomorphism over the étale local ring of
the source. -/
theorem isFlatOverAtGeometricPoint_iff_of_iso {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {F G : Modules.{u, u} B S hS X.1 X.2} {xbar : GeometricPoint B S hS X.1}
    (e : geometricModuleStalk B S hS X xbar F ≅ geometricModuleStalk B S hS X xbar G) :
    IsFlatOverAtGeometricPoint B S hS f F xbar ↔ IsFlatOverAtGeometricPoint B S hS f G xbar := by
  unfold IsFlatOverAtGeometricPoint
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar G) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  let e' : geometricModuleStalk B S hS X xbar F ≃ₗ[etaleLocalRing B S hS Y.1
      (geometricPointMap f.hom xbar)] geometricModuleStalk B S hS X xbar G :=
    { e.toLinearEquiv.toAddEquiv with
      map_smul' := fun r m ↦ e.toLinearEquiv.map_smul (etaleLocalRingMap X.2 f.hom xbar r) m }
  exact Module.Flat.equiv_iff e'

/-- **Stacks 05VV.**  For a morphism `f : X ⟶ Y` of algebraic spaces, an invertible
`𝒪_X`-module `ℒ` and a quasi-coherent `𝒪_X`-module `M`, the module `M ⊗ ℒ` is flat over `Y`
exactly when `M` is. -/
theorem isFlatOver_tensor_invertible_iff {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L)
    (hM : M.IsQuasicoherentOnSite)
    (hML : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj L).IsQuasicoherentOnSite) :
    IsFlatOver B S hS X.2 f.hom
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj L) ↔
      IsFlatOver B S hS X.2 f.hom M := by
  rw [← flatLocus_eq_univ_iff_isFlatOver f _ hML, ← flatLocus_eq_univ_iff_isFlatOver f _ hM,
    flatLocus_eq_setOf_forall_isFlatOverAtGeometricPoint,
    flatLocus_eq_setOf_forall_isFlatOverAtGeometricPoint]
  refine iff_of_eq (congrArg (· = Set.univ) (Set.ext fun x ↦ ?_))
  exact forall_congr' fun xbar ↦ imp_congr_right fun _ ↦
    isFlatOverAtGeometricPoint_iff_of_iso B S hS X f
      (geometricModuleStalkTensorInvertibleIso B S hS X xbar M L hL)

end AlgebraicGeometry.Space

end
