module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBaseChangeAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomFunctorAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackTensorExact

/-!
# The functors `- ⊗_A N` and `SheafHom^dg_B(N, -)`, on modules and on differential graded categories

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of differential graded `O`-algebras and
let `N` be a differential graded `(A, B)`-bimodule. Section
[Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) defines a functor and a functor of
differential graded categories

`- ⊗_A N : Mod(A, d) ⥤ Mod(B, d)` and `SheafHom^dg_B(N, -) : Mod(B, d) ⥤ Mod(A, d)`,

sending a homomorphism of degree `n` to the induced map of degree `n`, and specialises them to
`- ⊗_{A, φ} B` and `res_φ` for a homomorphism `φ : A ⟶ B`. This file assembles, from the
constructions of the library, the two functors with their actions on hom complexes, and the
adjunction `- ⊗_A N ⊣ SheafHom^dg_B(N, -)` of [Stacks, Tag 0FRS] with both functors constructed.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.dgTensorRightData`: the tensor product functor with
  `N`, its values exhibited as tensor products.
* `SheafOfModules.DifferentialGradedModule.dgTensorRightConcreteDGFunctor`: `- ⊗_A N` on
  homogeneous maps, `c ↦ c ⊗ 1`, additively and compatibly with the differentials, composition
  and identities.
* `SheafOfModules.DifferentialGradedModule.baseChangeConcreteDGFunctor`: the same for
  `- ⊗_{A, φ} B`.
* `SheafOfModules.DifferentialGradedModule.dgTensorRightSheafHomAdjunction`: the adjunction
  `- ⊗_A N ⊣ SheafHom^dg_B(N, -)`.

## Implementation notes

The functor `SheafHom^dg_B(N, -)` is `SheafOfModules.sheafHomFunctor`, its values the modules
`SheafOfModules.sheafHomModule`, and its action on hom complexes
`SheafOfModules.DifferentialGradedModule.sheafHomConcreteDGFunctor`; restriction on hom
complexes is `SheafOfModules.DifferentialGradedModule.restrictionConcreteDGFunctor`. A
`SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor` induces an additive functor of the
differential graded categories by `ConcreteDGFunctor.dgFunctor`.

The ringed site has a single universe `u`, the universe of the hom complexes of
`DifferentialGradedTensorHomHomComplex.lean`; the instance
`X.J.HasSheafCompose (forget₂ CommRingCat RingCat)` is supplied by
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`, as in
`DifferentialGradedBaseChangeAdjunction.lean`.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- The tensor product functor `- ⊗_A N` with a differential graded `(A, B)`-bimodule `N`,
`SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`, with its values exhibited as
tensor products. -/
abbrev dgTensorRightData (N : DifferentialGradedBimodule.{u, u, u} A B) :
    TensorFunctorData.{u, u, u, u, u} A B N :=
  letI := X.hasSheafCompose_forget₂_ringCat
  RelativeTensor.tensorFunctorDataDgTensorRight
    (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)))
    (B := (B : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) N

/-- **`- ⊗_A N` as a functor of differential graded categories**: the functor
`Mod(A, d) ⥤ Mod(B, d)` of the tensor product with a differential graded `(A, B)`-bimodule `N`,
sending a homogeneous map `c` of degree `n` to the induced map `c ⊗ 1` of degree `n`,
additively and compatibly with the differentials of the hom complexes, composition and
identities. -/
@[stacks 0FRP "- ⊗_A N as a functor of differential graded categories Mod^dg(A, d) ⥤ Mod^dg(B, d)"]
def dgTensorRightConcreteDGFunctor (N : DifferentialGradedBimodule.{u, u, u} A B) :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X) (Y := X) A B :=
  tensorConcreteDGFunctor (dgTensorRightData N)

/-- The underlying functor of `dgTensorRightConcreteDGFunctor N` is `- ⊗_A N`. -/
theorem dgTensorRightConcreteDGFunctor_functor (N : DifferentialGradedBimodule.{u, u, u} A B) :
    (dgTensorRightConcreteDGFunctor N).functor = (dgTensorRightData N).functor :=
  rfl

/-- **`- ⊗_{A, φ} B` as a functor of differential graded categories**, for a homomorphism
`φ : A ⟶ B` of sheaves of differential graded algebras: base change, sending a homogeneous map
`c` of degree `n` to `c ⊗ 1`. -/
@[stacks 0FRP "- ⊗_{A,φ} B as a functor of differential graded categories"]
def baseChangeConcreteDGFunctor (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X) (Y := X) A B :=
  tensorConcreteDGFunctor (baseChangeData φ hφ)

/-- The underlying functor of `baseChangeConcreteDGFunctor φ hφ` is base change. -/
theorem baseChangeConcreteDGFunctor_functor (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    (baseChangeConcreteDGFunctor φ hφ).functor = baseChange φ hφ :=
  rfl

/-- **The tensor-hom adjunction `- ⊗_A N ⊣ SheafHom^dg_B(N, -)`**, with both functors
constructed: for a differential graded `(A, B)`-bimodule `N`, the tensor product functor
`- ⊗_A N : Mod(A, d) ⥤ Mod(B, d)` is left adjoint to the internal hom functor
`SheafHom^dg_B(N, -) : Mod(B, d) ⥤ Mod(A, d)`, that is
`Hom_{Mod(B, d)}(M ⊗_A N, L) = Hom_{Mod(A, d)}(M, SheafHom^dg_B(N, L))` functorially in `M` and
`L`, by `ψ ↦ (x ↦ (y ↦ ψ (x ⊗ y)))`. -/
@[stacks 0FRS "Hom(M ⊗_A N, L) = Hom(M, SheafHom^dg_B(N, L)) as an adjunction of the constructed
functors - ⊗_A N and SheafHom^dg_B(N, -)"]
def dgTensorRightSheafHomAdjunction (N : DifferentialGradedBimodule.{u, u, u} A B) :
    (dgTensorRightData N).functor ⊣ sheafHomFunctor N :=
  tensorSheafHomAdjunction (dgTensorRightData N) (sheafHomFunctorData N)

end SheafOfModules.DifferentialGradedModule
