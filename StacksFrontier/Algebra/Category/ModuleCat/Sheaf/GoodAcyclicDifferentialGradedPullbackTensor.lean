module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedModule

/-!
# Acyclicity of `f^*𝒬 ⊗_𝒜 𝒩` for a good acyclic `𝒬`

Clause (1) of Tag 0FSI says that the relative tensor product `P ⊗_A N` of an acyclic K-flat right
differential graded `A`-module with a left one is acyclic
(`SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isKFlat_of_acyclic`). This file
extends it to tensor products with a differential graded bimodule, and to the functor
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE, whose first factor is a pullback along a morphism of ringed sites.

## Main results

* `SheafOfModules.DifferentialGradedModule.acyclic_of_isTensorProduct_of_isKFlat_of_acyclic`:
  an acyclic K-flat right differential graded `A`-module has acyclic tensor product with every
  differential graded `(A, B)`-bimodule, at every object exhibited as that tensor product.
* `SheafOfModules.DifferentialGradedModule.acyclic_pullbackTensor_of_isKFlat_of_acyclic`:
  `f^*𝒬 ⊗_𝒜 𝒩` is acyclic as soon as `f^*𝒬` is K-flat and acyclic.
* `SheafOfModules.DifferentialGradedModule.acyclic_pullbackTensor_of_isGood_of_acyclic`:
  `f^*𝒬 ⊗_𝒜 𝒩` is acyclic for a good acyclic `𝒬`.
* `SheafOfModules.DifferentialGradedModule.acyclic_pullbackTensor_of_isGoodToposBaseChange`:
  the same over a morphism of ringed topoi, with goodness in the sense of Tag 0FSA, as soon as
  `f^*𝒬` is acyclic.

## Implementation notes

`RelativeTensor.dgTensorRight` lives on the diagonal universe `max u v` of the site hosting the
tensor product, so the tensor product with a bimodule is stated with the algebra universe and
the three module universes of the target site all equal to `max u v`.

The module `𝒬` lives over `A` on `C` and the pullback `f^*𝒬` over `A₁` on `C₁`, with
`φ₁ : A ⟶ f_*A₁` the semilinear homomorphism; the bimodule `N` and the second algebra `A₁'` of
the tensor product live on `C₁`.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u v₁ u₁ v₂ u₂ w

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### Clause (1) of Tag 0FSI at a tensor product with a bimodule -/

section Bimodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type (max u v))]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] [HasSheafify J AddCommGrpCat.{max u v}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, max u v} (toRingCat J Osharp)}

/-- **Clause (1) of Tag 0FSI at a tensor product with a differential graded bimodule.** An
acyclic K-flat right differential graded `A`-module `M` has acyclic tensor product with every
differential graded `(A, B)`-bimodule `N`: every right differential graded `B`-module exhibited
as `M ⊗_A N` by `SheafOfModules.IsTensorProduct` has acyclic complex. -/
theorem acyclic_of_isTensorProduct_of_isKFlat_of_acyclic
    {M : DifferentialGradedModule.{t, max u v, max u v} A}
    (hM : RelativeTensor.IsKFlat M) (hMac : M.complex.Acyclic)
    {N : DifferentialGradedBimodule.{t, max u v, max u v} A B}
    {T : DifferentialGradedModule.{t, max u v, max u v} B}
    (hT : IsTensorProduct M N T) : T.complex.Acyclic := by
  have h := acyclic_dgTensor_of_isKFlat_of_acyclic hM hMac
    N.toLeftDifferentialGradedModule
  have iso : RelativeTensor.dgTensorRight M N ≅ T :=
    (RelativeTensor.isTensorProductDgTensorRight M N).uniqueIso hT
  have e : (RelativeTensor.dgTensorRight M N).complex ≅ T.complex :=
    ⟨iso.hom.toHomologicalComplex, iso.inv.toHomologicalComplex,
      HomologicalComplex.hom_ext _ _ fun n => congrArg (·.toHomologicalComplex.f n) iso.hom_inv_id,
      HomologicalComplex.hom_ext _ _ fun n => congrArg (·.toHomologicalComplex.f n) iso.inv_hom_id⟩
  exact fun i => (h i).of_iso e

end Bimodule

/-! ### Tag 0FSI over the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE -/

section PullbackTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J₁ (Type (max u₁ v₁))]
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify J₁ AddCommGrpCat.{max u₁ v₁}]
  {Osharp₁ : Sheaf J₁ CommRingCat.{t}} {w₁ : C ⥤ C₁}
  {ρ₁ : (toRingCat J Osharp).obj ⟶ w₁.op ⋙ (toRingCat J₁ Osharp₁).obj}
  {A₁ A₁' : DifferentialGradedAlgebra.{t, max u₁ v₁} (toRingCat J₁ Osharp₁)}
  {φ₁ : DifferentialGradedAlgebra.SemilinearHom w₁ ρ₁ A A₁}
  {N : DifferentialGradedBimodule.{t, max u₁ v₁, max u₁ v₁} A₁ A₁'}

omit [HasWeakSheafify J (Type m)] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J AddCommGrpCat.{m}] in
/-- **Tag 0FSI over the functor of Tag 0FTE.** The value `f^*𝒬 ⊗_{𝒜} 𝒩` of the functor
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` at a right differential graded module `𝒬` is acyclic as soon as the pullback
`f^*𝒬` is K-flat and acyclic. -/
theorem acyclic_pullbackTensor_of_isKFlat_of_acyclic
    (PD : PullbackData.{t, max u₁ v₁, max u₁ v₁, v₁, u₁, m, m, v, u} φ₁)
    (D : TensorFunctorData.{t, max u₁ v₁, max u₁ v₁, max u₁ v₁, max u₁ v₁} A₁ A₁' N)
    {Q : DifferentialGradedModule.{t, m, m} A}
    (hflat : RelativeTensor.IsKFlat (PD.obj Q)) (hac : (PD.obj Q).complex.Acyclic) :
    ((pullbackTensorFunctor PD D).obj Q).complex.Acyclic :=
  acyclic_of_isTensorProduct_of_isKFlat_of_acyclic hflat hac
    (isTensorProduct_pullbackTensorFunctor_obj PD D Q)

/-- **Tag 0FSI at the pullback-tensor.** For a good acyclic right differential graded `A`-module
`𝒬`, the value `f^*𝒬 ⊗_{𝒜} 𝒩` of the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE is acyclic. -/
theorem acyclic_pullbackTensor_of_isGood_of_acyclic
    {PD : PullbackData.{t, max u₁ v₁, max u₁ v₁, v₁, u₁, m, m, v, u} φ₁}
    (D : TensorFunctorData.{t, max u₁ v₁, max u₁ v₁, max u₁ v₁, max u₁ v₁} A₁ A₁' N)
    {Q : DifferentialGradedModule.{t, m, m} A}
    (hQ : IsGood.{t, m, v, u, max u₁ v₁, v₁, u₁} Q)
    (data : PullbackAcyclicityData PD Q) :
    ((pullbackTensorFunctor PD D).obj Q).complex.Acyclic :=
  acyclic_pullbackTensor_of_isKFlat_of_acyclic PD D
    (hQ.baseChange w₁ ρ₁ A₁ φ₁ PD).2 (acyclic_pullback_of_isGood_of_acyclic data)

end PullbackTensor

/-! ### The same over a morphism of ringed topoi, with goodness at Tag 0FSA -/

section ToposPullbackTensor

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, max u₁ v₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Y.J AddCommGrpCat.{max u₁ v₁}] [HasSheafify Y.J (Type (max u₁ v₁))]
  {B : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Y.J Y.O)}
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, max u₁ v₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify X.J AddCommGrpCat.{max u₁ v₁}] [HasSheafify X.J (Type (max u₁ v₁))]
  [HasWeakSheafify X.J (Type (max u₁ v₁))]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **Tag 0FSI at the pullback-tensor over a morphism of ringed topoi**, with goodness read at
the definition of Tag 0FSA. Let `𝒬` be a good right differential graded `ℬ`-module on `Y`, let
`f : X ⟶ Y` be a morphism of ringed topoi, let `𝒜` be a sheaf of differential graded algebras on
`X` and `ψ : ℬ ⟶ f_*𝒜` a unital homomorphism, and let `T` be an object corepresenting
`T' ↦ Hom_ℬ(𝒬, f_{*,ψ}T')`, that is, a pullback `f^*𝒬`. Then `f^*𝒬 ⊗_𝒜 𝒩` is acyclic for every
differential graded `(𝒜, 𝒜')`-bimodule `𝒩`, as soon as `f^*𝒬` is acyclic. -/
theorem acyclic_pullbackTensor_of_isGoodToposBaseChange
    {Q : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B}
    (hQ : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} Q)
    (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat X.J X.O))
    (ψ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hψ : ψ.IsUnital)
    {T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A}
    (e : (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
      coyoneda.obj (Opposite.op Q)).CorepresentableBy T)
    (hTac : T.complex.Acyclic)
    {A' : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat X.J X.O)}
    {N : DifferentialGradedBimodule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A A'}
    {TN : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A'}
    (hTN : IsTensorProduct T N TN) : TN.complex.Acyclic :=
  acyclic_of_isTensorProduct_of_isKFlat_of_acyclic
    ((hQ.baseChange f A ψ hψ).2 T e).2 hTac hTN

end ToposPullbackTensor

end DifferentialGradedModule

end SheafOfModules

end
