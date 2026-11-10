module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorUnit

/-!
# The derived tensor product and the derived pullback

The two functors of Tag 0FTG are the two instances of the derived pullback-tensor functor of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctor`
in which one of the two halves of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` is trivial.

* The *derived tensor product* `- ⊗^L_𝒜 𝒩` is the case of the identity morphism of ringed
  sites: the pullback along it of a right differential graded `𝒜`-module is the module itself,
  which is `SheafOfModules.DifferentialGradedModule.idPullbackData`, so the functor of Tag 0FTE
  is the tensor product with the bimodule. Its value on a good module `𝒫` is `𝒫 ⊗_𝒜 𝒩`.
* The *derived pullback* `Lf^*` is the case of the diagonal bimodule `{}_𝒜 𝒜_𝒜`: the tensor
  product `ℳ ⊗_𝒜 {}_𝒜 𝒜_𝒜` is `ℳ` itself, which is
  `SheafOfModules.DifferentialGradedModule.tensorFunctorDataDiagonal`, so the functor of
  Tag 0FTE is the pullback. Its value on a good module `𝒫` is `f^*𝒫`.

Neither is a new construction: each is the general functor with one input taken to be the
canonical trivial one, so every result about the general functor — the counit, the value on a
good module and its naturality, the uniqueness up to a unique compatible isomorphism, and the
composition of Tag 0FTI — applies verbatim.

The identity pullback needs its differential graded extension before it can be used, that is
the pullback of a homotopy. Along the identity the pullback of a homomorphism is the
homomorphism itself, `idPullbackData_map`, so the pullback of a homotopy is the homotopy itself:
`idPullbackDataHomotopyExtension`. The derived tensor product therefore carries no pullback data
at all.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.idPullbackDataHomotopyExtension` is the differential
  graded extension of the pullback along the identity morphism of ringed sites.
* `SheafOfModules.DifferentialGradedModule.derivedTensor` is the derived tensor product
  `- ⊗^L_𝒜 𝒩 : D(𝒜, d) ⥤ D(𝒜', d)` with a differential graded `(𝒜, 𝒜')`-bimodule `𝒩`.
* `SheafOfModules.DifferentialGradedModule.derivedTensorObjIso` identifies its value at a good
  right differential graded `𝒜`-module `𝒫` with `𝒫 ⊗_𝒜 𝒩`.
* `SheafOfModules.DifferentialGradedModule.derivedPullback` is the derived pullback
  `Lf^* : D(ℬ, d) ⥤ D(𝒜, d)` along a morphism of ringed sites and a homomorphism of sheaves of
  differential graded algebras.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackObjIso` identifies its value at a good
  right differential graded `ℬ`-module `𝒫` with `f^*𝒫`.

## Main results

* `SheafOfModules.DifferentialGradedModule.idPullbackData_map`: along the identity morphism of
  ringed sites the pullback of a homomorphism of right differential graded modules is the
  homomorphism itself.

## Implementation notes

The two definitions are reducible to the general one on purpose, with no new clause and no new
carried datum, so that a user may rewrite them away and apply any result of the general file.
The two identifications of the value on a good module are literally the general one: for the
identity pullback `f^*𝒫 ⊗_𝒜 𝒩` is `𝒫 ⊗_𝒜 𝒩` and for the diagonal bimodule it is `f^*𝒫`, in
both cases by `rfl`, because `idPullbackData` takes a module to itself and
`tensorFunctorDataDiagonal` is the identity functor.

These two functors are stated for an arbitrary resolving class and an arbitrary exactness
package, at arbitrary universes. Tag 0FTG itself is registered on the constructed functors:
`SheafOfModules.DifferentialGradedModule.derivedTensorProductTopos` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDerivedTensorProduct.lean`
for part (1), the functor of Tag 0FTF at the identity morphism of a ringed topos, isomorphic to
`SheafOfModules.DifferentialGradedModule.derivedTensorProduct` (which is `derivedTensor` at the
flat K-flat resolutions and the constructed exactness of the tensor product), and
`SheafOfModules.DifferentialGradedModule.derivedPullbackRingedTopos` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDerivedPullback.lean` for
part (2), along a morphism of ringed topoi.

## References

* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' s z v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### The identity pullback is a differential graded pullback -/

section Identity

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- Along the identity morphism of ringed sites the pullback of a homomorphism of right
differential graded `𝒜`-modules is the homomorphism itself: it is the unique morphism of the
pullbacks compatible with the two identity units, and the homomorphism is one. -/
theorem idPullbackData_map {M M₂ : DifferentialGradedModule.{t, a, m} A} (ψ : M ⟶ M₂) :
    (idPullbackData (A := A)).map ψ = ψ :=
  rfl

/-- **The pullback along the identity morphism of ringed sites is a differential graded
pullback**: the pullback of a homotopy is the homotopy itself, the two homomorphisms it connects
being their own pullbacks. -/
def idPullbackDataHomotopyExtension :
    (idPullbackData.{t, a, m} (A := A)).HomotopyExtension where
  mapHomotopy {_M _M₂ ψ χ} h := by
    rwa [idPullbackData_map ψ, idPullbackData_map χ]

end Identity

/-! ### The derived tensor product -/

section DerivedTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A A' : DifferentialGradedAlgebra.{t, a} R}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {g : GoodResolutionData.{t, a, m, v, u} A}
  [(quasiIsomorphisms.{t, a, m} A).HasRightCalculusOfFractions]

/-- **The derived tensor product** `- ⊗^L_𝒜 𝒩 : D(𝒜, d) ⥤ D(𝒜', d)` with a differential graded
`(𝒜, 𝒜')`-bimodule `𝒩` on a ringed site: the derived pullback-tensor functor for the identity
morphism of ringed sites, along which a right differential graded module is its own pullback, so
that the functor of differential graded modules being derived is `ℳ ↦ ℳ ⊗_𝒜 𝒩`. Its value on a
good module `𝒫` is `𝒫 ⊗_𝒜 𝒩`, which is `derivedTensorObjIso`. -/
noncomputable def derivedTensor
    (hE : PullbackTensorExactnessData (idPullbackData.{t, a, m} (A := A)) D g) :
    derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a, s} A' :=
  derivedPullbackTensor idPullbackDataHomotopyExtension hE

/-- The value of the derived tensor product at the image in `D(𝒜, d)` of a good right
differential graded `𝒜`-module `𝒫` is the image in `D(𝒜', d)` of `𝒫 ⊗_𝒜 𝒩`. -/
noncomputable def derivedTensorObjIso
    (hE : PullbackTensorExactnessData (idPullbackData.{t, a, m} (A := A)) D g)
    {Q : DifferentialGradedModule.{t, a, m} A} (hQ : g.IsGood Q) :
    (derivedTensor hE).obj
        ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj Q)) ≅
      (toDerivedCategory.{t, a, s} A').obj
        ((HomotopyCategory.quotient.{t, a, s} A').obj (D.functor.obj Q)) :=
  derivedPullbackTensorObjIso idPullbackDataHomotopyExtension hE hQ

end DerivedTensor

/-! ### The derived pullback -/

section DerivedPullback

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]
  {w : C' ⥤ C} {σ : R'.obj ⟶ w.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom w σ B A}
  {P : PullbackData.{t, a, m, v, u, a', m'} φ}
  {g : GoodResolutionData.{t, a', m', v', u'} B}
  [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]

/-- **The derived pullback** `Lf^* : D(ℬ, d) ⥤ D(𝒜, d)` along a morphism of ringed sites and a
homomorphism of sheaves of differential graded algebras: the derived pullback-tensor functor for
the diagonal bimodule `{}_𝒜 𝒜_𝒜`, the tensor product with which is the identity functor, so that
the functor of differential graded modules being derived is the pullback `f^*`. Its value on a
good module `𝒫` is `f^*𝒫`, which is `derivedPullbackObjIso`. -/
noncomputable def derivedPullback (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P (tensorFunctorDataDiagonal.{t, a, m} A) g) :
    derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, m} A :=
  derivedPullbackTensor E hE

/-- The value of the derived pullback at the image in `D(ℬ, d)` of a good right differential
graded `ℬ`-module `𝒫` is the image in `D(𝒜, d)` of `f^*𝒫`. -/
noncomputable def derivedPullbackObjIso (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P (tensorFunctorDataDiagonal.{t, a, m} A) g)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) :
    (derivedPullback E hE).obj
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj Q)) ≅
      (toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj (P.obj Q)) :=
  derivedPullbackTensorObjIso E hE hQ

end DerivedPullback

end DifferentialGradedModule

end SheafOfModules

end
