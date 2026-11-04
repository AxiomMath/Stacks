module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison

/-!
# The cohomology of a derived tensor product with a flat module in degree zero

Let `W` be a scheme, let `K` be an object of `D(𝒪_W)` and let `N` be a flat `𝒪_W`-module.  Then

`H^i(K ⊗^𝐋 N[0]) ≅ H^i(K) ⊗ N`

for every `i`, and consequently tensoring with `N[0]` does not lower the degrees in which `K` has
cohomology: if `K` has none below degree `n`, neither has `K ⊗^𝐋 N[0]`.

The statement about a cochain complex is
`Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso`, on a ringed site.  What this file adds is
the passage to an arbitrary object of the derived category -- which is a transport along a
representative, the localization functor `DerivedCategory.Q` being essentially surjective -- and
the boundedness-below consequence.

Both are inputs to step 1 of the proof of [Stacks, Tag 0G0E], where the object tensored is the
kernel `K` on `X ×_k X` and the flat module is a box product `ℰ^∨ ⊠ 𝒢^∨` of finite locally free
modules: the display computes the cohomology of `K ⊗^𝐋 (ℰ^∨ ⊠ 𝒢^∨)[0]` in the lowest degree where
`K` has any, and that degree is the lowest degree of the tensor product only because tensoring
with a flat module in degree zero preserves the bound.

## Main definitions

* `AlgebraicGeometry.homologyTensorSingleFlatIso` — `H^i(K ⊗^𝐋 N[0]) ≅ H^i(K) ⊗ N` for flat `N`,
  for an arbitrary object `K` of `D(𝒪_W)` and every degree.

## Main results

* `AlgebraicGeometry.isGE_tensorSingleFlat` — if `K` has no cohomology below degree `n`, neither
  has `K ⊗^𝐋 N[0]`.

## Implementation notes

*The representative.*  `CategoryTheory.Functor.objPreimage` and
`CategoryTheory.Functor.objObjPreimageIso` for `DerivedCategory.Q`, which is essentially
surjective, give a cochain complex `L` with `Q(L) ≅ K`; the isomorphism is transported through the
first variable of the derived tensor bifunctor, and `L`'s own cohomology is identified with that of
`K` by `DerivedCategory.homologyFunctorFactors`.  No choice beyond `objPreimage`'s enters, and it
is a choice of object only, so nothing downstream has to be natural in it.

*No glue between spellings is needed.*
`Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso` is stated on a small ringed site for
`Stacks.DerivedTensor.RingedSite.Modules`, and `dtenLeft` and
`AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace` are stated at the scheme spelling
`AlgebraicGeometry.Scheme.Modules`; the site of a scheme is its site of opens and the two
spellings are `rfl`-equal, and here unification crosses them unaided -- unlike the
`HasDerivedCategory` *instances*, which are what needs bridging in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/ExternalTensor/SingleComparison.lean`.  Only the
two additivity instances of the tensor bifunctor have to be named, for the usual reason that
instance search is keyed on the spelling.

*The model of the derived categories.*  `CategoryTheory.HasDerivedCategory.standard` is activated
as a local instance at high priority, as in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/BoxDisplay.lean`, rather than taken
as a binder: the derived tensor bifunctor and the ringed-site comparison have to be read at *one*
model, and a binder at the `Scheme.Modules` spelling is not found at the ringed-site spelling the
comparison is stated at, so the two would be instantiated at different models and the hom
universes would not agree.

*Additivity in the first variable.*  `Stacks.SheafOfModules.Tensor.sheafTensor` is additive as a
functor into the functor category, which is additivity in its first variable; what the
boundedness-below argument needs is that `- ⊗ N` carries a zero object to a zero object, so the
additivity has to be read on the flipped partial application.  That is
`AlgebraicGeometry.sheafTensorFlipObjAdditive` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/ExternalTensor/SingleComparison.lean`, a `local
instance` there, re-activated here rather than restated.  The named instance for the *second*
variable, `sheafTensorObjAdditive`, is the wrong one.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

-- Tensoring with a fixed module in the *first* variable is additive.  The declaration is
-- `AlgebraicGeometry.sheafTensorFlipObjAdditive` of
-- `StacksFrontier/AlgebraicGeometry/DerivedVarieties/ExternalTensor/SingleComparison.lean`, where it
-- is a `local instance`; it has to be re-activated here.  The named instance for the *second*
-- variable, `Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive`, does not give it.
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive

attribute [local instance 100000] HasDerivedCategory.standard

variable (W : Scheme.{u})

/-- **The cohomology of a derived tensor product with a flat module in degree zero**:

`H^i(K ⊗^𝐋 N[0]) ≅ H^i(K) ⊗ N`

for a flat `𝒪_W`-module `N`, an arbitrary object `K` of `D(𝒪_W)` and an arbitrary degree `i`.

`Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso` is this for a cochain complex; `K` is
replaced by a representative, `DerivedCategory.Q` being essentially surjective, and the
representative's cohomology is identified with `H^i(K)` by
`DerivedCategory.homologyFunctorFactors`. -/
def homologyTensorSingleFlatIso (K : DerivedCategory W.Modules) (N : W.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.toRingedSpace.sheaf) N)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor W.Modules i).obj
        ((dtenLeft W K).obj ((DerivedCategory.singleFunctor W.Modules 0).obj N)) ≅
      Scheme.Modules.tensorObjRingedSpace W
        ((DerivedCategory.homologyFunctor W.Modules i).obj K) N :=
  letI e : DerivedCategory.Q.obj ((DerivedCategory.Q (C := W.Modules)).objPreimage K) ≅ K :=
    (DerivedCategory.Q (C := W.Modules)).objObjPreimageIso K
  (DerivedCategory.homologyFunctor W.Modules i).mapIso
      (((derivedTensorProductFunctor W.toRingedSpace.sheaf).mapIso e).app
        ((DerivedCategory.singleFunctor W.Modules 0).obj N)).symm ≪≫
    homologyTensorFlatIso W.toRingedSpace.sheaf N hN
      ((DerivedCategory.Q (C := W.Modules)).objPreimage K) i ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).mapIso
      (((DerivedCategory.homologyFunctorFactors W.Modules i).app
          ((DerivedCategory.Q (C := W.Modules)).objPreimage K)).symm ≪≫
        (DerivedCategory.homologyFunctor W.Modules i).mapIso e)).app N

/-- **The tensor product of a zero module with any module is zero**, read in the first variable:
`- ⊗ N` is additive, so it carries a zero object to a zero object. -/
theorem isZero_tensorObjRingedSpace_of_isZero (A N : W.Modules) (hA : IsZero A) :
    IsZero (Scheme.Modules.tensorObjRingedSpace W A N) :=
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).flip.obj N).Additive :=
    sheafTensorFlipObjAdditive W N
  have := Functor.preservesZeroMorphisms_of_additive
    (F := (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).flip.obj N)
  Functor.map_isZero ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).flip.obj N) hA

/-- **Tensoring with a flat module in degree zero preserves a bound from below.**  If `K` has no
cohomology below degree `n`, then neither has `K ⊗^𝐋 N[0]`, for `N` flat.

In degree `j < n` the cohomology of the tensor product is `H^j(K) ⊗ N` by
`AlgebraicGeometry.homologyTensorSingleFlatIso`, and `H^j(K)` is zero. -/
theorem isGE_tensorSingleFlat (K : DerivedCategory W.Modules) (N : W.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.toRingedSpace.sheaf) N)
    (n : ℤ) [K.IsGE n] :
    ((dtenLeft W K).obj ((DerivedCategory.singleFunctor W.Modules 0).obj N)).IsGE n :=
  (DerivedCategory.isGE_iff _ n).2 fun j hj =>
    IsZero.of_iso
      (isZero_tensorObjRingedSpace_of_isZero W
        ((DerivedCategory.homologyFunctor W.Modules j).obj K) N
        (DerivedCategory.isZero_of_isGE K n j hj))
      (homologyTensorSingleFlatIso W K N hN j)

end AlgebraicGeometry

end
