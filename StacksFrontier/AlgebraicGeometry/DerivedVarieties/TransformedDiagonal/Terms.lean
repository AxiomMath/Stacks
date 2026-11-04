module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The terms of the transformed resolution of the diagonal, with nothing carried

The terms `AlgebraicGeometry.DiagonalResolution.transformedTerm` of the complex of
[Stacks, Tag 0G0A], the transport `AlgebraicGeometry.DiagonalResolution.HomTransport` and the
complex `AlgebraicGeometry.DiagonalResolution.HomTransport.complex` it determines all take as an
argument `hG` the perfectness of the second factors `𝒢ᵢ` of the resolution placed in degree
zero — which is what puts them in the source of `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`. This file
supplies two things those declarations are used with.

* `AlgebraicGeometry.DiagonalResolution.isPerfect_singleFunctor_right` proves `hG`: a second factor
  of a resolution of the diagonal is finite locally free, and a finite locally free module in
  degree zero is perfect. Every later statement about the complex of [Stacks, Tag 0G0A] reads
  `transformedTerm`, `HomTransport` and `HomTransport.complex` at this proof, so none of them
  carries the perfectness of the `𝒢ᵢ` as a hypothesis.
* `AlgebraicGeometry.derivedExternalTensorAt` is the derived external tensor product
  `K ⊠ L = Lp^*K ⊗^𝐋 Lq^*L` with the three models of the derived categories as binders.
  `AlgebraicGeometry.derivedExternalTensor` is stated through `Stacks.Duality.derivedPullback`
  and `Stacks.Duality.derivedTensor`, neither of which takes a `HasDerivedCategory` binder, so it
  is pinned to the locally small model; the version here names instead the ringed-space derived
  pullback of [Stacks, Tag 06YJ] and the ringed-site derived tensor product of
  [Stacks, Tag 06YU], which take theirs as binders, so that it can be read at
  `CategoryTheory.HasDerivedCategory.standard`, where [Stacks, Tag 0FXZ] and the
  Fourier–Mukai vocabulary are stated. At the locally small model the two agree by `rfl`
  (`AlgebraicGeometry.derivedExternalTensorAt_eq`).

## Main definitions

* `AlgebraicGeometry.derivedExternalTensorAt`: `K ⊠ L` at any three models.
* `AlgebraicGeometry.DiagonalResolution.imageTerm` and
  `AlgebraicGeometry.DiagonalResolution.ImageHomTransport`: the terms `ℰᵢ ⊠ F(𝒢ᵢ)` and the
  transport of Hom groups, read at the proof of `hG`.

## Main results

* `AlgebraicGeometry.derivedExternalTensorAt_eq`: at the locally small model it is
  `AlgebraicGeometry.derivedExternalTensor`.
* `AlgebraicGeometry.DiagonalResolution.isPerfect_singleFunctor_right`: a second factor `𝒢ᵢ` of a
  resolution of the diagonal, placed in degree zero, is a perfect object of `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.PerfectComplexes

universe w w₁ w₂ w₃ u

namespace AlgebraicGeometry

/-! ### The three spellings of the category of modules on a scheme -/

/-- `HasDerivedCategory` for `𝒪_W`-modules spelled as sheaves of modules over the structure
sheaf of the underlying ringed space, which is the spelling the derived pullback of
[Stacks, Tag 06YJ] is stated at.  The type is `W.Modules` by `rfl`, but an instance proved at
one spelling is not retrieved at the other. -/
local instance (priority := 10000) hasDerivedCategoryRingedSpace (W : Scheme.{u})
    [i : HasDerivedCategory.{w} W.Modules] :
    HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) := i

/-- `HasDerivedCategory` for `𝒪_W`-modules spelled through
`Stacks.SheafOfModules.Tensor.ringSheaf`, which is the spelling the derived tensor product of
[Stacks, Tag 06YU] is stated at.  Again the type is `W.Modules` by `rfl`. -/
local instance (priority := 10000) hasDerivedCategoryTensorSite (W : Scheme.{u})
    [i : HasDerivedCategory.{w} W.Modules] :
    HasDerivedCategory.{w} (Stacks.DerivedTensor.RingedSite.Modules W.sheaf) := i

/-! ### The derived external tensor product at any model -/

/-- The derived external tensor product `K ⊠ L` of an object of `D(𝒪_X)` and an object of
`D(𝒪_Y)`, for `X` and `Y` schemes over `S`: the derived tensor product on `X ×_S Y` of the
derived pullbacks of `K` and `L` along the two projections, with the three models of the derived
categories as binders.

At the locally small model it is `AlgebraicGeometry.derivedExternalTensor`
(`AlgebraicGeometry.derivedExternalTensorAt_eq`); the binders are what let it be read at
`CategoryTheory.HasDerivedCategory.standard`. -/
@[sga "5 III 6.2", sga "6 III 1.6", sga "6 III 3.5", sga "6 III 4.7"]
def derivedExternalTensorAt {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} Y.Modules]
    [HasDerivedCategory.{w₃} (pullback f g).Modules]
    (K : DerivedCategory X.Modules) (L : DerivedCategory Y.Modules) :
    DerivedCategory (pullback f g).Modules :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (pullback f g).sheaf).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst f g).toLRSHom.toShHom).obj K)).obj
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd f g).toLRSHom.toShHom).obj L)

/-- **At the locally small model the derived external tensor product of any model is
`AlgebraicGeometry.derivedExternalTensor`.** -/
theorem derivedExternalTensorAt_eq {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory X.Modules) (L : DerivedCategory Y.Modules) :
    derivedExternalTensorAt f g K L = derivedExternalTensor f g K L :=
  rfl

/-! ### The second factors are perfect -/

namespace DiagonalResolution

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
  (R : DiagonalResolution f)

/-- **A second factor of a resolution of the diagonal, placed in degree zero, is a perfect
object of `D(𝒪_X)`.** The factor is finite locally free, and a finite locally free module in
degree zero is perfect. This is the argument `hG` of
`AlgebraicGeometry.DiagonalResolution.transformedTerm`, which places `𝒢ᵢ` in the source of `F`. -/
theorem isPerfect_singleFunctor_right (i : ℕ) :
    IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (R.right i)) :=
  isPerfect_singleFunctor_of_isFiniteLocallyFree X _
    ⟨(R.right_finiteLocallyFree i).exists_isFiniteLocallyFreeData⟩

/-! ### The terms and the transport, read at that proof -/

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) (F : perfectDerived X ⥤ perfectDerived Y)

/-- The term `ℰᵢ ⊠ F(𝒢ᵢ)` of the complex of [Stacks, Tag 0G0A]:
`AlgebraicGeometry.DiagonalResolution.transformedTerm` at the perfectness of the second factors
proved by `AlgebraicGeometry.DiagonalResolution.isPerfect_singleFunctor_right`, so with nothing
carried. -/
abbrev imageTerm (i : ℕ) : DerivedCategory (pullback f g).Modules :=
  R.transformedTerm g F R.isPerfect_singleFunctor_right i

/-- An identification of the Hom groups between the terms `ℰᵢ ⊠ 𝒢ᵢ` with those between the terms
`ℰᵢ ⊠ F(𝒢ᵢ)`, compatible with identities and composition:
`AlgebraicGeometry.DiagonalResolution.HomTransport` at the perfectness of the second factors
proved by `AlgebraicGeometry.DiagonalResolution.isPerfect_singleFunctor_right`. Its complex,
the terms of that complex and its differentials are
`AlgebraicGeometry.DiagonalResolution.HomTransport.complex`,
`AlgebraicGeometry.DiagonalResolution.HomTransport.complex_X` and
`AlgebraicGeometry.DiagonalResolution.HomTransport.complex_d`. -/
abbrev ImageHomTransport : Type u :=
  HomTransport R g F R.isPerfect_singleFunctor_right

end DiagonalResolution

end AlgebraicGeometry

end
