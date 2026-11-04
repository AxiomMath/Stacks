module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelIdentity
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalModule
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation

/-!
# The Fourier-Mukai construction as a functor of the kernel

Let `S` be a scheme, let `X` and `Y` be schemes over `S` and fix `M ∈ D(𝒪_X)`. The
Fourier-Mukai functor `Φ_K` of [Stacks, Tag 0FYQ] sends `M` to
`R pr_{2,*}(L pr_1^* M ⊗^𝐋 K)`; read instead as a function of the *kernel* `K`, this is the
functor

`Ψ_M : D(𝒪_{X ×_S Y}) ⟶ D(𝒪_Y)`,  `K ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋 K)`,

the composite of the derived tensor product with the fixed object `L pr_1^* M` on the left and
the derived direct image along `pr₂`. Both factors are exact, so `Ψ_M` is an exact functor of
triangulated categories. This is the functor the proof of [Stacks, Tag 0FZ6] applies to the
membership `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` of [Stacks, Tag 0FZ5]: "Since `L pr_1^* K ⊗^𝐋 −` is an exact functor
… Applying the exact functor `R pr_{2,*}` …".

The first of the two computations the source makes with it is that `Ψ_M(𝒪_Δ) = M` for a
separated `X ⟶ S`, which is Example [Stacks, Tag 0FYV]: `Ψ_M(𝒪_Δ)` is `Φ_{𝒪_Δ}(M)` on the nose,
and `Φ_{𝒪_Δ} ≅ 𝟭` is `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`.

## Main definitions

* `AlgebraicGeometry.fourierMukaiKernelFunctor` — the functor `Ψ_M`.

## Main results

* `AlgebraicGeometry.fourierMukaiKernelFunctor_obj` — `Ψ_M(K) = Φ_K(M)`, by definition.
* `AlgebraicGeometry.commShift_fourierMukaiKernelFunctor` and
  `AlgebraicGeometry.isTriangulated_fourierMukaiKernelFunctor` — `Ψ_M` is exact.
* `AlgebraicGeometry.fourierMukaiKernelFunctorDiagonalIso` — `Ψ_M(𝒪_Δ) ≅ M` for `f` separated,
  with `𝒪_Δ = Δ_*𝒪_X` the ordinary direct image placed in degree zero, for every `M`.

## Implementation notes

*The model of the derived categories.* As for `AlgebraicGeometry.fourierMukai`, everything is
read at `CategoryTheory.HasDerivedCategory.standard`, with a raised local priority.

*The commutation with the shift.* For the tensor factor it is the field `commShift_right` of the
derived tensor product of [Stacks, Tag 06YU], and its exactness is the field `exact_right`; for
the direct image it is the one a right derived functor carries,
`AlgebraicGeometry.commShift_derivedPushforward`.

## References

* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0FZ6](https://stacks.math.columbia.edu/tag/0FZ6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The Fourier-Mukai construction as a functor of the kernel.** For a fixed `M ∈ D(𝒪_X)`,
the functor `Ψ_M : D(𝒪_{X ×_S Y}) ⟶ D(𝒪_Y)`, `K ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋 K)`. -/
def fourierMukaiKernelFunctor (M : DerivedCategory X.Modules) :
    DerivedCategory (pullback f g).Modules ⥤ DerivedCategory Y.Modules :=
  dtenLeft (pullback f g) ((dpull (pullback.fst f g)).obj M) ⋙ dpush (pullback.snd f g)

/-- `Ψ_M(K)` is the value `Φ_K(M)` of the Fourier-Mukai functor with kernel `K` at `M`. -/
theorem fourierMukaiKernelFunctor_obj (M : DerivedCategory X.Modules)
    (K : DerivedCategory (pullback f g).Modules) :
    (fourierMukaiKernelFunctor f g M).obj K = (fourierMukai f g K).obj M :=
  rfl

/-- The derived tensor product with a fixed object on the left commutes with the shift: the
field `commShift_right` of the derived tensor product of [Stacks, Tag 06YU]. -/
local instance commShift_kernelFunctorTensor (W : Scheme.{u}) (A : DerivedCategory W.Modules) :
    (dtenLeft W A).CommShift ℤ :=
  (canonicalDerivedTensorProduct W.toRingedSpace.sheaf).commShift_right A

/-- The derived tensor product with a fixed object on the left is exact: the field
`exact_right` of the derived tensor product of [Stacks, Tag 06YU]. -/
local instance isTriangulated_kernelFunctorTensor (W : Scheme.{u})
    (A : DerivedCategory W.Modules) : (dtenLeft W A).IsTriangulated :=
  (canonicalDerivedTensorProduct W.toRingedSpace.sheaf).exact_right A

-- The derived direct image along a morphism of ringed spaces commutes with the shift and is
-- exact: the local instances `AlgebraicGeometry.commShift_derivedPushforward` and
-- `AlgebraicGeometry.isTriangulated_derivedPushforward`, re-activated here.
attribute [local instance] commShift_derivedPushforward isTriangulated_derivedPushforward

/-- `R p_*` commutes with the shift, read in the scheme spelling. -/
local instance commShift_kernelFunctorDpush {V W : Scheme.{u}} (p : V ⟶ W) :
    (dpush p).CommShift ℤ :=
  commShift_derivedPushforward p.toLRSHom.toShHom

/-- `R p_*` is exact, read in the scheme spelling. -/
local instance isTriangulated_kernelFunctorDpush {V W : Scheme.{u}} (p : V ⟶ W) :
    (dpush p).IsTriangulated :=
  isTriangulated_derivedPushforward p.toLRSHom.toShHom

/-- `Ψ_M` commutes with the shift, each of its two factors doing so. -/
instance commShift_fourierMukaiKernelFunctor (M : DerivedCategory X.Modules) :
    (fourierMukaiKernelFunctor f g M).CommShift ℤ :=
  Functor.CommShift.comp (F := dtenLeft (pullback f g) ((dpull (pullback.fst f g)).obj M))
    (G := dpush (pullback.snd f g))

/-- **`Ψ_M` is an exact functor of triangulated categories**: the derived tensor product with a
fixed object is exact by [Stacks, Tag 06YU], and the derived direct image is exact. -/
instance isTriangulated_fourierMukaiKernelFunctor (M : DerivedCategory X.Modules) :
    (fourierMukaiKernelFunctor f g M).IsTriangulated :=
  Functor.IsTriangulated.instComp (F := dtenLeft (pullback f g) ((dpull (pullback.fst f g)).obj M))
    (G := dpush (pullback.snd f g))

/-- **`Ψ_M(𝒪_Δ) ≅ M`** for a separated `f : X ⟶ S` and every `M ∈ D(𝒪_X)`, where
`𝒪_Δ = Δ_*𝒪_X` is the ordinary direct image of the structure sheaf along the diagonal, placed in
degree zero — the object of [Stacks, Tag 0FZ5]. This is the identity
`R pr_{2,*}(L pr_1^* K ⊗^𝐋 𝒪_Δ) = K` of the proof of [Stacks, Tag 0FZ6], which the source
attributes to Example [Stacks, Tag 0FYV]: `Ψ_M(RΔ_*𝒪_X) = Φ_{𝒪_Δ}(M)`, and `Φ_{𝒪_Δ} ≅ 𝟭` is
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso`; the ordinary and the derived direct image of
`𝒪_X` agree by `AlgebraicGeometry.diagonalKernelIsoDiagonalModule`. -/
def fourierMukaiKernelFunctorDiagonalIso [IsSeparated f] (M : DerivedCategory X.Modules) :
    (fourierMukaiKernelFunctor f f M).obj
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
            (SheafOfModules.unit X.ringCatSheaf))) ≅ M :=
  (fourierMukaiKernelFunctor f f M).mapIso (diagonalKernelIsoDiagonalModule f).symm ≪≫
    (fourierMukaiDiagonalKernelIso f).app M

end AlgebraicGeometry

end
