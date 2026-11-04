module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardStalkColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMapStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleTensorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteStalkPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# The projection formula `𝓖 ⊗_ℬ f_*𝓕 ≅ f_*(f^*𝓖 ⊗_𝒜 𝓕)` for a finite morphism of algebraic spaces

Let `S` be a scheme and `π : X ⟶ Y` a finite morphism of algebraic spaces over `S`. Let `𝒜` be
a sheaf of rings on `X_étale`, `ℬ` a sheaf of rings on `Y_étale`, and `φ : ℬ ⟶ π_*𝒜` a
homomorphism of sheaves of rings; these data are a morphism of ringed topoi

`f = (π, φ) : (Sh(X_étale), 𝒜) ⟶ (Sh(Y_étale), ℬ)`

and Stacks 0DK4 states that for a sheaf of `𝒜`-modules `𝓕` and a sheaf of `ℬ`-modules `𝓖` the
canonical map

`𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)`

is an isomorphism.

The datum `f` and the canonical map are those of Stacks 04G0, which this repository builds for an
arbitrary morphism of algebraic spaces as `AlgebraicGeometry.Space.smallEtaleRingedToposHomOfSharp`
and `AlgebraicGeometry.Space.tensorPushforwardMap`: the two lemmas quantify over the same
`(π, φ)`, in the same direction, and ask about the same adjoint transpose, differing only in the
hypothesis under which it is invertible.

## Main results

* `AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isFinite`: Stacks 0DK4.
* `AlgebraicGeometry.Space.exists_bijective_pushforwardFiberMap_of_isFinite`: Stacks 0DK3 in the
  shape of the stalkwise criteria for morphisms of ringed topoi.
* `AlgebraicGeometry.Space.preservesColimitsOfSize_pushforwardModules_of_isFinite`: the direct
  image of modules along `f` commutes with colimits of shape in `Type 0`, so it is exact (the
  module form of Stacks 0A4K) and commutes with countable direct sums.

## Implementation notes

The proof is the source's. Isomorphisms of sheaves of modules on `Y_étale` are detected on the
stalks at geometric points (Stacks 04K5,
`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePoint`). At a geometric point `y`
with lifts `x₁, …, xₙ`, the stalk of `f_*𝓕` is `∏ᵢ 𝓕_{xᵢ}` (Stacks 0DK3,
`AlgebraicGeometry.Space.bijective_pushforwardFiberMap_of_isFinite`), the stalk of `f^*𝓖` at `xᵢ`
is `𝒜_{xᵢ} ⊗_{ℬ_y} 𝓖_y` (Stacks 04K2), stalks commute with tensor products (Stacks 03EL), and
the stalk of the canonical map becomes the identity
`𝓖_y ⊗_{ℬ_y} ∏ᵢ 𝓕_{xᵢ} = ∏ᵢ (𝒜_{xᵢ} ⊗_{ℬ_y} 𝓖_y) ⊗_{𝒜_{xᵢ}} 𝓕_{xᵢ}`
(`TensorProduct.tensorPiBaseChangeEquiv`). This assembly, for an arbitrary morphism of ringed
topoi with points, is
`Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints`; the theorem
below feeds it the points of the small étale sites and Stacks 0DK3.

## References

* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- At each geometric point `y` of `Y`, for `π : X ⟶ Y` finite, the stalk at `y` of the direct
image along `π` of a sheaf of sets on `X_étale` is the product of its stalks at the finitely many
geometric points of `X` lying over `y` (Stacks 0DK3), in the shape consumed by the stalkwise
criteria
`Stacks.SheafOfModules.preservesColimitsOfSize_pushforwardModules_of_isConservativeFamilyOfPoints`
and `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints`. -/
theorem exists_bijective_pushforwardFiberMap_of_isFinite (π : X ⟶ Y)
    (hπ : IsFinite B S hS π.hom) :
    ∀ Ψ : (SmallEtale.topology B S hS Y.1).Point.{u},
      ObjectProperty.ofObj (fun y : GeometricPoint B S hS Y.1 => etaleSitePoint B S hS Y.1 y Y.2)
        Ψ →
      ∃ (ι : Type u) (_ : Finite ι) (Φ : ι → (SmallEtale.topology B S hS X.1).Point.{u})
        (e : ∀ i, Ψ.sheafFiber (A := Type u) ≅
          (smallToposMorphismTypeU B S hS π).inverseImage ⋙ (Φ i).sheafFiber (A := Type u)),
        ∀ M : Sheaf (SmallEtale.topology B S hS X.1) (Type u), Function.Bijective
          (fun z i => ((smallToposMorphismTypeU B S hS π).pushforwardFiberMap (Φ i) Ψ (e i)).app
            M z) := by
  have hrep := ((isFinite_iff_representable B S hS π.hom X.2 Y.2).1 hπ).1
  rintro _ ⟨y⟩
  exact ⟨GeometricLifts B S hS π y, finite_geometricLifts B S hS π hπ y,
    fun v => etaleSitePoint B S hS X.1 (geometricLiftPoint B S hS π y v) X.2,
    fun v => stalkInverseImageIsoOfLift B S hS π hrep y v,
    fun M => bijective_pushforwardFiberMap_of_isFinite B S hS π hrep hπ y M⟩

/-- **Stacks 0DK4.** Let `π : X ⟶ Y` be a finite morphism of algebraic spaces over `S`, `𝒜` a
sheaf of rings on `X_étale`, `ℬ` a sheaf of rings on `Y_étale` and `φ : ℬ ⟶ π_*𝒜` a
homomorphism of sheaves of rings, with associated morphism of ringed topoi
`f = (π, φ) : (Sh(X_étale), 𝒜) ⟶ (Sh(Y_étale), ℬ)`. For every sheaf of `𝒜`-modules `𝓕` and every
sheaf of `ℬ`-modules `𝓖` the canonical map `𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)` is an
isomorphism. -/
@[stacks 0DK4]
theorem isIso_tensorPushforwardMap_of_isFinite (π : X ⟶ Y) (hπ : IsFinite B S hS π.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}}
    (φ : ℬ ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS π)).obj 𝒜)
    (𝓕 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS X 𝒜).O))
    (𝓖 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS Y ℬ).O)) :
    IsIso (tensorPushforwardMap B S hS π φ 𝓖 𝓕) :=
  Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints
    (smallEtaleRingedToposHomOfSharp B S hS π φ)
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS Y.1 Y.2)
    (exists_bijective_pushforwardFiberMap_of_isFinite B S hS π hπ) 𝓖 𝓕

/-- **Stacks 0A4K for modules over a finite morphism**: for `π : X ⟶ Y` finite, `𝒜` a sheaf of
rings on `X_étale`, `ℬ` one on `Y_étale` and `φ : ℬ ⟶ π_*𝒜`, the direct image of sheaves of
`𝒜`-modules along `f = (π, φ)` commutes with all colimits indexed by a small category in
`Type 0`. In particular it is exact, and it commutes with countable direct sums.

On the stalk at a geometric point `y` of `Y`, `f_*` is the finite product of the stalk functors
at the geometric points of `X` over `y` (Stacks 0DK3), and stalks commute with colimits. -/
theorem preservesColimitsOfSize_pushforwardModules_of_isFinite (π : X ⟶ Y)
    (hπ : IsFinite B S hS π.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}}
    (φ : ℬ ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS π)).obj 𝒜) :
    PreservesColimitsOfSize.{0, 0}
      (_root_.AlgebraicGeometry.RingedToposHom.pushforwardModules
        (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
        (Y := smallEtaleRingedToposOfRings B S hS Y ℬ) (ringedToposHomOfSharp B S hS π φ)) :=
  have :=
    Stacks.SheafOfModules.preservesColimitsOfSize_pushforwardModules_of_isConservativeFamilyOfPoints
      (ringedToposHomOfSharp B S hS π φ).toModulesHom
      (isConservativeFamilyOfPoints_etaleSitePoint B S hS Y.1 Y.2)
      (exists_bijective_pushforwardFiberMap_of_isFinite B S hS π hπ)
  preservesColimits_of_natIso (ringedToposHomOfSharp B S hS π φ).toModulesPushforwardIso

end AlgebraicGeometry.Space

end
