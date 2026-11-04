module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariants
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiNumbers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
import StacksCore.Tactic.StacksAttribute

/-!
# The numerical invariants of a coherent family and the substack `Coh^P_{X/B}` (Stacks 0DNC)

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation, let `I` be a
set, let `E_i` be a perfect object of `D(𝒪_X)` for each `i ∈ I`, and let `P : I → ℤ`; these are
the standing data `AlgebraicGeometry.Space.NumericalSituation`.  For an object `(T, 𝓕)` of
`Coh_{X/B}` — a scheme `T` over `B` and a finitely presented `𝒪_{X_T}`-module `𝓕`, flat over `T`
with support proper over `T` — Stacks 0DNC forms the object

`K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋_{𝒪_{X_T}} 𝓕)`

of `D(𝒪_T)`, where `E_{i,T}` is the derived pullback of `E_i` to `X_T = X ×_B T`, and the function

`χ_i : |T| → ℤ`,  `χ_i(t) = χ(K_i ⊗^𝐋_{𝒪_T} κ(t))`,

the Euler characteristic of the derived fibre of `K_i` at `t`.  The substack
`Coh^P_{X/B} ⊆ Coh_{X/B}` consists of the objects with `χ_i(t) = P(i)` for every `i ∈ I` and every
`t ∈ |T|`.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.numericalTensor`: the object
  `E_{i,T} ⊗^𝐋 𝓕` of `D(𝒪_{X_T})`.
* `AlgebraicGeometry.Space.NumericalSituation.numericalDirectImage`: **the object `K_i`** of
  `D(𝒪_T)`.
* `AlgebraicGeometry.Space.NumericalSituation.numericalEuler`: **the function `χ_i : |T| → ℤ`**,
  the derived-fibre Euler characteristic of `K_i`.
* `AlgebraicGeometry.Space.NumericalSituation.HasNumericalInvariants`: the condition
  `χ_i(t) = P(i)` for all `i` and `t`.
* `AlgebraicGeometry.Space.NumericalSituation.numericalSubstack`: **`Coh^P_{X/B}`**, the full
  subcategory of `Coh_{X/B}` cut out by that condition.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_restrict`: an object of
  `Coh^P_{X/B}` lies in `Coh^{P|_J}_{X/B}` for every subset `J ⊆ I`; this is the inclusion
  `Coh^P_{X/B} ⊆ Coh^{P'}_{X/B}` by which Stacks 0DND reduces an infinite index set to its finite
  subsets.
* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_iff_restrict`: `Coh^P_{X/B}`
  is the intersection of the `Coh^{P|_J}_{X/B}` over the finite subsets `J ⊆ I`.

## Implementation notes

All four operations entering `K_i` are the derived functors of the small étale ringed topoi of
algebraic spaces: the derived pullback is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`
along the projection `X_T ⟶ X`, the derived tensor product is
`Stacks.SheafOfModules.derivedTensorProductFunctor` on the small étale ringed site of `X_T`, the
module `𝓕` enters as the complex concentrated in degree `0`, and `Rf_{T,*}` is
`Stacks.DerivedFunctor.totalRightDerived` of the direct image along the projection `X_T ⟶ T`.  So
`K_i` is an object of `D(𝒪_T)` for the small étale structure sheaf of `T`, which is the convention
of the source for a scheme regarded as an algebraic space.

The value `χ_i(t)` is `AlgebraicGeometry.Space.derivedFibreEuler` of `K_i`: the alternating sum of
the dimensions `dim_k H^n(K_i ⊗^𝐋 k)` for a field-valued point `Spec(k) ⟶ T` representing `t`.
For a perfect `K_i` this is the source's `χ(K_i ⊗^𝐋 κ(t))`, the field `k` being an extension of
`κ(t)`.  The module universe of the standing data is that of the structure rings, which is the
universe of the derived pullback, the derived direct image and the derived tensor product.

The substack is the full subcategory of the category structure
`AlgebraicGeometry.Space.CoherentSituation.coherentCategory` on the objects of `Coh_{X/B}`, for
the canonical pseudofunctoriality datum `AlgebraicGeometry.Space.modulePushforwardCoherence`.

## References

* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace NumericalSituation

variable (N : NumericalSituation.{u, v, u} B S hS D) (A : CoherentObject D)

/-- The test scheme `T` of an object `(T, 𝓕)` of `Coh_{X/B}`, as an algebraic space. -/
abbrev testSpace : AlgebraicSpaces B S hS := (schemeSpaceFunctor B S hS).obj A.T.left

/-- The object `E_{i,T} ⊗^𝐋_{𝒪_{X_T}} 𝓕` of `D(𝒪_{X_T})`: the derived tensor product of the derived
pullback of `E_i` along the projection `X_T ⟶ X` with the module `𝓕` placed in degree `0`. -/
def numericalTensor (i : N.I) :
    DerivedCategory (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedSite B S hS (D.space A.T).1 (D.space A.T).2)).obj
    ((smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A.T)).obj (N.E i))).obj
    ((DerivedCategory.singleFunctor _ 0).obj A.F)

/-- For an object `(T, 𝓕)` of `Coh_{X/B}` and `i ∈ I`, the object
`K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋_{𝒪_{X_T}} 𝓕)` of `D(𝒪_T)`, where `f_T : X_T ⟶ T` is the projection of
the base change and `E_{i,T}` the derived pullback of `E_i` to `X_T`. -/
@[stacks 0DNC "the object `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)` of `D(𝒪_T)`"]
def numericalDirectImage (i : N.I) :
    DerivedCategory (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2) :=
  (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS (D.projection A.T))).obj
    (N.numericalTensor A i)

/-- The function `χ_i : |T| → ℤ` whose value at a point `t` of `T` is the Euler characteristic
`χ(K_i ⊗^𝐋 κ(t)) = ∑ (-1)^n dim H^n(K_i ⊗^𝐋 κ(t))` of the derived fibre of `K_i` at `t`. -/
@[stacks 0DNC "the function `χ_i : |T| → ℤ`, `t ↦ χ(K_i ⊗^𝐋 κ(t))`"]
def numericalEuler (i : N.I) : points B S hS (testSpace A).1 → ℤ :=
  derivedFibreEuler (testSpace A) (N.numericalDirectImage A i)

/-- An object `(T, 𝓕)` of `Coh_{X/B}` has the numerical invariants `P` when `χ_i(t) = P(i)` for
every `i ∈ I` and every point `t` of `T`. -/
def HasNumericalInvariants : Prop :=
  ∀ (i : N.I) (t : points B S hS (testSpace A).1), N.numericalEuler A i t = N.P i

/-- The substack `Coh^P_{X/B} ⊆ Coh_{X/B}`: the full subcategory of `Coh_{X/B}` on the objects
`(T, 𝓕)` with `χ_i(t) = P(i)` for all `i ∈ I` and all `t ∈ |T|`. -/
@[stacks 0DNC "the substack `Coh^P_{X/B} ⊆ Coh_{X/B}` cut out by `χ_i(t) = P(i)`"]
abbrev numericalSubstack : Type (u + 1) :=
  letI : Category.{u + 1} (CoherentObject D) :=
    CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D
  ObjectProperty.FullSubcategory N.HasNumericalInvariants

/-- The value `χ_i(t)` is the derived-fibre Euler characteristic of `K_i` at `t`. -/
theorem numericalEuler_apply (i : N.I) (t : points B S hS (testSpace A).1) :
    N.numericalEuler A i t = derivedFibreEuler (testSpace A) (N.numericalDirectImage A i) t :=
  rfl

/-- An object has the numerical invariants `P` if and only if `χ_i(t) = P(i)` for every `i ∈ I`
and every point `t` of `T`. -/
theorem hasNumericalInvariants_iff :
    N.HasNumericalInvariants A ↔
      ∀ (i : N.I) (t : points B S hS (testSpace A).1), N.numericalEuler A i t = N.P i :=
  Iff.rfl

/-- The objects `K_i` of the restricted standing data are those of the original data. -/
@[simp]
theorem numericalDirectImage_restrict (J : Set N.I) (i : J) :
    (N.restrict J).numericalDirectImage A i = N.numericalDirectImage A i.1 :=
  rfl

/-- The functions `χ_i` of the restricted standing data are those of the original data. -/
@[simp]
theorem numericalEuler_restrict (J : Set N.I) (i : J) :
    (N.restrict J).numericalEuler A i = N.numericalEuler A i.1 :=
  rfl

/-- An object of `Coh^P_{X/B}` lies in `Coh^{P|_J}_{X/B}` for every subset `J` of the index set. -/
theorem hasNumericalInvariants_restrict {A : CoherentObject D} (h : N.HasNumericalInvariants A)
    (J : Set N.I) : (N.restrict J).HasNumericalInvariants A :=
  fun i t => h i.1 t

/-- `Coh^P_{X/B}` is the intersection of the `Coh^{P|_J}_{X/B}` over the finite subsets `J` of the
index set. -/
theorem hasNumericalInvariants_iff_restrict :
    N.HasNumericalInvariants A ↔
      ∀ J : Set N.I, J.Finite → (N.restrict J).HasNumericalInvariants A := by
  refine ⟨fun h J _ => N.hasNumericalInvariants_restrict h J, fun h i t => ?_⟩
  exact h {i} (Set.finite_singleton i) ⟨i, rfl⟩ t

end NumericalSituation

end AlgebraicGeometry.Space

end
