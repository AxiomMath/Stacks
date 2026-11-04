module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Situation
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethUnconditional
public import StacksFrontier.Homology.KunnethDegreeZero

/-!
# The global Künneth formula over a field in degree zero, on elements

Let `k` be a field, let `X` and `Y` be schemes quasi-compact and quasi-separated over `Spec k`,
let `W = X ×_k Y` with projections `p` and `q`, and let `K ∈ D_QCoh(𝒪_X)` and
`M ∈ D_QCoh(𝒪_Y)`. Suppose the cohomology of `RΓ(X, K)` and of `RΓ(Y, M)` vanishes in negative
degrees. This file proves that the canonical `k`-bilinear map

`H⁰RΓ(X, K) × H⁰RΓ(Y, M) ⟶ H⁰RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

exhibits its target as the tensor product over `k` of its two sources. The map is the
cohomology product of [Stacks, Tag 068H] in degree zero, `[x] ⊗ [y] ↦ [x ⊗ y]`, followed by
`H⁰` of the global Künneth morphism of [Stacks, Tag 0G7V] for the canonical global cup product of
Cohomology, Section 0FKU. The conclusion is stated about that map, on elements, and not as an
abstract isomorphism: `AlgebraicGeometry.isTensorPairing_degreeZeroKunnethPairing` is in the
shape `AlgebraicGeometry.IsTensorPairing`, and
`AlgebraicGeometry.degreeZeroKunnethLinearEquiv` is a `k`-linear equivalence out of
`H⁰RΓ(X, K) ⊗_k H⁰RΓ(Y, M)` whose value at a pure tensor is
`AlgebraicGeometry.degreeZeroKunnethLinearEquiv_tmul`.

## The two links

* The global Künneth morphism is an isomorphism, by the second conclusion of
  [Stacks, Tag 0FLQ], `Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`. Its
  hypotheses are met: `Spec k` is affine and every pair of schemes over a field is Tor
  independent, `AlgebraicGeometry.torIndependent_over_field`.
* The cohomology product in degree zero is an isomorphism over a field when both arguments have
  no cohomology in negative degrees, by
  `CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero`.

## The two models of `D(k)`

The global Künneth morphism lives in `D(A)` for `A = Γ(Spec k, 𝒪)`, which is isomorphic to `k`
but not equal to it. The degree-zero statement is therefore applied over `A`, which is a field by
`AlgebraicGeometry.gammaSectionsField`, and the resulting `A`-linear isomorphism
`AlgebraicGeometry.degreeZeroKunnethMap` is read over `k` by restriction of scalars along
`k ≅ A`, which is monoidal by `Stacks.ModuleCat.RingIsoTransport.isIso_baseChange`. The field
structure on `A` enters only inside proofs, so no statement here mentions it.

## Main definitions

* `AlgebraicGeometry.degreeZeroSections`: `H⁰RΓ(V, N)` over `A`, for `c : V ⟶ Spec k`.
* `AlgebraicGeometry.degreeZeroKunnethMap`: the canonical `A`-linear map
  `H⁰RΓ(X, K) ⊗_A H⁰RΓ(Y, M) ⟶ H⁰RΓ(W, Lp^*K ⊗^𝐋 Lq^*M)`.
* `AlgebraicGeometry.degreeZeroKunnethLinearEquiv`: the same map, over `k`, as a linear
  equivalence.
* `AlgebraicGeometry.degreeZeroKunnethPairing`: its additive extension to formal integral
  combinations of pairs.

## Main results

* `AlgebraicGeometry.isIso_degreeZeroKunnethMap`: the `A`-linear map is an isomorphism.
* `AlgebraicGeometry.degreeZeroKunnethLinearEquiv_tmul`: the `k`-linear equivalence at
  `x ⊗ y` is the `A`-linear map at `x ⊗ y`.
* `AlgebraicGeometry.isTensorPairing_degreeZeroKunnethPairing`: **the pairing exhibits
  `H⁰RΓ(W, Lp^*K ⊗^𝐋 Lq^*M)` as `H⁰RΓ(X, K) ⊗_k H⁰RΓ(Y, M)`**.
* `AlgebraicGeometry.isTensorPairing_of_linearEquiv`: a pairing that factors through a
  `k`-linear equivalence out of `M ⊗_k N` is a tensor pairing.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.GlobalKunneth (baseRing tensorBase sectionsOverBase)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

/-! ### Tensor pairings from linear equivalences -/

section TensorPairing

variable {k : Type*} [CommRing k] {M N P : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

/-- **A pairing that factors through a `k`-linear equivalence out of `M ⊗_k N` exhibits its
target as the tensor product.** If the additive extension `p` of a pairing of `M` and `N` sends
each generator `(m, n)` to `e (m ⊗ n)` for a `k`-linear equivalence `e : M ⊗_k N ≃ P`, then `p`
is surjective and its kernel is the subgroup of `k`-bilinearity relations. -/
theorem isTensorPairing_of_linearEquiv (e : M ⊗[k] N ≃ₗ[k] P)
    (p : FreeAbelianGroup (M × N) →+ P)
    (hp : ∀ m n, p (FreeAbelianGroup.of (m, n)) = e (m ⊗ₜ[k] n)) :
    IsTensorPairing k M N p := by
  have hcomp : ∀ u, p u = e (freeAbelianGroupToTensor k M N u) := by
    intro u
    induction u using FreeAbelianGroup.induction_on with
    | zero => simp
    | of mn => rw [hp, freeAbelianGroupToTensor_of]
    | neg mn h => rw [map_neg, h, map_neg, map_neg]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := surjective_freeAbelianGroupToTensor k M N (e.symm z)
    exact ⟨u, by rw [hcomp, hu, LinearEquiv.apply_symm_apply]⟩
  · ext u
    simp only [AddMonoidHom.mem_ker, hcomp, LinearEquiv.map_eq_zero_iff]

end TensorPairing

/-! ### Degree-zero cohomology of derived sections over `Spec k` -/

variable (k : Type u) [Field k] {X Y : Scheme.{u}}

/-- **`H⁰RΓ(V, N)`**, over `A = Γ(Spec k, 𝒪)`, for a scheme `c : V ⟶ Spec k` over a field and
`N ∈ D(𝒪_V)`: the degree-zero cohomology of the derived sections of `N` over `V`, with scalars
restricted along `c^♯` to the functions on the base. -/
abbrev degreeZeroSections {V : Scheme.{u}} (c : V ⟶ Spec (.of k))
    (N : DerivedCategory V.Modules) :
    ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).obj
    ((sectionsOverBase c.toLRSHom.toShHom).obj N)

/-- The canonical global cup product of Cohomology, Section 0FKU, on `Spec k`: the one at which
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme` is stated. -/
abbrev canonicalGlobalCupProduct :
    Stacks.Cohomology.GlobalKunneth.GlobalCupProduct (Spec (.of k)).toRingedSpace :=
  Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct
    (Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace
      (Spec (.of k)).toRingedSpace)

/-- `Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M` on `W = X ×_k Y`. -/
abbrev boxDerived (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules) :
    DerivedCategory (Limits.pullback f g).Modules :=
  ((derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).obj
      ((derivedPullback (Limits.pullback.fst f g).toLRSHom.toShHom).obj K)).obj
    ((derivedPullback (Limits.pullback.snd f g).toLRSHom.toShHom).obj M)

/-! ### The degree-zero Künneth map over `Γ(Spec k, 𝒪)` -/

/-- **The degree-zero Künneth map.** For `f : X ⟶ Spec k`, `g : Y ⟶ Spec k`, `K ∈ D(𝒪_X)` and
`M ∈ D(𝒪_Y)`, the `A`-linear map

`H⁰RΓ(X, K) ⊗_A H⁰RΓ(Y, M) ⟶ H⁰RΓ(X ×_k Y, Lp^*K ⊗^𝐋 Lq^*M)`

for `A = Γ(Spec k, 𝒪)`: the cohomology product of [Stacks, Tag 068H] in degree zero, given by
tensoring cocycles, followed by `H⁰` of the global Künneth morphism of [Stacks, Tag 0G7V] at the
canonical global cup product. -/
def degreeZeroKunnethMap (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules) :
    degreeZeroSections k f K ⊗ degreeZeroSections k g M ⟶
      degreeZeroSections k (Limits.pullback.fst f g ≫ f) (boxDerived k f g K M) :=
  (RingTheory.TorProducts.cohomologyTensorProduct
      ((sectionsOverBase f.toLRSHom.toShHom).obj K)
      ((sectionsOverBase g.toLRSHom.toShHom).obj M) 0 0).map ≫
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) (0 + 0)).map
      (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme f g
        (canonicalGlobalCupProduct k) K M)

/-- **The degree-zero Künneth map is an isomorphism over a field.** Let `X` and `Y` be
quasi-compact and quasi-separated over `Spec k`, let `K ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`,
and suppose `RΓ(X, K)` and `RΓ(Y, M)` have no cohomology in negative degrees. Then

`H⁰RΓ(X, K) ⊗_A H⁰RΓ(Y, M) ⟶ H⁰RΓ(X ×_k Y, Lp^*K ⊗^𝐋 Lq^*M)`

is an isomorphism. The global Künneth morphism is invertible by the second conclusion of
[Stacks, Tag 0FLQ], and the cohomology product in degree zero by
`CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero`, applied over the field
`Γ(Spec k, 𝒪)`. -/
theorem isIso_degreeZeroKunnethMap (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hK₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase f.toLRSHom.toShHom).obj K)))
    (hM₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase g.toLRSHom.toShHom).obj M))) :
    IsIso (degreeZeroKunnethMap k f g K M) := by
  have hglob := Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme f g
    (torIndependent_over_field k f g) K M hK hM
  have hprod : IsIso (RingTheory.TorProducts.cohomologyTensorProduct
      ((sectionsOverBase f.toLRSHom.toShHom).obj K)
      ((sectionsOverBase g.toLRSHom.toShHom).obj M) 0 0).map := by
    let := gammaSectionsField k
    exact CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero _ _ hK₀ hM₀
  unfold degreeZeroKunnethMap
  infer_instance

/-! ### The degree-zero Künneth map over `k` -/

/-- `H⁰RΓ(V, N)` as a `k`-vector space: `degreeZeroSections` with scalars restricted along
`k ≅ Γ(Spec k, 𝒪)`. -/
abbrev degreeZeroSectionsField {V : Scheme.{u}} (c : V ⟶ Spec (.of k))
    (N : DerivedCategory V.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).obj (degreeZeroSections k c N)

/-- **The degree-zero Künneth isomorphism over `k`**, as a `k`-linear equivalence

`H⁰RΓ(X, K) ⊗_k H⁰RΓ(Y, M) ≃ H⁰RΓ(X ×_k Y, Lp^*K ⊗^𝐋 Lq^*M)`

under the hypotheses of `AlgebraicGeometry.isIso_degreeZeroKunnethMap`. It is
`AlgebraicGeometry.degreeZeroKunnethMap` read over `k`: base change from `⊗_k` to `⊗_A` along
the ring isomorphism `k ≅ A = Γ(Spec k, 𝒪)`, which is invertible by
`Stacks.ModuleCat.RingIsoTransport.isIso_baseChange`, followed by the `A`-linear map. Its value
at a pure tensor is `AlgebraicGeometry.degreeZeroKunnethLinearEquiv_tmul`. -/
def degreeZeroKunnethLinearEquiv (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hK₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase f.toLRSHom.toShHom).obj K)))
    (hM₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase g.toLRSHom.toShHom).obj M))) :
    (degreeZeroSectionsField k f K ⊗[k] degreeZeroSectionsField k g M) ≃ₗ[k]
      degreeZeroSectionsField k (Limits.pullback.fst f g ≫ f) (boxDerived k f g K M) :=
  haveI := isIso_degreeZeroKunnethMap k f g K M hK hM hK₀ hM₀
  (Stacks.ModuleCat.RingIsoTransport.baseChangeIso (gammaSectionsRingEquiv k).symm
      (degreeZeroSections k f K) (degreeZeroSections k g M) ≪≫
    (ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).mapIso
      (asIso (degreeZeroKunnethMap k f g K M))).toLinearEquiv

/-- **The degree-zero Künneth isomorphism at a pure tensor** is the degree-zero Künneth map at
the same pure tensor over `Γ(Spec k, 𝒪)`, which is the cohomology product `[x] ⊗ [y] ↦ [x ⊗ y]`
followed by `H⁰` of the global Künneth morphism. -/
theorem degreeZeroKunnethLinearEquiv_tmul (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hK₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase f.toLRSHom.toShHom).obj K)))
    (hM₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase g.toLRSHom.toShHom).obj M)))
    (x : degreeZeroSectionsField k f K) (y : degreeZeroSectionsField k g M) :
    degreeZeroKunnethLinearEquiv k f g K M hK hM hK₀ hM₀ (x ⊗ₜ[k] y) =
      (degreeZeroKunnethMap k f g K M).hom
        (x ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace] y) :=
  rfl

/-- **The degree-zero Künneth pairing**: the additive extension to formal integral combinations
of pairs of `(x, y) ↦ μ(x ⊗ y)`, where `μ` is `AlgebraicGeometry.degreeZeroKunnethMap`. -/
def degreeZeroKunnethPairing (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules) :
    FreeAbelianGroup (degreeZeroSectionsField k f K × degreeZeroSectionsField k g M) →+
      degreeZeroSectionsField k (Limits.pullback.fst f g ≫ f) (boxDerived k f g K M) :=
  FreeAbelianGroup.lift fun xy =>
    (degreeZeroKunnethMap k f g K M).hom
      (xy.1 ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace] xy.2)

/-- The degree-zero Künneth pairing sends the generator `(x, y)` to the degree-zero Künneth map
applied to `x ⊗ y`. -/
@[simp]
theorem degreeZeroKunnethPairing_of (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (xy : degreeZeroSectionsField k f K × degreeZeroSectionsField k g M) :
    degreeZeroKunnethPairing k f g K M (FreeAbelianGroup.of xy) =
      (degreeZeroKunnethMap k f g K M).hom
        (xy.1 ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace] xy.2) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The global Künneth formula over a field in degree zero, on elements.** Let `k` be a field,
let `X` and `Y` be quasi-compact and quasi-separated over `Spec k`, let `K ∈ D_QCoh(𝒪_X)` and
`M ∈ D_QCoh(𝒪_Y)`, and suppose `RΓ(X, K)` and `RΓ(Y, M)` have no cohomology in negative
degrees. Then the canonical pairing

`H⁰RΓ(X, K) × H⁰RΓ(Y, M) ⟶ H⁰RΓ(X ×_k Y, Lp^*K ⊗^𝐋 Lq^*M)`

— the cohomology product in degree zero followed by `H⁰` of the global Künneth morphism —
exhibits its target as `H⁰RΓ(X, K) ⊗_k H⁰RΓ(Y, M)`: every element of the target is an integral
combination of products, and a combination of products vanishes exactly when the
`k`-bilinearity relations force it to. -/
theorem isTensorPairing_degreeZeroKunnethPairing (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hK₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase f.toLRSHom.toShHom).obj K)))
    (hM₀ : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase g.toLRSHom.toShHom).obj M))) :
    IsTensorPairing k (degreeZeroSectionsField k f K) (degreeZeroSectionsField k g M)
      (degreeZeroKunnethPairing k f g K M) :=
  isTensorPairing_of_linearEquiv (degreeZeroKunnethLinearEquiv k f g K M hK hM hK₀ hM₀) _
    fun x y => degreeZeroKunnethPairing_of k f g K M (x, y)

end AlgebraicGeometry

end
