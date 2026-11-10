module

public import StacksFrontier.Deformation.Examples.Geometric.CompletionRankOneCoefficients
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationTowerInjective

/-!
# Localization of rank-one tensor coefficients

Let `k` be a field, `P` a `k`-algebra, `S ⊆ P` a multiplicative subset and `V` a
one-dimensional `k`-vector space, presented by a `k`-linear equivalence `ι : V ≃ₗ[k] k`.
**Stacks 0DZ8** is stated with coefficients `LocalizedModule S N` for a `P`-module `N`, whereas
the coefficients a first-order deformation over the base `k ⊕ V` produces are `P ⊗[k] V`
downstairs and `S⁻¹P ⊗[k] V` upstairs. At `N = P ⊗[k] V` the two differ by the canonical
`S⁻¹P`-linear equivalence

`LocalizedModule S (P ⊗[k] V) ≃ₗ[S⁻¹P] S⁻¹P ⊗[k] V`,

which is `Deformation.Examples.localizationRankOneEquiv`: both sides are canonically `S⁻¹P`
itself, since `V` has rank one. This file builds that equivalence and transports Stacks 0DZ8
along it, in the Ext form the tangent-space comparison of **Stacks 0GPV** consumes.

## Main definitions

* `Deformation.Examples.localizationCoefficientMap`: the `P`-linear coefficient map
  `P ⊗[k] V → S⁻¹P ⊗[k] V`, which on `p ⊗ v` is `(p/1) ⊗ v`. It is a localization of `P ⊗[k] V`
  at `S`.
* `Deformation.Examples.localizationRankOneEquiv`: the `S⁻¹P`-linear equivalence above.
* `Deformation.Examples.localizationExtOne`: **Stacks 0DZ8 in Ext form at rank-one
  coefficients**, the map `Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_{S⁻¹P}(NL_{S⁻¹P/k}, S⁻¹P ⊗[k] V)`
  obtained by conjugating the equivalence of Stacks 0DZ8 by the classification of **Stacks
  0GPT** and by the rank-one comparison.

## Main results

* `Deformation.Examples.bijective_localizationExtOne`: it is bijective.
* `Deformation.Examples.naiveCotangentExtOneMap_localizationCoefficientMap`: it is compatible
  with the two comparison maps of **Stacks 0GPV**, i.e. the restriction along `P → S⁻¹P` of the
  image of a class is the image of the class under the coefficient map
  `P ⊗[k] V → S⁻¹P ⊗[k] V`. This is the identity that makes it usable: the only handle Stacks
  0DZ8 offers on its equivalence is that it carries the class of an extension to the class of
  its localization, and **Stacks 0GPV** turns the localization map of middle rings into exactly
  this identity.

## Implementation notes

The hypothesis of Stacks 0DZ8 is recorded here in the source's own shape — `Spec(P) → Spec(k)`
is smooth at every point of `V(g)`, for every `g ∈ S` — and
`Deformation.Examples.disjoint_nonsmoothLocus_of_isSmoothAt_of_mem` converts it into the
disjointness form `squareZeroAlgebraExtensionClassesLocalizationEquiv` is stated with. The two
are contrapositives of each other: a prime meets `S` exactly when it lies in `V(g)` for some
`g ∈ S`.

## References

* [Stacks Project, Tag 0DZ8](https://stacks.math.columbia.edu/tag/0DZ8)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public noncomputable section

open Stacks.Deformation
open scoped TensorProduct

universe w

namespace Deformation.Examples

attribute [local implicit_reducible] Stacks.Deformation.algebraExtensionProblem

/-! ### The source's smoothness hypothesis -/

/-- **The two readings of the hypothesis of Stacks 0DZ8.** If `Spec(P) → Spec(k)` is smooth at
every point of `V(g)` for every `g` in a multiplicative subset `S`, then `S` is disjoint from
every prime at which `P` is not smooth over `k`. -/
public theorem disjoint_nonsmoothLocus_of_isSmoothAt_of_mem
    {k P : Type w} [Field k] [CommRing P] [Algebra k P] (S : Submonoid P)
    (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (q : PrimeSpectrum P) (hq : ¬ Algebra.IsSmoothAt k q.asIdeal) :
    Disjoint (S : Set P) (q.asIdeal : Set P) := by
  rw [Set.disjoint_left]
  intro g hgS hgq
  exact hq (hsm g hgS q hgq)

/-! ### The rank-one comparison -/

section RankOne

variable (k P : Type w) [Field k] [CommRing P] [Algebra k P] (S : Submonoid P)
  {V : Type w} [AddCommGroup V] [Module k V]

/-- **The coefficient map of the localization comparison at rank-one coefficients**: the
`P`-linear map `P ⊗[k] V → S⁻¹P ⊗[k] V` localizing the left tensor factor. -/
public def localizationCoefficientMap (ι : V ≃ₗ[k] k) :
    P ⊗[k] V →ₗ[P] Localization S ⊗[k] V :=
  ((tensorRankOneTrivialization k (Localization S) ι).symm.restrictScalars P
      : Localization S →ₗ[P] Localization S ⊗[k] V).comp
    ((Algebra.linearMap P (Localization S)).comp
      (tensorRankOneTrivialization k P ι).toLinearMap)

/-- The coefficient map localizes the left tensor factor. -/
public theorem localizationCoefficientMap_tmul (ι : V ≃ₗ[k] k) (p : P) (v : V) :
    localizationCoefficientMap k P S ι (p ⊗ₜ[k] v)
      = algebraMap P (Localization S) p ⊗ₜ[k] v := by
  change (algebraMap P (Localization S) (ι v • p)) ⊗ₜ[k] ι.symm 1 = _
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply k P (Localization S),
    ← Algebra.smul_def, TensorProduct.smul_tmul, ← map_smul ι.symm, smul_eq_mul, mul_one,
    ι.symm_apply_apply]

/-- The coefficient map is a localization of `P ⊗[k] V` at `S`: both trivialisations of the
rank-one tensor factor are isomorphisms, and `P → S⁻¹P` is one. -/
public instance isLocalizedModule_localizationCoefficientMap (ι : V ≃ₗ[k] k) :
    IsLocalizedModule S (localizationCoefficientMap k P S ι) := by
  have h₁ : IsLocalizedModule S
      ((Algebra.linearMap P (Localization S)).comp
        ((tensorRankOneTrivialization k P ι : P ⊗[k] V ≃ₗ[P] P) : P ⊗[k] V →ₗ[P] P)) :=
    IsLocalizedModule.of_linearEquiv_right S (Algebra.linearMap P (Localization S))
      (tensorRankOneTrivialization k P ι)
  exact IsLocalizedModule.of_linearEquiv S _
    ((tensorRankOneTrivialization k (Localization S) ι).symm.restrictScalars P)

/-- **Localization commutes with a rank-one tensor factor.** Both `S⁻¹(P ⊗[k] V)` and
`S⁻¹P ⊗[k] V` are canonically `S⁻¹P` itself, by
`Deformation.Examples.tensorRankOneTrivialization` below and above the localization, so they
are canonically `S⁻¹P`-linearly isomorphic. -/
public def localizationRankOneEquiv (ι : V ≃ₗ[k] k) :
    LocalizedModule S (P ⊗[k] V) ≃ₗ[Localization S] Localization S ⊗[k] V :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (P ⊗[k] V))
      (localizationCoefficientMap k P S ι))

/-- The rank-one comparison carries the canonical map into the localized module to the
coefficient map. -/
public theorem localizationRankOneEquiv_mk (ι : V ≃ₗ[k] k) (x : P ⊗[k] V) :
    localizationRankOneEquiv k P S ι (LocalizedModule.mkLinearMap S (P ⊗[k] V) x)
      = localizationCoefficientMap k P S ι x :=
  IsLocalizedModule.linearEquiv_apply S (LocalizedModule.mkLinearMap S (P ⊗[k] V))
    (localizationCoefficientMap k P S ι) x

/-- The coefficient map factors as the canonical map into the localized module followed by the
rank-one comparison. -/
public theorem restrictScalars_localizationRankOneEquiv_comp_mkLinearMap (ι : V ≃ₗ[k] k) :
    (((localizationRankOneEquiv k P S ι :
          LocalizedModule S (P ⊗[k] V) →ₗ[Localization S] Localization S ⊗[k] V).restrictScalars
        P).comp (LocalizedModule.mkLinearMap S (P ⊗[k] V)))
      = localizationCoefficientMap k P S ι :=
  LinearMap.ext fun x => localizationRankOneEquiv_mk k P S ι x

end RankOne

/-! ### Stacks 0DZ8 in Ext form at rank-one coefficients -/

section ExtOne

variable (k P : Type w) [Field k] [CommRing P] [Algebra k P] [Algebra.FiniteType k P]
  (S : Submonoid P) {V : Type w} [AddCommGroup V] [Module k V]

variable (hsm : ∀ g ∈ S, ∀ q : PrimeSpectrum P, g ∈ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)

include hsm

/-- **Stacks 0DZ8 in Ext form at rank-one coefficients.** The equivalence of Stacks 0DZ8 on
isomorphism classes of square-zero extensions, read through the classification of **Stacks
0GPT** on both sides and through the rank-one comparison of the coefficients, as a map
`Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_{S⁻¹P}(NL_{S⁻¹P/k}, S⁻¹P ⊗[k] V)`. -/
public def localizationExtOne (ι : V ≃ₗ[k] k) :
    naiveCotangentExtOne k P (P ⊗[k] V) →
      naiveCotangentExtOne k (Localization S) (Localization S ⊗[k] V) :=
  fun ξ =>
    naiveCotangentExtOneMap k (Localization S)
      ((localizationRankOneEquiv k P S ι :
        LocalizedModule S (P ⊗[k] V) →ₗ[Localization S] Localization S ⊗[k] V))
      (squareZeroAlgebraExtensionClassesEquivExtOne k (Localization S)
        (LocalizedModule S (P ⊗[k] V))
        (squareZeroAlgebraExtensionClassesLocalizationEquiv k P S
          (fun q hq => disjoint_nonsmoothLocus_of_isSmoothAt_of_mem S hsm q hq) (P ⊗[k] V)
          ((squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] V)).symm ξ)))

/-- **Stacks 0DZ8 in Ext form at rank-one coefficients is bijective.** -/
public theorem bijective_localizationExtOne (ι : V ≃ₗ[k] k) :
    Function.Bijective (localizationExtOne k P S hsm ι) := by
  have hmap : Function.Bijective (naiveCotangentExtOneMap k (Localization S)
      ((localizationRankOneEquiv k P S ι :
        LocalizedModule S (P ⊗[k] V) →ₗ[Localization S] Localization S ⊗[k] V))) :=
    bijective_naiveCotangentExtOneMap_of_inverse k (Localization S) _
      ((localizationRankOneEquiv k P S ι).symm :
        Localization S ⊗[k] V →ₗ[Localization S] LocalizedModule S (P ⊗[k] V))
      (fun m => (localizationRankOneEquiv k P S ι).symm_apply_apply m)
      (fun n => (localizationRankOneEquiv k P S ι).apply_symm_apply n)
  exact hmap.comp
    (((squareZeroAlgebraExtensionClassesEquivExtOne k (Localization S)
        (LocalizedModule S (P ⊗[k] V))).bijective.comp
      (squareZeroAlgebraExtensionClassesLocalizationEquiv k P S
        (fun q hq => disjoint_nonsmoothLocus_of_isSmoothAt_of_mem S hsm q hq)
        (P ⊗[k] V)).bijective).comp
      (squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] V)).symm.bijective)

/-- **Stacks 0DZ8 in Ext form is compatible with the comparison maps of Stacks 0GPV.** For a
class `ξ ∈ Ext¹_P(NL_{P/k}, P ⊗[k] V)`, the restriction along `P → S⁻¹P` of the image of `ξ`
under Stacks 0DZ8 is the image of `ξ` under the coefficient map `P ⊗[k] V → S⁻¹P ⊗[k] V`.

This is Stacks 0GPV applied to the localization map of middle rings: a square-zero extension
`X` of `P` by `P ⊗[k] V` and its localization `Y`, which is what Stacks 0DZ8 matches the class
of `X` with, do admit a `k`-algebra map of middle rings over `P → S⁻¹P` and over the
localization map of the coefficients, by definition of
`Deformation.Examples.IsLocalizedExtension`. -/
public theorem naiveCotangentExtOneMap_localizationCoefficientMap (ι : V ≃ₗ[k] k)
    (ξ : naiveCotangentExtOne k P (P ⊗[k] V)) :
    naiveCotangentExtOneMap k P (localizationCoefficientMap k P S ι) ξ
      = naiveCotangentExtOneTowerMap k P (Localization S)
          (localizationExtOne k P S hsm ι ξ) := by
  classical
  set hS : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal →
      Disjoint (S : Set P) (q.asIdeal : Set P) :=
    fun q hq => disjoint_nonsmoothLocus_of_isSmoothAt_of_mem S hsm q hq with hSdef
  obtain ⟨X, hX⟩ := Quotient.exists_rep
    ((squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] V)).symm ξ)
  have hXξ : squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] V) ⟦X⟧ = ξ := by
    rw [hX]
    exact (squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] V)).apply_symm_apply ξ
  obtain ⟨Y, hEY, hloc⟩ :=
    squareZeroAlgebraExtensionClassesLocalizationEquiv_apply k P S hS (P ⊗[k] V) X
  obtain ⟨f, -, hfB, hfN⟩ := hloc
  -- Stacks 0GPV for the localization map of middle rings
  have hgpv := (exists_compatible_algebraMap_iff k P (Localization S)
    (LocalizedModule.mkLinearMap S (P ⊗[k] V)) X Y).mp ⟨f, hfB, hfN⟩
  -- unwind the definition of the Ext-form equivalence
  have hval : localizationExtOne k P S hsm ι ξ
      = naiveCotangentExtOneMap k (Localization S)
        ((localizationRankOneEquiv k P S ι :
          LocalizedModule S (P ⊗[k] V) →ₗ[Localization S] Localization S ⊗[k] V))
        (squareZeroAlgebraExtensionClassesEquivExtOne k (Localization S)
          (LocalizedModule S (P ⊗[k] V)) ⟦Y⟧) := by
    rw [localizationExtOne, ← hX, hEY]
  rw [hval, naiveCotangentExtOneTowerMap_map, ← hgpv, hXξ,
    ← naiveCotangentExtOneMap_comp, restrictScalars_localizationRankOneEquiv_comp_mkLinearMap]

end ExtOne

end Deformation.Examples

end
