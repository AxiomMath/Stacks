module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentStepEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.AssociatedNumericalType
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivity
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.FieldExtension
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport

/-!
# The genus formula on a regular proper model

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X` of `C`, with multiplicities `mᵢ`,
`κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and `gᵢ` the genus of `Cᵢ` over `κᵢ`. [Stacks, Tag 0CA3] asserts

`g_C = 1 + Σᵢ mᵢ([κᵢ : k](gᵢ - 1) - ½(Cᵢ · Cᵢ))`.

This file carries out the source's proof at the model's own data: the canonical multiplicities
of [Stacks, Tag 0C5Z], the intersection numbers `(Cᵢ · Cⱼ) = deg(𝒪_X(Cⱼ)|_{Cᵢ})`, the weights
`[κᵢ : k]` and the genera `gᵢ`.

## Main results

* `Stacks.Models.RegularProperModelSituation.cast_genus_eq_one_add_sum_specialFiberComponent` —
  **[Stacks, Tag 0CA3]**.
* `Stacks.Models.RegularProperModelSituation.eulerCharacteristic_C_eq_specialFiber` —
  `χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`, which is
  `RegularProperModelSituation.eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre`
  read on the special fibre `X_k` rather than on the closed subscheme of `X` it cuts out.
* `Stacks.Models.RegularProperModelSituation.eulerCharacteristic_specialFiberComponent_eq` —
  `χ(Cᵢ, 𝒪_{Cᵢ}) = [κᵢ : k](1 - gᵢ)`.
* `Stacks.Models.RegularProperModelSituation.two_mul_eulerCharacteristic_specialFiber_eq` —
  the chain of [Stacks, Tag 0CA2] from `∅` to `X_k`, collapsed by [Stacks, Tag 0C66]:
  `2χ(X_k, 𝒪_{X_k}) = 2Σᵢ mᵢχ(Cᵢ, 𝒪_{Cᵢ}) + Σᵢ mᵢ(Cᵢ · Cᵢ)`.
* `Stacks.Models.RegularProperModelSituation.cast_genus_eq_one_add_sum_of_eulerCharacteristic_eq`
  — the formula from `χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})` alone.

## The argument

The source chooses a chain `∅ = D₀ ⊂ D₁ ⊂ … ⊂ D_m = X_k` of effective Cartier divisors with
`D_{j+1} = D_j + C_{i_j}`. Here the chain is the induction on a coefficient family `c ≤ m`, the
divisor being `D_c = Σᵢ cᵢCᵢ` and `E c = χ(X_k, 𝒪_{D_c})`; the induction itself is
`Stacks.Models.two_mul_eq_sum_of_recursion_le_of_ker`.

## References

* [Stacks Project, Tag 0CA3](https://stacks.math.columbia.edu/tag/0CA3)
* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

attribute [instance] Stacks.Models.isProper_curveToFractionField

variable (S : RegularProperModelSituation.{u})

/-! ### The generic fibre -/

/-- The structure sheaf of the curve is coherent. -/
public instance isCoherent_unit_C : (SheafOfModules.unit S.C.ringCatSheaf).IsCoherent :=
  Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.K S.C_to_K

/-- The structure sheaf of the special fibre is coherent. -/
public instance isCoherent_unit_specialFiber :
    (SheafOfModules.unit S.specialFiber.ringCatSheaf).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent S.specialFiber

/-! ### The Euler characteristics of the two fibres -/

/-- The special fibre, read as the closed subscheme of `X` it cuts out, is mapped isomorphically
onto `X_k` by `Stacks.Models.RegularProperModelSituation.fibreSubschemeι`. -/
public theorem fibreSubschemeι_specialFiberIdeal :
    S.fibreSubschemeι S.specialFiberIdeal le_rfl = (asIso S.specialFiberι.toImage).inv :=
  (cancel_mono S.specialFiberι).1 <| (S.fibreSubschemeι_comp _ _).trans
    ((Iso.inv_comp_eq _).2 S.specialFiberι.toImage_imageι.symm).symm

/-- The map `Stacks.Models.RegularProperModelSituation.fibreSubschemeι` from the closed subscheme
of `X` cut out by the special fibre to `X_k` is an isomorphism. -/
public instance isIso_fibreSubschemeι_specialFiberIdeal :
    IsIso (S.fibreSubschemeι S.specialFiberIdeal le_rfl) := by
  rw [fibreSubschemeι_specialFiberIdeal]
  infer_instance

/-- The pushforward of the structure sheaf of a closed subscheme `E ⊇ X_k` of `X` has the same
Euler characteristic on `X_k` as the structure sheaf has on `E` itself. -/
private theorem eulerCharacteristic_pushforward_unit (E : S.X.IdealSheafData)
    (h : S.specialFiberIdeal ≤ E) [IsLocallyNoetherian E.subscheme] :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι E h)).obj
          (SheafOfModules.unit E.subscheme.ringCatSheaf)) =
      eulerCharacteristic S.k (S.fibreSubschemeι E h ≫ S.specialFiberToSpec)
        (SheafOfModules.unit E.subscheme.ringCatSheaf) :=
  eulerCharacteristic_pushforward_of_isClosedImmersion S.k (S.fibreSubschemeι _ h)
    S.specialFiberToSpec _ inferInstance inferInstance

/-- **`χ(X_k, ι_*𝒪_{X_k}) = χ(X_k, 𝒪_{X_k})`** for the special fibre `X_k ⊆ X` itself, read as a
closed subscheme of `X` and mapped to `X_k` by the isomorphism
`Stacks.Models.RegularProperModelSituation.fibreSubschemeι`. -/
theorem eulerCharacteristic_pushforward_specialFiberIdeal (E : S.X.IdealSheafData)
    (h : S.specialFiberIdeal ≤ E) (hE : E = S.specialFiberIdeal) :
    eulerCharacteristic S.k S.specialFiberToSpec
      ((Scheme.Modules.pushforward (S.fibreSubschemeι E h)).obj
        (SheafOfModules.unit E.subscheme.ringCatSheaf)) =
      eulerCharacteristic S.k S.specialFiberToSpec
        (SheafOfModules.unit S.specialFiber.ringCatSheaf) := by
  subst hE
  have : IsLocallyNoetherian S.specialFiberIdeal.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (S.fibreSubschemeι _ h)
  refine (S.eulerCharacteristic_pushforward_unit _ h).trans ?_
  exact eulerCharacteristic_eq_of_finrank_cohomologyOverField_eq S.k S.k _ _ _ _ fun n =>
    finrank_cohomologyOverField_unit_pushforward S.k (S.fibreSubschemeι _ h)
      S.specialFiberToSpec n

/-- **`χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`**: the Euler characteristic of the structure sheaf is the
same on the generic and on the special fibre of the regular proper model. This is
`RegularProperModelSituation.eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre`,
which takes the special fibre as the closed subscheme of `X` it cuts out, read on `X_k`. -/
@[sga "6 X 7.5" "special case"]
public theorem eulerCharacteristic_C_eq_specialFiber :
    eulerCharacteristic S.K S.C_to_K (SheafOfModules.unit S.C.ringCatSheaf) =
      eulerCharacteristic S.k S.specialFiberToSpec
        (SheafOfModules.unit S.specialFiber.ringCatSheaf) := by
  have : IsLocallyNoetherian S.specialFiberIdeal.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (S.fibreSubschemeι _ le_rfl)
  refine S.eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre.trans ?_
  refine (S.eulerCharacteristic_pushforward_unit _ le_rfl).symm.trans ?_
  exact S.eulerCharacteristic_pushforward_specialFiberIdeal _ le_rfl rfl

/-! ### The components of the special fibre -/

/-- **`χ(Cᵢ, 𝒪_{Cᵢ}) = [κᵢ : k](1 - gᵢ)`**, the sentence of the proof of [Stacks, Tag 0CA3]
following its citation of [Stacks, Tag 04L2]: `κᵢ` is a field finite over `k`, and `gᵢ` is the
genus of `Cᵢ` over `κᵢ`. -/
public theorem eulerCharacteristic_specialFiberComponent_eq
    (Z : irreducibleComponents S.specialFiber) :
    eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
        (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) =
      (S.specialFiberComponentWeight Z : ℤ) * (1 - (S.specialFiberComponentGenus Z : ℤ)) := by
  have h1 := eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus S.k
    (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
  have h2 := genus_eq_finrank_globalSections_mul_genus_toSpecΓ S.k
    (S.specialFiberComponentToSpec Z)
    (S.isField_and_finite_globalSections_specialFiberComponent Z).1
  refine h1.trans ?_
  rw [h2]
  unfold specialFiberComponentWeight specialFiberComponentGenus
  push_cast
  ring

/-! ### The divisors `D_c = Σᵢ cᵢCᵢ` below the special fibre -/

/-- A divisor `Σᵢ cᵢCᵢ` with `c ≤ m` lies in the special fibre `X_k = Σᵢ mᵢCᵢ`. -/
public theorem specialFiberIdeal_le_prod_of_le (c : irreducibleComponents S.specialFiber → ℕ)
    (hc : c ≤ S.specialFiberMultiplicity) :
    S.specialFiberIdeal ≤ ∏ Z, S.specialFiberComponentIdeal Z ^ c Z := by
  have h : ∏ Z, S.specialFiberComponentIdeal Z ^ S.specialFiberMultiplicity Z =
      (∏ Z, S.specialFiberComponentIdeal Z ^ c Z) *
        ∏ Z, S.specialFiberComponentIdeal Z ^ (S.specialFiberMultiplicity Z - c Z) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Z _ => by rw [← pow_add, Nat.add_sub_cancel' (hc Z)]
  rw [S.specialFiberIdeal_eq_prod, h]
  exact Scheme.IdealSheafData.mul_le_left _ _

/-- The coefficients of `Σᵢ cᵢCᵢ` along the components are the `cᵢ`. -/
public theorem specialFiberDivisorCoeff_prod (c : irreducibleComponents S.specialFiber → ℕ)
    (W : irreducibleComponents S.specialFiber) :
    S.specialFiberDivisorCoeff (∏ Z, S.specialFiberComponentIdeal Z ^ c Z) W = c W := by
  rw [RegularModelSituation.specialFiberDivisorCoeff,
    S.effectiveCartierMultiplicity_prod_specialFiberComponentIdeal_pow,
    ite_eq_left (Finset.mem_univ W)]
  simp

open scoped Classical in
/-- `χ(X_k, 𝒪_{D_c})` for the divisor `D_c = Σᵢ cᵢCᵢ`, when it lies in `X_k` (and `0` otherwise),
the structure sheaf of `D_c` being pushed forward to `X_k`. -/
def specialFiberDivisorEulerChar (c : irreducibleComponents S.specialFiber → ℕ) : ℤ :=
  if h : S.specialFiberIdeal ≤ ∏ Z, S.specialFiberComponentIdeal Z ^ c Z then
    eulerCharacteristic S.k S.specialFiberToSpec
      ((Scheme.Modules.pushforward (S.fibreSubschemeι _ h)).obj
        (SheafOfModules.unit (∏ Z, S.specialFiberComponentIdeal Z ^ c Z).subscheme.ringCatSheaf))
  else 0

/-- The empty divisor has Euler characteristic zero. -/
theorem eulerCharacteristic_pushforward_top (E : S.X.IdealSheafData) (h : S.specialFiberIdeal ≤ E)
    (hE : E = ⊤) :
    eulerCharacteristic S.k S.specialFiberToSpec
      ((Scheme.Modules.pushforward (S.fibreSubschemeι _ h)).obj
        (SheafOfModules.unit E.subscheme.ringCatSheaf)) = 0 := by
  subst hE
  have : IsLocallyNoetherian (⊤ : S.X.IdealSheafData).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (S.fibreSubschemeι _ h)
  rw [S.eulerCharacteristic_pushforward_unit _ h]
  exact eulerCharacteristic_eq_zero_of_isEmpty S.k _ _ _

/-- The divisor `D_0 = 0` has `χ(X_k, 𝒪_{D_0}) = 0`. -/
theorem specialFiberDivisorEulerChar_zero : S.specialFiberDivisorEulerChar 0 = 0 := by
  have hE : ∏ Z, S.specialFiberComponentIdeal Z ^ (0 : irreducibleComponents S.specialFiber → ℕ) Z
      = ⊤ := by
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
    exact Scheme.IdealSheafData.one_eq_top
  rw [specialFiberDivisorEulerChar, dite_eq_left (hE ▸ le_top)]
  exact S.eulerCharacteristic_pushforward_top _ _ hE

/-- The divisor `D_m = Σᵢ mᵢCᵢ` with the multiplicities `mᵢ` of the components of `X_k` has
`χ(X_k, 𝒪_{D_m}) = χ(X_k, 𝒪_{X_k})`. -/
theorem specialFiberDivisorEulerChar_multiplicity :
    S.specialFiberDivisorEulerChar S.specialFiberMultiplicity =
      eulerCharacteristic S.k S.specialFiberToSpec
        (SheafOfModules.unit S.specialFiber.ringCatSheaf) := by
  rw [specialFiberDivisorEulerChar, dite_eq_left (S.specialFiberIdeal_le_prod_of_le _ le_rfl)]
  exact S.eulerCharacteristic_pushforward_specialFiberIdeal _ _ S.specialFiberIdeal_eq_prod.symm

variable [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **The recursion of [Stacks, Tag 0CA2] along the divisors `D_c` below `X_k`**: adding a
component `C_Z` to `D_c` changes `χ(X_k, 𝒪_{D_c})` by `-(D_c · C_Z) + χ(C_Z, 𝒪_{C_Z})`. -/
theorem specialFiberDivisorEulerChar_add_single
    (c : irreducibleComponents S.specialFiber → ℕ) (Z : irreducibleComponents S.specialFiber)
    (hc : c + Pi.single Z 1 ≤ S.specialFiberMultiplicity) :
    S.specialFiberDivisorEulerChar (c + Pi.single Z 1) =
      S.specialFiberDivisorEulerChar c - (∑ Y, (c Y : ℤ) * S.specialFiberIntersectionMatrix Z Y) +
        eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) := by
  have hc' : c ≤ S.specialFiberMultiplicity := fun W =>
    (Nat.le_add_right _ _).trans (hc W)
  have hk := S.specialFiberIdeal_le_prod_of_le _ hc
  have hk' := S.specialFiberIdeal_le_prod_of_le _ hc'
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (∏ W, S.specialFiberComponentIdeal W ^ c W) :=
    Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ c
      fun W _ => S.isEffectiveCartierDivisor_specialFiberComponent W
  have hsum : ∏ W, S.specialFiberComponentIdeal W ^
        (c + Pi.single Z 1 : irreducibleComponents S.specialFiber → ℕ) W =
      (∏ W, S.specialFiberComponentIdeal W ^ c W) * S.specialFiberComponentIdeal Z := by
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single_of_mem Z (Finset.mem_univ Z)
      (fun W _ hW => by rw [Pi.single_eq_of_ne hW, pow_zero]), Pi.single_eq_same, pow_one]
  obtain ⟨h1, h2⟩ := S.eulerCharacteristic_addComponent Z _ _ hsum hk
  rw [S.intersectionProduct_single_right] at h2
  have hsymm : ∀ Y, (S.specialFiberDivisorCoeff (∏ W, S.specialFiberComponentIdeal W ^ c W) Y : ℤ) *
      S.specialFiberComponentDegree Y
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Z)) =
      (c Y : ℤ) * S.specialFiberIntersectionMatrix Z Y := fun Y => by
    rw [S.specialFiberDivisorCoeff_prod c Y]
    exact congrArg _ ((S.componentDegree_specialFiberComponent_comm Y Z).trans
      (S.specialFiberIntersectionMatrix_eq_componentDegree Z Y).symm)
  simp only [hsymm] at h2
  rw [specialFiberDivisorEulerChar, specialFiberDivisorEulerChar, dite_eq_left hk, dite_eq_left hk']
  linarith

/-! ### The genus formula -/

/-- **The chain of [Stacks, Tag 0CA2] from the empty divisor to the special fibre, collapsed**:
`2χ(X_k, 𝒪_{X_k}) = 2Σᵢ mᵢχ(Cᵢ, 𝒪_{Cᵢ}) + Σᵢ mᵢ(Cᵢ · Cᵢ)`, the off-diagonal part of the double
sum cancelling against the diagonal part by part (2) of [Stacks, Tag 0C66]. -/
public theorem two_mul_eulerCharacteristic_specialFiber_eq :
    2 * eulerCharacteristic S.k S.specialFiberToSpec
        (SheafOfModules.unit S.specialFiber.ringCatSheaf) =
      2 * (∑ Z, (S.specialFiberMultiplicity Z : ℤ) *
        eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf)) +
        ∑ Z, (S.specialFiberMultiplicity Z : ℤ) * S.specialFiberIntersectionMatrix Z Z := by
  rw [← S.specialFiberDivisorEulerChar_multiplicity]
  exact two_mul_eq_sum_of_recursion_le_of_ker _ (fun Z Y => S.specialFiberIntersectionMatrix Z Y)
    (fun Z Y => S.specialFiberIntersectionMatrix_comm Z Y) S.specialFiberMultiplicity
    S.specialFiberDivisorEulerChar S.specialFiberDivisorEulerChar_zero
    (fun c Z hc => S.specialFiberDivisorEulerChar_add_single c Z hc)
    (sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion S
      (fun W => S.specialFiberComponentIdeal W) (fun W => S.specialFiberComponentToSpec W)
      (fun W => S.isProper_specialFiberComponentToSpec W)
      (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W)
      S.specialFiberIntersectionMatrix S.specialFiberMultiplicity
      (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W)
      (fun c W => S.specialFiberDivisorDegree_eq_sum W c) S.specialFiberIdeal_eq_prod)

/-- **The genus formula of [Stacks, Tag 0CA3], from `χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`.** With
`mᵢ` the multiplicities of the components `Cᵢ` of the special fibre, `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})`,
`gᵢ` the genus of `Cᵢ` over `κᵢ` and `(Cᵢ · Cᵢ)` the self-intersection numbers,

`g_C = 1 + Σᵢ mᵢ([κᵢ : k](gᵢ - 1) - ½(Cᵢ · Cᵢ))`.

The hypothesis is the equality of the Euler characteristics of the structure sheaves of the
generic and the special fibre, which is
`Stacks.Models.RegularProperModelSituation.eulerCharacteristic_C_eq_specialFiber`. -/
public theorem cast_genus_eq_one_add_sum_of_eulerCharacteristic_eq
    (h : eulerCharacteristic S.K S.C_to_K (SheafOfModules.unit S.C.ringCatSheaf) =
      eulerCharacteristic S.k S.specialFiberToSpec
        (SheafOfModules.unit S.specialFiber.ringCatSheaf)) :
    (genus S.C_to_K : ℚ) = 1 + ∑ Z, (S.specialFiberMultiplicity Z : ℚ) *
      ((S.specialFiberComponentWeight Z : ℚ) * ((S.specialFiberComponentGenus Z : ℚ) - 1) -
        (S.specialFiberIntersectionMatrix Z Z : ℚ) / 2) := by
  have := cast_eq_one_add_sum S.specialFiberMultiplicity
    (fun Z Y => S.specialFiberIntersectionMatrix Z Y)
    (fun Z => eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
      (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf))
    (fun Z => (S.specialFiberComponentWeight Z : ℤ)) (fun Z => (S.specialFiberComponentGenus Z : ℤ))
    (genus S.C_to_K : ℤ) _ S.two_mul_eulerCharacteristic_specialFiber_eq
    ((one_sub_genus_curve_eq_eulerCharacteristic S).trans h)
    S.eulerCharacteristic_specialFiberComponent_eq
  push_cast at this
  exact this

/-- **Stacks Project, Tag 0CA3.** In the situation of [Stacks, Tag 0C61] — `R` a discrete
valuation ring with fraction field `K` and residue field `k`, `C` a smooth projective curve over
`K` with `H⁰(C, 𝒪_C) = K`, `X` a regular proper model of `C`, `C₁, …, Cₙ` the irreducible
components of the special fibre and `X_k = Σ mᵢCᵢ` as in [Stacks, Tag 0C5Z] —

`g_C = 1 + Σᵢ mᵢ([κᵢ : k](gᵢ - 1) - ½(Cᵢ · Cᵢ))`,

where `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})`, `gᵢ` is the genus of `Cᵢ` (over `κᵢ`), `g_C` is the genus of `C` and
`(Cᵢ · Cᵢ) = deg(𝒪_X(Cᵢ)|_{Cᵢ})` is the self-intersection number of [Stacks, Tag 0C64]. The
components are indexed by `irreducibleComponents X_k`, and the formula is stated over `ℚ`.

The proof is the source's: `1 - g_C = χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`, the chain of
[Stacks, Tag 0CA2] from the empty divisor to `X_k` collapsed by part (2) of
[Stacks, Tag 0C66], and `χ(Cᵢ, 𝒪_{Cᵢ}) = [κᵢ : k](1 - gᵢ)`. -/
@[stacks 0CA3 "g_C = 1 + Σ mᵢ([κᵢ : k](gᵢ - 1) - (Cᵢ · Cᵢ)/2) at the canonical data of the model"]
public theorem cast_genus_eq_one_add_sum_specialFiberComponent :
    (genus S.C_to_K : ℚ) = 1 + ∑ Z, (S.specialFiberMultiplicity Z : ℚ) *
      ((S.specialFiberComponentWeight Z : ℚ) * ((S.specialFiberComponentGenus Z : ℚ) - 1) -
        (S.specialFiberIntersectionMatrix Z Z : ℚ) / 2) :=
  S.cast_genus_eq_one_add_sum_of_eulerCharacteristic_eq S.eulerCharacteristic_C_eq_specialFiber

end RegularProperModelSituation

end Stacks.Models

end
