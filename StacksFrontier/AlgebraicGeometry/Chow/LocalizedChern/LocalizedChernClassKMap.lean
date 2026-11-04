module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedChernCharacterKMap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedChernKMap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyLocalized
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation

/-!
# The localized Chern class map on `K₀(D_{Z,perf}(𝒪_X))`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` with quasi-compact irreducible components (for instance `X` quasi-compact),
let `i : Z ⟶ X` be a closed immersion and let `D_{Z,perf}(𝒪_X)` be the perfect objects of
`D(𝒪_X)` whose cohomology sheaves are supported on `Z` (Remark 0FEP). Remark 0FES states that the
localized Chern classes define a canonical map

  `c(Z ⟶ X, -) : K₀(D_{Z,perf}(𝒪_X)) ⟶ A⁰(X) × ∏_{i ≥ 1} Aⁱ(Z ⟶ X)`,
  `[E] ↦ c(Z ⟶ X, E) = 1 + c₁(Z ⟶ X, E) + c₂(Z ⟶ X, E) + ⋯`,

extended multiplicatively, the product on the right being that of Remark 0FA0.

A supported perfect object `E` vanishes on `X ∖ Z`, so it restricts there to the zero module, a
finite locally free module of rank `0 < 1`; its Chern classes are defined since the irreducible
components of `X` are quasi-compact (Stacks 0GUE). Hence it has a total localized Chern class at
the cutoff `1` (Remark 0FBC), an element of the ring `A⁽¹⁾(Z ⟶ X)` of
`Stacks.Chow.instRingLocalizedGradingOne`. Its degree-`0` component is `c₀(E) = 1`, so it is a
unit. For a distinguished triangle `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` of `D_{Z,perf}(𝒪_X)`, Lemma 0FBD with
`p₁ = p₃ = 1` and output cutoff `1` (condition (b): the irreducible components of `X` are
quasi-compact) gives `c(Z ⟶ X, E₂) = c(Z ⟶ X, E₁) c(Z ⟶ X, E₃)`. So the classes extend
multiplicatively to `K₀(D_{Z,perf}(𝒪_X))`
(`CategoryTheory.Pretriangulated.K0.monoidHomOfMulTriangle`).

## Main definitions

* `Stacks.Chow.supportedTotalLocalizedChern` — `c(Z ⟶ X, E) ∈ A⁽¹⁾(Z ⟶ X)` for a supported perfect
  object `E`.
* `Stacks.Chow.localizedChernClassKMap` — the map `c(Z ⟶ X, -)` of Stacks 0FES.

## Main results

* `Stacks.Chow.homPart_zero_complexChern`, `Stacks.Chow.homPart_zero_perfectChernClass`,
  `Stacks.Chow.perfectChernClass_apply_zero` — `c₀ = 1` for a locally bounded complex of finite
  locally free modules and for an object whose Chern classes are defined.
* `Stacks.Chow.supportedTotalLocalizedChern_fst`, `Stacks.Chow.supportedTotalLocalizedChern_snd` —
  the components of `c(Z ⟶ X, E)`: `1` in degree `0`, `0` in the negative degrees and
  `cₙ(Z ⟶ X, E)` in the degrees `n ≥ 1`.
* `Stacks.Chow.isUnit_supportedTotalLocalizedChern` — `c(Z ⟶ X, E)` is a unit.
* `Stacks.Chow.supportedTotalLocalizedChern_triangle` — Stacks 0FBD for distinguished triangles of
  `D_{Z,perf}(𝒪_X)`.
* `Stacks.Chow.localizedChernClassKMap_cls`, `Stacks.Chow.localizedChernClassKMap_add` — the map
  sends `[E]` to `c(Z ⟶ X, E)` and sums to products.
* `Stacks.Chow.localizedChernClassKMap_unique` — it is the only such homomorphism.

## Implementation notes

The target is the ring `A⁽¹⁾(Z ⟶ X) = ∏_{n < 1} Aⁿ(X) × ∏_{n ≥ 1} Aⁿ(Z ⟶ X)` of Remark 0FA0,
which besides the source's factors `A⁰(X)` and `Aⁱ(Z ⟶ X)`, `i ≥ 1`, has the factors `Aⁿ(X)` of
the negative degrees `n`; the components of every `c(Z ⟶ X, E)` there vanish
(`Stacks.Chow.supportedTotalLocalizedChern_fst`). The source of the map is
`K₀(D_{Z,perf}(𝒪_X))` written multiplicatively.

## References

* [Stacks Project, Tag 0FES](https://stacks.math.columbia.edu/tag/0FES)
* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
* [Stacks Project, Tag 0FBC](https://stacks.math.columbia.edu/tag/0FBC)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect

universe u

namespace Stacks.Chow

open TotalChowClass

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The degree-`0` Chern class -/

section ChernZero

variable (C : ChowSituation.{u})

/-- **`c₀(𝓔^•) = 1`** for a locally bounded complex `𝓔^•` of finite locally free modules: on each
rank locus the class is `∏_n c(𝓔^n)^{(-1)^n}`, whose degree-`0` part is `1`. -/
theorem homPart_zero_complexChern {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    {P : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P) :
    TotalChowClass.homComponent 0 (complexChern C sY hP) = 1 := by
  refine eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ => ?_
  rw [map_one, TotalChowClass.res_homComponent, res_complexChern_complexRankLocus]
  exact (complexChernBounded_spec C ((complexRankLocus hP ρ.down).ι ≫ sY)
    (pullbackComplex (complexRankLocus hP ρ.down).ι P) ρ.down
    (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down)).choose_spec.1

/-- **`c₀(E) = 1`** for an object `E` of `D(𝒪_X)` whose Chern classes are defined: by Stacks 0GUD
it suffices to check this after restriction along the envelope of a presentation, where it is
`Stacks.Chow.homPart_zero_complexChern`. -/
theorem homPart_zero_perfectChernClass {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) :
    TotalChowClass.homComponent 0 (perfectChernClass C sX hE) = 1 := by
  obtain ⟨H⟩ := hE
  refine res_injective_of_isEnvelope H.f H.envelope rfl ?_
  rw [map_one, TotalChowClass.res_homComponent, res_perfectChernClass C sX ⟨H⟩ H]
  exact homPart_zero_complexChern C (H.f ≫ sX) H.locallyBounded

end ChernZero

/-! ### The total localized Chern class of a supported perfect object -/

section Class

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i]

/-- **A perfect object supported on `Z` is, on `X ∖ Z`, a finite locally free module of rank
`< 1` placed in degree `0`**: it is zero there, and the zero module has rank `0`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_one_of_supportedPerfect
    (E : supportedPerfectDerivedCategory i) :
    ∃ M : OXMod.{u, u, u} (X.toRingedSpace.restrict (⟨(Set.range i.base)ᶜ,
      i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M 1 ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (X.toRingedSpace.ofRestrict (⟨(Set.range i.base)ᶜ,
            i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
              X.Opens).isOpenEmbedding)).obj E.obj ≅
            (DerivedCategory.singleFunctor _ 0).obj M) :=
  exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _)
    (supportedPerfect_isZero_derivedPullback_compl i E) one_pos

/-- The data of a localized Chern class at the cutoff `1` for a supported perfect object `E`:
the closed immersion `i : Z ⟶ X`, the object `E`, and the cutoff `1`, `E|_{X ∖ Z}` being the zero
module, of rank `< 1`. -/
abbrev supportedPerfectDataOne (E : supportedPerfectDerivedCategory i) : LocalizedChernData.{u} :=
  (supportedPerfectData C a i E).withObject E.obj 1 E.property.1
    (exists_isFiniteLocallyFreeOfRankLT_one_of_supportedPerfect E)

variable (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **The localized Chern class `c(Z ⟶ X, E) = 1 + c₁(Z ⟶ X, E) + c₂(Z ⟶ X, E) + ⋯`** of a
supported perfect object `E ∈ D_{Z,perf}(𝒪_X)`, for `X` with quasi-compact irreducible components:
the total localized Chern class `c⁽¹⁾(Z ⟶ X, E) ∈ A⁽¹⁾(Z ⟶ X)` of Remark 0FBC at the cutoff `1`,
`E` vanishing on `X ∖ Z`. Its components are `1 ∈ A⁰(X)` in degree `0`
(`Stacks.Chow.supportedTotalLocalizedChern_fst`) and the localized Chern classes
`cₙ(Z ⟶ X, E) ∈ Aⁿ(Z ⟶ X)` in the degrees `n ≥ 1`
(`Stacks.Chow.supportedTotalLocalizedChern_snd`). -/
def supportedTotalLocalizedChern (E : supportedPerfectDerivedCategory i) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (i ≫ a) a i rfl 1 :=
  LocalizedChernData.totalLocalizedChern (D := supportedPerfectDataOne C a E)
    (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj E.property.1)
    ((supportedPerfectData C a i E).isFiniteLocallyFreeOfRankLTOnComplement_withObject
      (exists_isFiniteLocallyFreeOfRankLT_one_of_supportedPerfect E))

/-- The components of `c(Z ⟶ X, E)` below the cutoff `1` are those of `1`: the class `c₀(E) = 1`
in degree `0`, and zero in the negative degrees. -/
theorem supportedTotalLocalizedChern_fst (E : supportedPerfectDerivedCategory i) :
    (supportedTotalLocalizedChern C a hX E).1 =
      (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) (i ≫ a) a i rfl 1).1 := by
  have key : ∀ (c : TotalChowClass C a), c 0 = (1 : TotalChowClass C a) 0 →
      ∀ n : {n : ℤ // n < ((1 : ℕ) : ℤ)}, c.intComponent C a n.1 =
        (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) (i ≫ a) a i rfl 1).1 n := by
    rintro c hc ⟨n, hn⟩
    by_cases h0 : n = 0
    · subst h0
      rw [localizedGrading_one_fst_of_eq rfl, TotalChowClass.intComponent, dite_eq_left le_rfl]
      show bivariantClassDegreeCongr C _ a a (𝟙 X) (Category.id_comp a) _ (c 0) = _
      rw [hc, TotalChowClass.one_apply_zero, bivariantClassDegreeCongr_bivariantClassDegreeCongr]
    · rw [localizedGrading_one_fst_of_ne h0,
        TotalChowClass.intComponent_of_neg _ (show n < 0 by push_cast at hn; omega)]
  funext n
  rw [supportedTotalLocalizedChern, LocalizedChernData.totalLocalizedChern_fst]
  exact key _ (perfectChernClass_apply_zero C a _) n

/-- **`c(Z ⟶ X, E)` is a unit** of `A⁽¹⁾(Z ⟶ X)`, its degree-`0` component being `1`
(`Stacks.Chow.localizedGrading_isUnit_of_fst_zero`). -/
theorem isUnit_supportedTotalLocalizedChern (E : supportedPerfectDerivedCategory i) :
    IsUnit (supportedTotalLocalizedChern C a hX E) :=
  localizedGrading_isUnit_of_fst_zero (congrFun (supportedTotalLocalizedChern_fst C a hX E) _)

/-- The components of `c(Z ⟶ X, E)` in the degrees `n ≥ 1` are the localized Chern classes
`cₙ(Z ⟶ X, E)` of Remark 0GUK. -/
theorem supportedTotalLocalizedChern_snd (E : supportedPerfectDerivedCategory i)
    (n : {n : ℤ // ((1 : ℕ) : ℤ) ≤ n}) :
    (supportedTotalLocalizedChern C a hX E).2 n =
      LocalizedChernData.localizedChernOfLe (D := supportedPerfectDataOne C a E)
        (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj E.property.1)
        ((supportedPerfectData C a i E).isFiniteLocallyFreeOfRankLTOnComplement_withObject
          (exists_isFiniteLocallyFreeOfRankLT_one_of_supportedPerfect E)) n :=
  rfl

/-- **Stacks 0FBD for supported perfect objects.** For a distinguished triangle
`E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` of `D_{Z,perf}(𝒪_X)`, with `X` having quasi-compact irreducible
components, `c(Z ⟶ X, E₂) = c(Z ⟶ X, E₁) c(Z ⟶ X, E₃)` in the ring `A⁽¹⁾(Z ⟶ X)`: this is
`Stacks.Chow.LocalizedChernData.totalLocalizedChern_triangle_eq_cutoffMul` with `p₁ = p₃ = 1` and
output cutoff `1`, under condition (b). -/
theorem supportedTotalLocalizedChern_triangle (T : Triangle (supportedPerfectDerivedCategory i))
    (hT : T ∈ distTriang (supportedPerfectDerivedCategory i)) :
    supportedTotalLocalizedChern C a hX T.obj₂ =
      supportedTotalLocalizedChern C a hX T.obj₁ * supportedTotalLocalizedChern C a hX T.obj₃ := by
  rw [localizedGrading_mul_def]
  exact (supportedPerfectData C a i T.obj₁).totalLocalizedChern_triangle_eq_cutoffMul
    T.obj₁.property.1 T.obj₂.property.1 T.obj₃.property.1 (p₁ := 1) (p₃ := 1) (r := 1) le_rfl
    _ _ _ hT (exists_isFiniteLocallyFreeOfRankLT_one_of_supportedPerfect T.obj₁)
    (exists_isFiniteLocallyFreeOfRankLT_one_of_supportedPerfect T.obj₃)
    (Or.inr (Or.inr (Or.inl hX)))

end Class

/-! ### Stacks 0FES -/

section KMap

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i] (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **Stacks 0FES: the localized Chern class map**
`c(Z ⟶ X, -) : K₀(D_{Z,perf}(𝒪_X)) ⟶ A⁰(X) × ∏_{i ≥ 1} Aⁱ(Z ⟶ X)`, for `X` locally of finite type
over `S` with quasi-compact irreducible components (for instance `X` quasi-compact) and a closed
immersion `i : Z ⟶ X`: the homomorphism from `K₀(D_{Z,perf}(𝒪_X))`, written multiplicatively, to
the ring `A⁽¹⁾(Z ⟶ X)` with the product of Remark 0FA0, sending `[E]` to
`c(Z ⟶ X, E) = 1 + c₁(Z ⟶ X, E) + c₂(Z ⟶ X, E) + ⋯`
(`Stacks.Chow.localizedChernClassKMap_cls`), extended multiplicatively
(`Stacks.Chow.localizedChernClassKMap_add`). It is well defined by Lemma 0FBD
(`Stacks.Chow.supportedTotalLocalizedChern_triangle`). -/
@[stacks 0FES]
def localizedChernClassKMap :
    Multiplicative (K0 (supportedPerfectDerivedCategory i)) →*
      localizedBivariantGrading C (gysinSystemOfInvertible C) (i ≫ a) a i rfl 1 :=
  K0.monoidHomOfMulTriangle (supportedTotalLocalizedChern_triangle C a hX)
    (isUnit_supportedTotalLocalizedChern C a hX)

/-- **Stacks 0FES, the value on a generator**: `c(Z ⟶ X, [E]) = c(Z ⟶ X, E)`. -/
@[stacks 0FES "the value `c(Z → X, E) = 1 + c_1(Z → X, E) + ⋯` on a generator `[E]`"]
theorem localizedChernClassKMap_cls (E : supportedPerfectDerivedCategory i) :
    localizedChernClassKMap C a hX (Multiplicative.ofAdd (K0.cls E)) =
      supportedTotalLocalizedChern C a hX E :=
  K0.monoidHomOfMulTriangle_cls _ _ E

/-- **Stacks 0FES, multiplicativity**: `c(Z ⟶ X, α + β) = c(Z ⟶ X, α) c(Z ⟶ X, β)` in
`A⁽¹⁾(Z ⟶ X)`. -/
@[stacks 0FES "the map is extended multiplicatively: `c(Z → X, α + β) = c(Z → X, α) c(Z → X, β)`"]
theorem localizedChernClassKMap_add (α β : K0 (supportedPerfectDerivedCategory i)) :
    localizedChernClassKMap C a hX (Multiplicative.ofAdd (α + β)) =
      localizedChernClassKMap C a hX (Multiplicative.ofAdd α) *
        localizedChernClassKMap C a hX (Multiplicative.ofAdd β) :=
  K0.monoidHomOfMulTriangle_add _ _ α β

/-- **Uniqueness**: `Stacks.Chow.localizedChernClassKMap` is the only homomorphism from
`K₀(D_{Z,perf}(𝒪_X))`, written multiplicatively, with `[E] ↦ c(Z ⟶ X, E)`. -/
theorem localizedChernClassKMap_unique
    (φ : Multiplicative (K0 (supportedPerfectDerivedCategory i)) →*
      localizedBivariantGrading C (gysinSystemOfInvertible C) (i ≫ a) a i rfl 1)
    (hφ : ∀ E, φ (Multiplicative.ofAdd (K0.cls E)) = supportedTotalLocalizedChern C a hX E) :
    φ = localizedChernClassKMap C a hX :=
  K0.monoidHom_ext fun E ↦ by rw [hφ, localizedChernClassKMap_cls]

end KMap

end Stacks.Chow

end
