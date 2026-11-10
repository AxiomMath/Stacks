module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormula
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.CategoryTheory.Abelian.ShortExactReflectFaithful
import StacksCore.Tactic.StacksAttribute

/-!
# The genus of the curve and the genus of the reduced special fibre

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve `C` over the fraction
field of a discrete valuation ring, and write the special fibre as a sum of effective Cartier
divisors `X_k = Σ mᵢCᵢ`.  Put `d = gcd(m₁, …, mₙ)`, let `D = Σ (mᵢ/d)Cᵢ` be the reduced special
fibre and let `κ = H⁰(D, 𝒪_D)`.  [Stacks, Tag 0C69] relates the genus of `C` to the genus of `D`
over `κ`:

`1 - g_C = d · [κ : k] · (1 - g_D)`.

The source's proof runs `1 - g_C = χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k}) = d·χ(D, 𝒪_D) = d[κ:k](1 - g_D)`.
The two outer identities are the comparison of the genus with the Euler characteristic of the
structure sheaf, in
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/EulerCharacteristicComparison.lean`; the middle
one, `χ(X_k, 𝒪_{X_k}) = d·χ(D, 𝒪_D)`, is the claim proved here by the source's induction.

## Main results

* `Stacks.Models.eulerCharacteristic_add_of_shortExact_pushforward` — additivity of the Euler
  characteristic over the residue field along a short exact sequence of `𝒪_X`-modules each of
  which is pushed forward from a closed subscheme of the special fibre.  This transports the
  sequence of [Stacks, Tag 0C4T] from `X`, which lies over `R`, to the special fibre, which lies
  over `k`.
* `Stacks.Models.eulerCharacteristic_pullback_negativeTwist_pow_eq` —
  `χ(D, 𝒪_X(-rD)|_D) = χ(D, 𝒪_D)`: the restriction is invertible of degree zero on `D`.
* `Stacks.Models.fibreEuler_specialFiberIdeal_eq` — `χ(X_k, 𝒪_{X_k}) = d·χ(D, 𝒪_D)`.
* `Stacks.Models.fibreEuler_reducedSpecialFibre_eq` — `χ(D, 𝒪_D) = [κ : k](1 - g_D)`.
* `Stacks.Models.one_sub_genus_curve_eq_eulerCharacteristic` — `1 - g_C = χ(C, 𝒪_C)`.
* `Stacks.Models.one_sub_genus_eq_gcd_mul_finrank_mul_one_sub_genus_reducedSpecialFibre` —
  the formula of [Stacks, Tag 0C69].
* `Stacks.Models.one_sub_genus_eq_gcd_mul_finrank_mul_one_sub_genus_specialFiberComponents` —
  the same at the irreducible components of the special fibre.

## Implementation notes

**Relative to a decomposition.**  As in
`StacksFrontier/AlgebraicGeometry/Curves/Models/ReducedSpecialFibre.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/Models/ReducedFibreFiltration.lean`, the components and
their multiplicities are not constructed here: a finite index set `s`, a family `C` of effective
Cartier divisors and multiplicities `m` with `X_k = ∏ i ∈ s, C i ^ m i` enter as hypotheses,
which is the phrase "write `X_k = Σ mᵢCᵢ`" opening Situation [Stacks, Tag 0C61].  The binder list
is that of `Stacks.Models.exists_chain_reducedSpecialFibre`, whose conclusion at its top stage is
what makes `κ` a field finite over the residue field.  The canonical family of irreducible
components satisfies every one of those binders except the identification of `(X_k)_red` with
`Σ Cᵢ`, and the specialization along it is the last theorem of the file.

**Beware the notation.**  On `AlgebraicGeometry.Scheme.IdealSheafData` the sum of divisors is the
product `*` and the `n`-fold sum `nD` is the power `^`, so `Σ aᵢCᵢ` is written
`∏ i ∈ s, C i ^ a i`; inclusion of closed subschemes is the reverse order on ideal sheaf data, so
`rD ⊆ X_k` reads `S.specialFiberIdeal ≤ D ^ r`.

**`D` is the reduced special fibre of the decomposition**, `Stacks.Models.reducedSpecialFibre`,
and `κ` is its ring of global functions with the residue-field algebra structure induced by the
canonical `D ⟶ Spec(k)` of
`Stacks.Models.RegularProperModelSituation.fibreSubschemeToSpec`.  Neither is re-defined here,
and the algebra structure is written `((Scheme.ΓSpecIso (.of S.k)).inv ≫ _.appTop).hom.toAlgebra`
— which is `Stacks.Models.RegularProperModelSituation.fibreSubschemeResidueMap` unfolded, and the
spelling that `rw` crosses.

**The degree of `𝒪_X(D)` on a subscheme of the special fibre.**  `d` times it is the degree of
`𝒪_X(dD) = 𝒪_X(X_k)`, which is trivial by
`Stacks.Models.invertibleSheafIso_specialFiberIdeal`, so it vanishes; the degree of `𝒪_X(-rD)` is
then `-r` times zero by the invertible case of [Stacks, Tag 0AYX], which
`Stacks.Models.componentDegreeAdditive` supplies with no hypothesis.

## References

* [Stacks Project, Tag 0C69](https://stacks.math.columbia.edu/tag/0C69)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C67](https://stacks.math.columbia.edu/tag/0C67)
* [Stacks Project, Tag 0C68](https://stacks.math.columbia.edu/tag/0C68)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Artin-Winters, Lemma 2.6]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Divisors

universe u

namespace Stacks.Models

section Decomposition

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ)

/-- The special fibre contains every sum `Σ (mᵢ/d)Cᵢ` of its components with smaller
multiplicities: the reduced fibre is a closed subscheme of the special fibre. -/
theorem specialFiberIdeal_le_reducedSpecialFibre
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    S.specialFiberIdeal ≤ reducedSpecialFibre s C m :=
  hdec.trans_le (AlgebraicGeometry.Scheme.IdealSheafData.prod_pow_le_prod_pow_of_le s C
    fun _ _ => Nat.div_le_self _ _)

/-- A closed subscheme of the special fibre has dimension at most one: the special fibre of a
regular proper model is one-dimensional, and the subscheme is closed in it. -/
theorem topologicalKrullDim_fibreSubscheme_le (Z : S.X.IdealSheafData)
    (h : S.specialFiberIdeal ≤ Z) :
    topologicalKrullDim Z.subscheme ≤ (1 : WithBot ℕ∞) := by
  have hle : topologicalKrullDim Z.subscheme ≤ topologicalKrullDim S.specialFiber :=
    (S.fibreSubschemeι Z h).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  rwa [S.toRegularModelSituation.topologicalKrullDim_specialFiber S.nonempty_specialFiber] at hle

/-- The Euler characteristic over the residue field of the structure sheaf of a closed subscheme
of the special fibre. -/
@[ega "III 2.5.1" "special case"]
abbrev fibreEuler (Z : S.X.IdealSheafData) (h : S.specialFiberIdeal ≤ Z) : ℤ :=
  @eulerCharacteristic S.k _ Z.subscheme (S.fibreSubschemeToSpec Z h) _
    (SheafOfModules.unit Z.subscheme.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k (S.fibreSubschemeToSpec Z h))

/-- The greatest common divisor of the multiplicities of a nonempty family of positive
multiplicities is positive. -/
theorem gcd_multiplicity_pos (hm : ∀ i ∈ s, 0 < m i) (hsne : s.Nonempty) : 0 < s.gcd m := by
  rcases Nat.eq_zero_or_pos (s.gcd m) with h0 | h0
  · obtain ⟨i, hi⟩ := hsne
    have h1 := Finset.gcd_eq_zero_iff.mp h0 i hi
    have h2 := hm i hi
    omega
  · exact h0

/-- The index set of a decomposition of the special fibre is nonempty: the reduction of the
special fibre is connected, hence nonempty, so it is not the empty divisor. -/
theorem nonempty_of_radical_eq_prod
    (hred : S.specialFiberIdeal.radical = ∏ i ∈ s, C i) : s.Nonempty := by
  rcases Finset.eq_empty_or_nonempty s with rfl | h
  · exfalso
    have htop : S.specialFiberIdeal.radical = (⊤ : S.X.IdealSheafData) := by
      rw [hred, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    have := S.connectedSpace_subscheme_radical_specialFiberIdeal
    have hne : Nonempty S.specialFiberIdeal.radical.subscheme := inferInstance
    rw [htop] at hne
    exact (inferInstance : IsEmpty (⊤ : S.X.IdealSheafData).subscheme).false hne.some
  · exact h

/-- The `d`-th power of the reduced special fibre is the special fibre, `d = gcd(mᵢ)`. -/
private theorem reducedSpecialFibre_pow_gcd_eq
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    reducedSpecialFibre s C m ^ s.gcd m = S.specialFiberIdeal :=
  (reducedSpecialFibre_pow_gcd s C m).trans hdec.symm

/-- The special fibre contains every multiple `rD` of the reduced special fibre with `r ≤ d`. -/
theorem specialFiberIdeal_le_reducedSpecialFibre_pow
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) (r : ℕ) (hr : r ≤ s.gcd m) :
    S.specialFiberIdeal ≤ reducedSpecialFibre s C m ^ r := by
  have hEq := reducedSpecialFibre_pow_gcd_eq S s C m hdec
  rw [← hEq, ← Nat.add_sub_cancel' hr, pow_add]
  exact Scheme.IdealSheafData.mul_le_left _ _

/-- The Euler characteristic of the structure sheaf of a closed subscheme of the special fibre
depends only on the subscheme. -/
theorem fibreEuler_congr {Z Z' : S.X.IdealSheafData} (h : Z = Z')
    (hZ : S.specialFiberIdeal ≤ Z) (hZ' : S.specialFiberIdeal ≤ Z') :
    fibreEuler S Z hZ = fibreEuler S Z' hZ' := by subst h; rfl

/-! ### The generic fibre -/

/-- **The generic fibre of a regular proper model is proper over the fraction field.**  The curve
is projective over `K` by the standing hypothesis of [Stacks, Tag 0C61], and an H-projective
morphism is proper. -/
theorem isProper_curveToFractionField : IsProper S.C_to_K :=
  AlgebraicGeometry.isProper_of_isProjectiveMorphism S.C_to_K S.curveProjective

/-- **The global functions of the generic fibre are the fraction field**, so they are
one-dimensional over it: `H⁰(C, 𝒪_C) = K` is part of Situation [Stacks, Tag 0C61]. -/
theorem finrank_globalSections_curve_eq_one :
    letI : Algebra S.K Γ(S.C, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.K)).inv ≫ S.C_to_K.appTop).hom.toAlgebra
    Module.finrank S.K Γ(S.C, ⊤) = 1 := by
  let : Algebra S.K Γ(S.C, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.K)).inv ≫ S.C_to_K.appTop).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap S.K Γ(S.C, ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective
      ((Scheme.ΓSpecIso (.of S.K)).inv ≫ S.C_to_K.appTop)).mp S.isIso_globalSections
  have e : S.K ≃ₗ[S.K] Γ(S.C, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap S.K Γ(S.C, ⊤)) hbij
  rw [← e.finrank_eq, Module.finrank_self]

/-- **`1 - g_C = χ(C, 𝒪_C)`** for the generic fibre of a regular proper model: the curve is
proper of dimension one over `K` and its global functions are `K` itself, so the alternating sum
`h⁰ - h¹` is `1 - g_C`. -/
theorem one_sub_genus_curve_eq_eulerCharacteristic :
    (1 : ℤ) - (AlgebraicGeometry.genus S.C_to_K : ℤ) =
      @eulerCharacteristic S.K _ _ S.C_to_K (isProper_curveToFractionField S)
        (SheafOfModules.unit S.C.ringCatSheaf)
        (@Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.K _ _ S.C_to_K
          (isProper_curveToFractionField S)) := by
  have := isProper_curveToFractionField S
  have hdim : topologicalKrullDim S.C ≤ (1 : WithBot ℕ∞) :=
    le_of_eq (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := S.C_to_K))
  exact AlgebraicGeometry.one_sub_genus_eq_eulerCharacteristic_unit S.K S.C_to_K hdim
    (finrank_globalSections_curve_eq_one S)

/-! ### Additivity of the Euler characteristic along the special fibre -/

/-- Pushing a module on a closed subscheme `Z ⊆ X` containing the special fibre forward to the
special fibre and then into `X` is pushing it forward along `Z ↪ X`. -/
private def fibrePushforwardIso (Z : S.X.IdealSheafData)
    (h : S.specialFiberIdeal ≤ Z) (G : Z.subscheme.Modules) :
    (Scheme.Modules.pushforward S.specialFiberι).obj
        ((Scheme.Modules.pushforward (S.fibreSubschemeι Z h)).obj G) ≅
      (Scheme.Modules.pushforward Z.subschemeι).obj G :=
  (Scheme.Modules.pushforwardComp (S.fibreSubschemeι Z h) S.specialFiberι).app G ≪≫
    (Scheme.Modules.pushforwardCongr (S.fibreSubschemeι_comp Z h)).app G

/-- **Additivity of the Euler characteristic over the residue field along a short exact sequence
of `𝒪_X`-modules each of which is pushed forward from a closed subscheme of the special
fibre.** -/
theorem eulerCharacteristic_add_of_shortExact_pushforward
    {Z₁ Z₂ Z₃ : S.X.IdealSheafData}
    (h₁ : S.specialFiberIdeal ≤ Z₁) (h₂ : S.specialFiberIdeal ≤ Z₂)
    (h₃ : S.specialFiberIdeal ≤ Z₃)
    {G₁ : Z₁.subscheme.Modules} {G₂ : Z₂.subscheme.Modules} {G₃ : Z₃.subscheme.Modules}
    {T : ShortComplex S.X.Modules} (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (Scheme.Modules.pushforward Z₁.subschemeι).obj G₁)
    (e₂ : T.X₂ ≅ (Scheme.Modules.pushforward Z₂.subschemeι).obj G₂)
    (e₃ : T.X₃ ≅ (Scheme.Modules.pushforward Z₃.subschemeι).obj G₃)
    (hc₁ : G₁.IsCoherent) (hc₂ : G₂.IsCoherent) (hc₃ : G₃.IsCoherent) :
    @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec Z₂ h₂) _ G₂ hc₂ =
      @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec Z₁ h₁) _ G₁ hc₁ +
        @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec Z₃ h₃) _ G₃ hc₃ := by
  have : IsLocallyNoetherian S.specialFiber :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field
      S.k S.specialFiberToSpec
  have hcoh : ∀ {Z : S.X.IdealSheafData} (h : S.specialFiberIdeal ≤ Z) (G : Z.subscheme.Modules),
      G.IsCoherent → ((Scheme.Modules.pushforward (S.fibreSubschemeι Z h)).obj G).IsCoherent :=
    fun _ G hG => have := hG; AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion _ G
  -- Step 1: each term of `T` is the direct image along `p` of a module on the special fibre.
  have u₁ := e₁ ≪≫ (fibrePushforwardIso S Z₁ h₁ G₁).symm
  have u₂ := e₂ ≪≫ (fibrePushforwardIso S Z₂ h₂ G₂).symm
  have u₃ := e₃ ≪≫ (fibrePushforwardIso S Z₃ h₃ G₃).symm
  -- Step 2: the two maps of `T` descend to the special fibre, by full faithfulness of `p_*`.
  have hff := Stacks.ClosedImmersion.fullyFaithfulPushforward S.specialFiberι
  have : (Scheme.Modules.pushforward S.specialFiberι).Faithful := hff.faithful
  set v := hff.preimage (u₁.inv ≫ T.f ≫ u₂.hom)
  set w := hff.preimage (u₂.inv ≫ T.g ≫ u₃.hom)
  have hmapv : (Scheme.Modules.pushforward S.specialFiberι).map v =
      u₁.inv ≫ T.f ≫ u₂.hom := hff.map_preimage _
  have hmapw : (Scheme.Modules.pushforward S.specialFiberι).map w =
      u₂.inv ≫ T.g ≫ u₃.hom := hff.map_preimage _
  have hvw : v ≫ w = 0 := by
    apply hff.map_injective
    rw [Functor.map_comp, Functor.map_zero, hmapv, hmapw]
    simp
  -- the descended complex is short exact.
  have hTW : (ShortComplex.mk v w hvw).ShortExact := by
    refine ShortComplex.shortExact_of_shortExact_map
      (Scheme.Modules.pushforward S.specialFiberι) ?_
    refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk u₁ u₂ u₃ ?_ ?_) hT
    · change u₁.hom ≫ (Scheme.Modules.pushforward S.specialFiberι).map v = T.f ≫ u₂.hom
      rw [hmapv]
      simp
    · change u₂.hom ≫ (Scheme.Modules.pushforward S.specialFiberι).map w = T.g ≫ u₃.hom
      rw [hmapw]
      simp
  -- Step 3: move each Euler characteristic back onto the subscheme it came from.
  have s : ∀ {Z : S.X.IdealSheafData} (h : S.specialFiberIdeal ≤ Z) (G : Z.subscheme.Modules)
      (hG : G.IsCoherent), @eulerCharacteristic S.k _ _ S.specialFiberToSpec _
        ((Scheme.Modules.pushforward (S.fibreSubschemeι Z h)).obj G) (hcoh h G hG) =
      @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec Z h) _ G hG :=
    fun h G hG => AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion S.k
      (S.fibreSubschemeι _ h) S.specialFiberToSpec G hG (hcoh h G hG)
  -- Step 4: additivity on the special fibre, which is proper over the residue field.
  rw [← s h₁ G₁ hc₁, ← s h₂ G₂ hc₂, ← s h₃ G₃ hc₃]
  have := hcoh h₁ G₁ hc₁
  have := hcoh h₂ G₂ hc₂
  have := hcoh h₃ G₃ hc₃
  exact AlgebraicGeometry.eulerCharacteristic_add_of_shortExact S.k S.specialFiberToSpec hTW


/-- **The degree of `𝒪_X(D)` on a closed subscheme of the special fibre vanishes**, `D` being
the reduced special fibre `Σ (mᵢ/d)Cᵢ`: `d` times that degree is the degree of `𝒪_X(X_k)`, whose
invertible sheaf is trivial because the special fibre is cut out by a uniformizer. -/
theorem componentDegree_invertibleSheaf_reducedSpecialFibre_eq_zero
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i) (hsne : s.Nonempty)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (Z : S.X.IdealSheafData) (h : S.specialFiberIdeal ≤ Z) :
    componentDegree S.k Z (S.fibreSubschemeToSpec Z h) (S.isProper_fibreSubschemeToSpec Z h)
        (topologicalKrullDim_fibreSubscheme_le S Z h)
        (invertibleSheaf' (reducedSpecialFibre s C m))
        (@isTensorInvertible_invertibleSheaf _ _
          (isEffectiveCartierDivisor_reducedSpecialFibre s C m hC)) = 0 := by
  have : IsEffectiveCartierDivisor (reducedSpecialFibre s C m) :=
    isEffectiveCartierDivisor_reducedSpecialFibre s C m hC
  have hd : 0 < s.gcd m := gcd_multiplicity_pos s m hm hsne
  have hEq := reducedSpecialFibre_pow_gcd_eq S s C m hdec
  have hpow := componentDegree_invertibleSheaf_pow S (fun _ : Unit => Z)
    (fun _ => S.fibreSubschemeToSpec Z h) (fun _ => S.isProper_fibreSubschemeToSpec Z h)
    (fun _ => topologicalKrullDim_fibreSubscheme_le S Z h) ()
    (reducedSpecialFibre s C m) (s.gcd m)
    (isTensorInvertible_invertibleSheaf _) (isTensorInvertible_invertibleSheaf _)
  rw [componentDegree_invertibleSheaf_congr S (fun _ : Unit => Z)
      (fun _ => S.fibreSubschemeToSpec Z h) (fun _ => S.isProper_fibreSubschemeToSpec Z h)
      (fun _ => topologicalKrullDim_fibreSubscheme_le S Z h) () hEq
      (isTensorInvertible_invertibleSheaf _) (isTensorInvertible_invertibleSheaf _),
    componentDegree_eq_of_iso S.k Z (S.fibreSubschemeToSpec Z h)
      (S.isProper_fibreSubschemeToSpec Z h) (topologicalKrullDim_fibreSubscheme_le S Z h)
      _ (SheafOfModules.unit S.X.ringCatSheaf) (isTensorInvertible_invertibleSheaf _)
      (isTensorInvertible_unit S.X) (invertibleSheafIso_specialFiberIdeal S),
    componentDegree_unit_eq_zero S.k Z (S.fibreSubschemeToSpec Z h)
      (S.isProper_fibreSubschemeToSpec Z h) (topologicalKrullDim_fibreSubscheme_le S Z h)
      (isTensorInvertible_unit S.X)] at hpow
  have hd' : ((s.gcd m : ℕ) : ℤ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hpow.symm).resolve_left hd'

/-- **The restriction `𝒪_X(-rD)|_D` of the ideal sheaf of `rD` to the reduced special fibre `D`
has the same Euler characteristic as `𝒪_D`.** It is an invertible module whose degree on `D` is
`-r` times the degree of `𝒪_X(D)` on `D`, and that degree is zero; the degree of an invertible
module is the difference of the two Euler characteristics by definition. -/
theorem eulerCharacteristic_pullback_negativeTwist_pow_eq
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i) (hsne : s.Nonempty)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) (r : ℕ)
    (hcoh : ((Scheme.Modules.pullback (reducedSpecialFibre s C m).subschemeι).obj
      (negativeTwist (reducedSpecialFibre s C m ^ r))).IsCoherent) :
    @eulerCharacteristic S.k _ _
        (S.fibreSubschemeToSpec (reducedSpecialFibre s C m)
          (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)) _
        ((Scheme.Modules.pullback (reducedSpecialFibre s C m).subschemeι).obj
          (negativeTwist (reducedSpecialFibre s C m ^ r))) hcoh =
      fibreEuler S (reducedSpecialFibre s C m)
        (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec) := by
  have hE : IsEffectiveCartierDivisor (reducedSpecialFibre s C m) :=
    isEffectiveCartierDivisor_reducedSpecialFibre s C m hC
  have hEr : IsEffectiveCartierDivisor (reducedSpecialFibre s C m ^ r) :=
    isEffectiveCartierDivisor_pow hE r
  set hsfi := specialFiberIdeal_le_reducedSpecialFibre S s C m hdec with hsfidef
  set Z := reducedSpecialFibre s C m with hZdef
  set gZ := S.fibreSubschemeToSpec Z hsfi with hgZdef
  have hgp : IsProper gZ := S.isProper_fibreSubschemeToSpec Z hsfi
  have hdimZ : topologicalKrullDim Z.subscheme ≤ (1 : WithBot ℕ∞) :=
    topologicalKrullDim_fibreSubscheme_le S Z hsfi
  -- the degree of `𝒪_X(-rD)` on `D` is minus `r` times the degree of `𝒪_X(D)`, hence zero
  have hneg := componentDegree_negativeTwist_eq_neg S (fun _ : Unit => Z) (fun _ => gZ)
    (fun _ => hgp) (fun _ => hdimZ) () (Z ^ r) hEr
  have hpow := componentDegree_invertibleSheaf_pow S (fun _ : Unit => Z) (fun _ => gZ)
    (fun _ => hgp) (fun _ => hdimZ) () Z r
    (isTensorInvertible_invertibleSheaf _) (isTensorInvertible_invertibleSheaf _)
  have hzero := componentDegree_invertibleSheaf_reducedSpecialFibre_eq_zero S s C m hC hm hsne
    hdec Z hsfi
  have hdeg : componentDegree S.k Z gZ hgp hdimZ (negativeTwist' (Z ^ r))
      (isTensorInvertible_negativeTwist _) = 0 := by
    rw [hneg, hpow, hzero, mul_zero, neg_zero]
  have hsub := componentDegree_eq_eulerCharacteristic_restrict_sub S.k Z gZ hgp hdimZ
    (negativeTwist' (Z ^ r)) (isTensorInvertible_negativeTwist _) hcoh
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k gZ)
  rw [hdeg] at hsub
  have := sub_eq_zero.mp hsub.symm
  exact this

/-- **`χ(D, 𝒪_D) = [κ : k](1 - g_D)`** for the reduced special fibre `D`, with
`κ = H⁰(D, 𝒪_D)` and `g_D` the genus of `D` over `κ`: the Euler characteristic of the structure
sheaf is `dim_k κ - g_{D/k}` and the genus over `k` is `[κ : k]` times the genus over `κ`. -/
theorem fibreEuler_reducedSpecialFibre_eq
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hκ : IsField Γ((reducedSpecialFibre s C m).subscheme, ⊤)) :
    letI : Algebra S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec (reducedSpecialFibre s C m)
        (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)).appTop).hom.toAlgebra
    letI : Field Γ((reducedSpecialFibre s C m).subscheme, ⊤) := hκ.toField
    fibreEuler S (reducedSpecialFibre s C m)
        (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec) =
      (Module.finrank S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) : ℤ) *
        (1 - (AlgebraicGeometry.genus
          (reducedSpecialFibre s C m).subscheme.toSpecΓ : ℤ)) := by
  have hC1 := AlgebraicGeometry.eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus
    S.k (S.fibreSubschemeToSpec (reducedSpecialFibre s C m)
      (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec))
    (topologicalKrullDim_fibreSubscheme_le S (reducedSpecialFibre s C m)
      (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec))
  have hC2 := AlgebraicGeometry.genus_eq_finrank_globalSections_mul_genus_toSpecΓ
    S.k (S.fibreSubschemeToSpec (reducedSpecialFibre s C m)
      (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)) hκ
  rw [hC2] at hC1
  refine hC1.trans ?_
  push_cast
  ring

/-- The global functions of the reduced special fibre form a field, finite over the residue
field for the canonical residue-field algebra structure: this is the top stage of the chain of
[Stacks, Tag 0C68]. -/
theorem isField_and_moduleFinite_globalSections_reducedSpecialFibre
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hred : S.specialFiberIdeal.radical = ∏ i ∈ s, C i)
    (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k)) (hgproper : ∀ i, IsProper (g i))
    (hdimC : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme) :
    ∃ _ : IsField Γ((reducedSpecialFibre s C m).subscheme, ⊤),
      letI : Algebra S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec
          (reducedSpecialFibre s C m)
          (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)).appTop).hom.toAlgebra
      Module.Finite S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) := by
  obtain ⟨M, Z, _, hZM, _, hprops⟩ :=
    exists_chain_reducedSpecialFibre S s C m hC hm hdec hred g hgproper hdimC hint
  have hM := hprops M le_rfl
  rw [hZM] at hM
  obtain ⟨_, hfield, φ, hφcomp, hφfin⟩ := hM
  refine ⟨hfield, ?_⟩
  have hφ : φ = S.fibreSubschemeResidueMap (reducedSpecialFibre s C m)
      (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec) := by
    refine RingHom.ext fun c => ?_
    obtain ⟨r, rfl⟩ := S.surjective_algebraMap c
    have h1 := RingHom.congr_fun hφcomp r
    have h2 := RingHom.congr_fun (S.fibreSubschemeResidueMap_comp (reducedSpecialFibre s C m)
      (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)) r
    exact h1.trans h2.symm
  subst hφ
  exact hφfin

/-- **`χ((r+1)D, 𝒪) = χ(rD, 𝒪) + χ(D, 𝒪_D)`.** The short exact sequence
`0 ⟶ 𝒪_X(-rD)|_D ⟶ 𝒪_{(r+1)D} ⟶ 𝒪_{rD} ⟶ 0` of [Stacks, Tag 0C4T], additivity of the Euler
characteristic along it, and the vanishing of the degree of the twist. -/
theorem fibreEuler_reducedSpecialFibre_pow_succ
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i) (hsne : s.Nonempty)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) (r : ℕ)
    (h₁ : S.specialFiberIdeal ≤ reducedSpecialFibre s C m ^ (r + 1))
    (h₂ : S.specialFiberIdeal ≤ reducedSpecialFibre s C m ^ r) :
    fibreEuler S (reducedSpecialFibre s C m ^ (r + 1)) h₁ =
      fibreEuler S (reducedSpecialFibre s C m ^ r) h₂ +
        fibreEuler S (reducedSpecialFibre s C m)
          (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec) := by
  have hE : IsEffectiveCartierDivisor (reducedSpecialFibre s C m) :=
    isEffectiveCartierDivisor_reducedSpecialFibre s C m hC
  have hEr : IsEffectiveCartierDivisor (reducedSpecialFibre s C m ^ r) :=
    isEffectiveCartierDivisor_pow hE r
  have hsfi := specialFiberIdeal_le_reducedSpecialFibre S s C m hdec
  have hsum : reducedSpecialFibre s C m ^ (r + 1) =
      reducedSpecialFibre s C m ^ r * reducedSpecialFibre s C m := pow_succ _ r
  have hsub : reducedSpecialFibre s C m ^ (r + 1) ≤ reducedSpecialFibre s C m ^ r :=
    hsum ▸ Scheme.IdealSheafData.mul_le_left _ _
  obtain ⟨f, hz, hex⟩ := addEffectiveCartierDivisor_shortExact
    (reducedSpecialFibre s C m ^ r) (reducedSpecialFibre s C m ^ (r + 1))
    (reducedSpecialFibre s C m) hEr hsub hsum
  -- the twist is an invertible, hence coherent, module on `D`
  have : IsLocallyNoetherian (reducedSpecialFibre s C m).subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field
      S.k (S.fibreSubschemeToSpec (reducedSpecialFibre s C m) hsfi)
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (reducedSpecialFibre s C m).subscheme.presheaf
      (reducedSpecialFibre s C m).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (reducedSpecialFibre s C m).subschemeι).obj
        (negativeTwist (reducedSpecialFibre s C m ^ r))) :=
    isInvertible_restrict (reducedSpecialFibre s C m) (negativeTwist' _)
      (isTensorInvertible_negativeTwist _)
  have hctw : ((Scheme.Modules.pullback (reducedSpecialFibre s C m).subschemeι).obj
      (negativeTwist (reducedSpecialFibre s C m ^ r))).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k
      (S.fibreSubschemeToSpec (reducedSpecialFibre s C m) hsfi) _ 1
  have key := eulerCharacteristic_add_of_shortExact_pushforward S hsfi h₁ h₂
    (T := ShortComplex.mk f (Scheme.IdealSheafData.closedSubschemeRestriction hsub) hz)
    hex (Iso.refl _) (Iso.refl _) (Iso.refl _) hctw
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
      (S.fibreSubschemeToSpec (reducedSpecialFibre s C m ^ (r + 1)) h₁))
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
      (S.fibreSubschemeToSpec (reducedSpecialFibre s C m ^ r) h₂))
  rw [eulerCharacteristic_pullback_negativeTwist_pow_eq S s C m hC hm hsne hdec r hctw] at key
  exact key.trans (add_comm _ _)

/-- **`χ(rD, 𝒪_{rD}) = r · χ(D, 𝒪_D)` for `1 ≤ r ≤ d`**, by induction on `r` from the one-step
identity `hsucc`: this is the induction of the source's proof of [Stacks, Tag 0C69]. -/
theorem fibreEuler_reducedSpecialFibre_pow
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hsucc : ∀ (r : ℕ) (h₁ : S.specialFiberIdeal ≤ reducedSpecialFibre s C m ^ (r + 1))
        (h₂ : S.specialFiberIdeal ≤ reducedSpecialFibre s C m ^ r), 1 ≤ r → r + 1 ≤ s.gcd m →
      fibreEuler S (reducedSpecialFibre s C m ^ (r + 1)) h₁ =
        fibreEuler S (reducedSpecialFibre s C m ^ r) h₂ +
          fibreEuler S (reducedSpecialFibre s C m)
            (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec))
    (r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ s.gcd m)
    (h : S.specialFiberIdeal ≤ reducedSpecialFibre s C m ^ r) :
    fibreEuler S (reducedSpecialFibre s C m ^ r) h =
      (r : ℤ) * fibreEuler S (reducedSpecialFibre s C m)
        (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec) := by
  induction r with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [fibreEuler_congr S (pow_one (reducedSpecialFibre s C m)) h
        (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)]
      simp
    · rw [hsucc n h (specialFiberIdeal_le_reducedSpecialFibre_pow S s C m hdec n (by omega))
        hn hrd, ih hn (by omega)
        (specialFiberIdeal_le_reducedSpecialFibre_pow S s C m hdec n (by omega))]
      push_cast
      ring

/-- **`χ(X_k, 𝒪_{X_k}) = d · χ(D, 𝒪_D)`**, the claim of the source's proof of
[Stacks, Tag 0C69]: the special fibre is `dD`, and the Euler characteristic of `rD` grows by
`χ(D, 𝒪_D)` at each of the `d` steps. -/
theorem fibreEuler_specialFiberIdeal_eq
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i) (hsne : s.Nonempty)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    fibreEuler S S.specialFiberIdeal le_rfl =
      ((s.gcd m : ℕ) : ℤ) * fibreEuler S (reducedSpecialFibre s C m)
        (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec) := by
  have hEq := reducedSpecialFibre_pow_gcd_eq S s C m hdec
  rw [← fibreEuler_congr S hEq
    (specialFiberIdeal_le_reducedSpecialFibre_pow S s C m hdec _ le_rfl) le_rfl]
  exact fibreEuler_reducedSpecialFibre_pow S s C m hdec
    (fun r h₁ h₂ _ _ => fibreEuler_reducedSpecialFibre_pow_succ S s C m hC hm hsne hdec r h₁ h₂)
    (s.gcd m) (gcd_multiplicity_pos s m hm hsne) le_rfl _

/-- **The formula of [Stacks, Tag 0C69]** [Artin-Winters, Lemma 2.6].  In Situation
[Stacks, Tag 0C61], written at a decomposition `X_k = Σ mᵢCᵢ` of the special fibre into integral
proper curves over the residue field, with `d = gcd(mᵢ)`, `D = Σ (mᵢ/d)Cᵢ` the reduced special
fibre and `κ = H⁰(D, 𝒪_D)`:

`1 - g_C = d · [κ : k] · (1 - g_D)`,

where `g_C` is the genus of `C` over `K` and `g_D` the genus of `D` over `κ`.  That `κ` is a
field, finite over `k`, is part of the conclusion rather than a hypothesis: it is the top stage
of the chain of [Stacks, Tag 0C68].

The binder list is exactly that of `Stacks.Models.exists_chain_reducedSpecialFibre`, whose
conclusion at its top stage is what makes `κ` a field finite over `k`.  The source's proof is
the composite of four identities, each of them a theorem here:
`1 - g_C = χ(C, 𝒪_C)` is `Stacks.Models.one_sub_genus_curve_eq_eulerCharacteristic`;
`χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})` is
`RegularProperModelSituation.eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre`;
`χ(X_k, 𝒪_{X_k}) = d·χ(D, 𝒪_D)` is `Stacks.Models.fibreEuler_specialFiberIdeal_eq`; and
`χ(D, 𝒪_D) = [κ : k](1 - g_D)` is `Stacks.Models.fibreEuler_reducedSpecialFibre_eq`. -/
@[stacks 0C69 "the formula 1 - g_C = d [kappa:k](1 - g_D) at a decomposition X_k = sum m_i C_i \
of the special fibre into integral proper curves over the residue field whose product is the \
reduced special fibre, of which the irreducible components of Situation 0C61 are the case: \
d = gcd(m_i), D = sum (m_i/d)C_i, kappa = H^0(D, O_D), and g_D the genus of D over kappa. That \
kappa is a field finite over the residue field is part of the conclusion"]
theorem one_sub_genus_eq_gcd_mul_finrank_mul_one_sub_genus_reducedSpecialFibre
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hm : ∀ i ∈ s, 0 < m i)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i)
    (hred : S.specialFiberIdeal.radical = ∏ i ∈ s, C i)
    (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k)) (hgproper : ∀ i, IsProper (g i))
    (hdimC : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)
    (hint : ∀ i, AlgebraicGeometry.IsIntegral (C i).subscheme) :
    ∃ hκ : IsField Γ((reducedSpecialFibre s C m).subscheme, ⊤),
      letI : Algebra S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec
          (reducedSpecialFibre s C m)
          (specialFiberIdeal_le_reducedSpecialFibre S s C m hdec)).appTop).hom.toAlgebra
      letI : Field Γ((reducedSpecialFibre s C m).subscheme, ⊤) := hκ.toField
      Module.Finite S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) ∧
        (1 : ℤ) - (AlgebraicGeometry.genus S.C_to_K : ℤ) =
          ((s.gcd m : ℕ) : ℤ) *
            (Module.finrank S.k Γ((reducedSpecialFibre s C m).subscheme, ⊤) : ℤ) *
            (1 - (AlgebraicGeometry.genus
              (reducedSpecialFibre s C m).subscheme.toSpecΓ : ℤ)) := by
  obtain ⟨hκ, hfin⟩ := isField_and_moduleFinite_globalSections_reducedSpecialFibre S s C m
    hC hm hdec hred g hgproper hdimC hint
  have := isProper_curveToFractionField S
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.K S.C_to_K
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
    (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
  -- the Euler characteristic comparison, with its right-hand side read at `fibreEuler`, which `rw`
  -- needs
  have hchifibre : eulerCharacteristic S.K S.C_to_K (SheafOfModules.unit S.C.ringCatSheaf) =
      fibreEuler S S.specialFiberIdeal le_rfl :=
    S.eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre
  refine ⟨hκ, hfin, ?_⟩
  rw [(one_sub_genus_curve_eq_eulerCharacteristic S).trans hchifibre,
    fibreEuler_specialFiberIdeal_eq S s C m hC hm
      (nonempty_of_radical_eq_prod S s C hred) hdec,
    fibreEuler_reducedSpecialFibre_eq S s C m hdec hκ, mul_assoc]

/-! ### At the irreducible components of the special fibre -/

/-- **Stacks Project, Tag 0C69** [Artin-Winters, Lemma 2.6], at the irreducible components of
the special fibre, which is the setting of Situation [Stacks, Tag 0C61].  With `C₁, …, Cₙ` the
irreducible components of `X_k`, `mᵢ` their multiplicities, `d = gcd(mᵢ)`, `D = Σ (mᵢ/d)Cᵢ` and
`κ = H⁰(D, 𝒪_D)`:

`1 - g_C = d · [κ : k] · (1 - g_D)`.

Every binder of the general statement is discharged at the canonical family: the components are
integral effective Cartier divisors, proper of dimension at most one over the residue field with
positive multiplicities, `X_k = Σ mᵢCᵢ` is part (3) of [Stacks, Tag 0C5Z], and the reduction
`(X_k)_red = Σ Cᵢ` is
`Stacks.Models.RegularModelSituation.radical_specialFiberIdeal_eq_prod`. -/
@[stacks 0C69 "the formula 1 - g_C = d [kappa:k](1 - g_D) at the irreducible components of the \
special fibre, which is the setting of Situation 0C61: d = gcd(m_i) for m_i the multiplicity of \
C_i in X_k, D = sum (m_i/d)C_i the reduced special fibre, kappa = H^0(D, O_D), and g_D the genus \
of D over kappa. That kappa is a field finite over the residue field is part of the conclusion"]
theorem one_sub_genus_eq_gcd_mul_finrank_mul_one_sub_genus_specialFiberComponents :
    ∃ hκ : IsField Γ((reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
        S.specialFiberMultiplicity).subscheme, ⊤),
      letI : Algebra S.k Γ((reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
          S.specialFiberMultiplicity).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec
          (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
            S.specialFiberMultiplicity)
          (specialFiberIdeal_le_reducedSpecialFibre S Finset.univ
            S.specialFiberComponentIdeal S.specialFiberMultiplicity
            S.specialFiberIdeal_eq_prod)).appTop).hom.toAlgebra
      letI : Field Γ((reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
        S.specialFiberMultiplicity).subscheme, ⊤) := hκ.toField
      Module.Finite S.k Γ((reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
        S.specialFiberMultiplicity).subscheme, ⊤) ∧
        (1 : ℤ) - (AlgebraicGeometry.genus S.C_to_K : ℤ) =
          ((Finset.univ.gcd S.specialFiberMultiplicity : ℕ) : ℤ) *
            (Module.finrank S.k Γ((reducedSpecialFibre Finset.univ
              S.specialFiberComponentIdeal S.specialFiberMultiplicity).subscheme, ⊤) : ℤ) *
            (1 - (AlgebraicGeometry.genus (reducedSpecialFibre Finset.univ
              S.specialFiberComponentIdeal S.specialFiberMultiplicity).subscheme.toSpecΓ : ℤ)) :=
  one_sub_genus_eq_gcd_mul_finrank_mul_one_sub_genus_reducedSpecialFibre S Finset.univ
    S.specialFiberComponentIdeal S.specialFiberMultiplicity
    (fun Z _ => S.isEffectiveCartierDivisor_specialFiberComponent Z)
    (fun Z _ => S.specialFiberMultiplicity_pos Z)
    S.specialFiberIdeal_eq_prod S.radical_specialFiberIdeal_eq_prod
    (fun Z => S.specialFiberComponentToSpec Z)
    (fun Z => S.isProper_specialFiberComponentToSpec Z)
    (fun Z => S.topologicalKrullDim_specialFiberComponent Z)
    (fun Z => S.isIntegral_specialFiberComponentIdeal Z)

end Decomposition

end Stacks.Models

end
