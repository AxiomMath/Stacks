module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.GlobalSectionsBijective
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Idempotents
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.NegativeTwist
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.SectionPower
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.SectionsVanishing
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic

/-!
# Connectedness of the zero scheme from vanishing in very negative twists

Let `X` be a connected scheme, `L` an invertible `𝒪_X`-module and `s` a regular global section
of `L`. If the negative twists `L^{⊗ m}` have no global sections and no first cohomology for all
sufficiently negative `m`, then the zero scheme `Z(s)` is connected.

This is the whole of the Enriques–Severi–Zariski connectedness theorem
[Stacks, Tag 0FD9] except for the two vanishing theorems it consumes, [Stacks, Tag 0FD7] and
[Stacks, Tag 0FD8]: no field, no properness and no depth condition appear here, because they
enter only through those two.

The argument, following the source. Choose `n ≥ 1` with `-n` below both vanishing bounds. Then
`s^n` is a regular section of `L^{⊗ n}`
(`Stacks.AmpleSectionConnected.isRegularSection_sectionPow'`) and `Z(s) ≃ₜ Z(s^n)`
(`Stacks.AmpleSectionConnected.zeroSchemeSectionPowHomeo`), so it suffices to connect `Z(s^n)`. The
canonical sequence

`0 ⟶ ℐ_{Z(s^n)} ⟶ 𝒪_X ⟶ 𝒪_{Z(s^n)} ⟶ 0`

is short exact (`Stacks.IdealSheafSequence.divisorIdeal_shortExact`) and its first term is
`L^{⊗ -n}` (`Stacks.AmpleSectionConnected.idealSheafIsoTensorPowerNeg`), so by hypothesis both
its `Γ(X, -)` and its `H¹(X, -)` vanish; the long exact cohomology sequence then makes
`Γ(X, 𝒪_X) → Γ(Z(s^n), 𝒪)` bijective
(`Stacks.AmpleSectionConnected.bijective_secF_map_g_of_isZero`), and a scheme whose global
functions are those of a connected scheme is connected
(`Stacks.AmpleSectionConnected.connectedSpace_of_bijective_appTop`).

## Main results

* `Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isZero_negative_twists`
* `Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_subsingleton_sections_of_iso`: the
  same, with the vanishing taken over any family of modules isomorphic to the tensor powers and
  the `H⁰` half in the `Subsingleton _.sections` shape.

## Implementation notes

The map `Γ(X, 𝒪_X) → Γ(Z, 𝒪_Z)` that the cohomology produces and the ring map `i.appTop` that the
idempotent argument consumes are the *same function* —
`Stacks.IdealSheafSequence.divisorQuotientMap` is `SheafOfModules.unitToPushforwardObjUnit` of the
structural morphism, whose component over an open is the component of that morphism — so the
transfer of bijectivity is `rfl` pointwise. This is the reason for taking the sequence in its
ideal-sheaf form rather than tensoring the sequence of [Stacks, Tag 0C6K] by `L^{⊗ -n}`: there the
middle term would be `L^{⊗ -n} ⊗ L^{⊗ n}` rather than `𝒪_X`, and the identification with `𝒪_X` is
only an isomorphism of modules, which carries no idempotents.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleSectionConnected

variable {X : Scheme.{u}}

/-- **The map on global functions induced by the ideal sequence of a closed subscheme is the
structural ring map.** Both are the component over `⊤` of `𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem secF_map_divisorQuotientMap_apply (D : X.IdealSheafData) (a : Γ(X, ⊤)) :
    ((secF X.ringCatSheaf ⊤).map (Stacks.IdealSheafSequence.divisorQuotientMap D)).hom a =
      (D.subschemeι.appTop).hom a := rfl

/-- **The zero scheme of a regular section of an invertible module is connected, given vanishing
in all sufficiently negative twists.** See the module documentation for the argument. -/
theorem connectedSpace_zeroScheme_of_isZero_negative_twists [ConnectedSpace X]
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (hs : Mono (L.unitHomEquiv.symm s))
    (h0 : ∃ a₀ : ℤ, ∀ m : ℤ, m ≤ a₀ →
      IsZero ((secF X.ringCatSheaf ⊤).obj (tensorPowerModule' L m)))
    (h1 : ∃ a₁ : ℤ, ∀ m : ℤ, m ≤ a₁ →
      IsZero (Hgroup X.ringCatSheaf ⊤ 1 (tensorPowerModule' L m))) :
    ConnectedSpace (zeroScheme X L (s.eval (op ⊤))).subscheme := by
  obtain ⟨a₀, ha₀⟩ := h0
  obtain ⟨a₁, ha₁⟩ := h1
  obtain ⟨n, hn, hn₀, hn₁⟩ : ∃ n : ℕ, n ≠ 0 ∧ -((1 * n : ℕ) : ℤ) ≤ a₀ ∧ -((1 * n : ℕ) : ℤ) ≤ a₁ :=
    ⟨(max 1 (max (-a₀) (-a₁))).toNat, by omega, by omega, by omega⟩
  set t := sectionPow' L (sectionsDegreeOne L (s.eval (op ⊤))) n with ht_def
  have ht : Mono ((tensorPowerModule' L ((1 * n : ℕ) : ℤ)).unitHomEquiv.symm t) :=
    isRegularSection_sectionPow' L s hs n
  set D : X.IdealSheafData :=
    zeroScheme X (tensorPowerModule' L ((1 * n : ℕ) : ℤ)) (t.eval (op ⊤)) with hD_def
  obtain ⟨hz, hSE⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact D
  have hiso := idealSheafIsoTensorPowerNeg L (1 * n) t ht
  have h0' : IsZero ((secF X.ringCatSheaf ⊤).obj
      (ShortComplex.mk (Stacks.IdealSheafSequence.divisorIdealMap D)
        (Stacks.IdealSheafSequence.divisorQuotientMap D) hz).X₁) :=
    (ha₀ _ hn₀).of_iso ((secF X.ringCatSheaf ⊤).mapIso hiso)
  have h1' : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (ShortComplex.mk (Stacks.IdealSheafSequence.divisorIdealMap D)
        (Stacks.IdealSheafSequence.divisorQuotientMap D) hz).X₁) :=
    (ha₁ _ hn₁).of_iso ((Hfunctor X.ringCatSheaf ⊤ 1).mapIso hiso)
  have hbij := bijective_secF_map_g_of_isZero X ⊤ hSE h0' h1'
  have hbij' : Function.Bijective (D.subschemeι.appTop).hom := hbij
  have hconn : ConnectedSpace D.subscheme :=
    connectedSpace_of_bijective_appTop D.subschemeι hbij'
  exact (zeroSchemeSectionPowHomeo L s n hn).connectedSpace_iff.mpr hconn

/-- **The same conclusion from vanishing stated for any family of modules isomorphic to the
tensor powers.** The library carries three constructions of the integer tensor powers of an
invertible module, and a vanishing theorem may be stated over any of them; this form takes the
family and the comparison isomorphisms, so that no transport is left to the caller. The
hypothesis on `H⁰` is in the `Subsingleton _.sections` shape that [Stacks, Tag 0FD7] concludes
with. -/
theorem connectedSpace_zeroScheme_of_subsingleton_sections_of_iso [ConnectedSpace X]
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (hs : Mono (L.unitHomEquiv.symm s))
    (pow : ℤ → X.Modules) (e : ∀ m : ℤ, pow m ≅ tensorPowerModule' L m)
    (h0 : ∃ a₀ : ℤ, ∀ m : ℤ, m ≤ a₀ → Subsingleton (pow m).sections)
    (h1 : ∃ a₁ : ℤ, ∀ m : ℤ, m ≤ a₁ → IsZero (Hgroup X.ringCatSheaf ⊤ 1 (pow m))) :
    ConnectedSpace (zeroScheme X L (s.eval (op ⊤))).subscheme := by
  obtain ⟨a₀, ha₀⟩ := h0
  obtain ⟨a₁, ha₁⟩ := h1
  exact connectedSpace_zeroScheme_of_isZero_negative_twists L s hs
    ⟨a₀, fun m hm => (isZero_secF_top_of_subsingleton_sections X (pow m) (ha₀ m hm)).of_iso
      (((secF X.ringCatSheaf ⊤).mapIso (e m)).symm)⟩
    ⟨a₁, fun m hm => (ha₁ m hm).of_iso (((Hfunctor X.ringCatSheaf ⊤ 1).mapIso (e m)).symm)⟩

end Stacks.AmpleSectionConnected

end
