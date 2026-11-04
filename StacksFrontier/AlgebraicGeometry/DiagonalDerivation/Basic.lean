module

public import StacksFrontier.AlgebraicGeometry.DiagonalConormal.Retraction

/-!
# The derivation axioms for `p₂^♯ b - p₁^♯ b`, before any quotient is taken

[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) builds the comparison
`Ω_{X/S} ≅ C_Δ` out of the section `p₂^♯ b - p₁^♯ b` of the ideal sheaf of the diagonal. This
file proves additivity, the Leibniz rule, vanishing on sections pulled back from `S` and
compatibility with restriction for that section **as exact identities in the ring
`Γ(↑Δ.coborderRange, V)`**, before passing to the conormal sheaf or to any quotient by the
square of the ideal.

The Leibniz identity `delta_mul` is exact,

  `δ(b b') = p₂^♯ b · δ(b') + p₁^♯ b' · δ(b)`,

because `p_j^♯` are ring homomorphisms. Both `p₁^♯ b` and `p₂^♯ b` are lifts of `b` along the
structure map of the closed factorization of the diagonal (`app_liftFst`, `app_liftSnd`).
Replacing one by the other changes the right-hand side by exactly `δ(b) · δ(b')`
(`delta_mul_sub_leibniz`), and that product lies in the square of the ideal
(`delta_mul_delta_mem_sq`).

The first section is about an arbitrary morphism `g : Z ⟶ P` with two retractions; in the second
the two retractions are the two projections of `X ×_S X`.

## Main definitions

* `Stacks.DiagonalDerivation.delta`: for `g : Z ⟶ P` with two retractions `r₁, r₂`, the
  difference `r₂^♯ b - r₁^♯ b` of the two maps they induce on sections.
* `Stacks.DiagonalDerivation.liftFst` and `Stacks.DiagonalDerivation.liftSnd`: `p₁^♯ b` and
  `p₂^♯ b` as sections of `𝒪_{Δ.coborderRange}` over `V`. `liftFst_eq` and `liftSnd_eq` identify
  them with the sections over the image open `Δ.coborderRange.ι ''ᵁ V`.
* `Stacks.DiagonalDerivation.diagonalDelta`: `delta` for the two projections of `X ×_S X`, with
  the hypotheses stated over the image open `Δ.coborderRange.ι ''ᵁ V`, as in
  [Stacks, Tag 08S2].
* `Stacks.DiagonalDerivation.deltaIdealSection`: the section of the ideal sheaf of the diagonal
  whose image in the structure sheaf is `diagonalDelta`.

## Main results

Over an arbitrary morphism with two retractions:

* `Stacks.DiagonalDerivation.app_delta_eq_zero` and
  `Stacks.DiagonalDerivation.delta_mem_ker`: `delta b` is killed by the map on sections induced
  by `g`, hence lies in the kernel ideal.
* `Stacks.DiagonalDerivation.delta_zero`, `delta_add`, `delta_neg`, `delta_sub`: additivity.
* `Stacks.DiagonalDerivation.delta_mul`: **the exact Leibniz identity**, with the coefficient of
  `δ(b')` the *second* retraction applied to `b`.
* `Stacks.DiagonalDerivation.delta_mul_sub_leibniz`: with both coefficients taken from the
  *first* retraction instead, the defect is exactly `δ(b) · δ(b')`.
* `Stacks.DiagonalDerivation.delta_mul_delta_mem_sq`: that defect lies in the square of the
  kernel ideal.
* `Stacks.DiagonalDerivation.delta_appLE_eq_zero`: `delta` vanishes on sections pulled back
  along any `k : Z ⟶ T` that the two retractions agree over.
* `Stacks.DiagonalDerivation.delta_restrict`: compatibility with restriction, in both slots at
  once.

For the diagonal:

* `Stacks.DiagonalDerivation.diagonalDelta_eq`: `diagonalDelta` is `p₂^♯ b - p₁^♯ b` over the
  image open.
* `Stacks.DiagonalDerivation.app_liftFst` and `Stacks.DiagonalDerivation.app_liftSnd`: **both
  `p₁^♯ b` and `p₂^♯ b` are lifts of `b`** along the structure map of the canonical closed
  factorization of the diagonal.
* `Stacks.DiagonalDerivation.diagonalDelta_add`, `diagonalDelta_mul`,
  `diagonalDelta_mul_sub_leibniz`, `diagonalDelta_restrict`: additivity, the Leibniz identity
  and its defect, and compatibility with restriction.
* `Stacks.DiagonalDerivation.diagonalDelta_appLE_eq_zero`: **vanishing on `f⁻¹𝒪_S`.**
* `Stacks.DiagonalDerivation.app_diagonalDelta_eq_zero` and
  `Stacks.DiagonalDerivation.diagonalDelta_mul_delta_mem_sq`: the kernel and square statements
  for the diagonal.
* `Stacks.DiagonalDerivation.kernel_ι_deltaIdealSection`: the characterizing property of
  `deltaIdealSection`.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.appLE` carries a containment proof mentioning the morphism, so an
equation between morphisms cannot be rewritten inside it; `Stacks.DiagonalConormal.appLE_congr`
is the transport, and `delta_appLE_eq_zero` goes through it rather than through `rw`. The
containment proofs produced by `appLE_comp_appLE` and by `appLE_map` are anonymous, so the steps
that mention them are written as `calc` chains whose intermediate terms carry explicit
containment proofs and are accepted by proof irrelevance.

`Γ(↑O, V)` and `Γ(P, O.ι ''ᵁ V)` are the same type definitionally but not syntactically, so
`diagonalDelta` is stated at the first spelling and `diagonalDelta_eq` relates it to the
expression over the image open, which elaborates at the second, as in
`Stacks.DiagonalConormal.appLE_opensι_comp`. The `Mul` instance is not found across the second
spelling, so the Leibniz identity is stated with `liftFst` and `liftSnd`.

The ideal sheaf of a closed immersion, which [Stacks, Tag 01C2] writes `idealSheaf`, is
`Stacks.ClosedImmersion.idealSheaf` (`StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs`).

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.DiagonalDerivation

/-! ### The difference of two retractions, on sections -/

section TwoRetractions

variable {Z P : Scheme.{u}} (g : Z ⟶ P) (r₁ r₂ : P ⟶ Z) (U : Z.Opens) (W : P.Opens)
  (h₁ : W ≤ r₁ ⁻¹ᵁ U) (h₂ : W ≤ r₂ ⁻¹ᵁ U)

/-- **The difference of the two maps on sections induced by two retractions.** For a section `b`
of `𝒪_Z` over `U`, this is `r₂^♯ b - r₁^♯ b`, a section of `𝒪_P` over `W`. -/
noncomputable def delta (b : Γ(Z, U)) : Γ(P, W) :=
  (r₂.appLE U W h₂).hom b - (r₁.appLE U W h₁).hom b

/-- `delta` is the difference of the two maps on sections, by definition. -/
theorem delta_eq (b : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ b = (r₂.appLE U W h₂).hom b - (r₁.appLE U W h₁).hom b :=
  rfl

/-! #### Additivity -/

/-- `delta` sends `0` to `0`. -/
theorem delta_zero : delta r₁ r₂ U W h₁ h₂ 0 = 0 := by
  simp only [delta_eq, map_zero, sub_zero]

/-- `delta` is additive. -/
theorem delta_add (b b' : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ (b + b') =
      delta r₁ r₂ U W h₁ h₂ b + delta r₁ r₂ U W h₁ h₂ b' := by
  simp only [delta_eq, map_add]
  ring

/-- `delta` commutes with negation. -/
theorem delta_neg (b : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ (-b) = -delta r₁ r₂ U W h₁ h₂ b := by
  simp only [delta_eq, map_neg]
  ring

/-- `delta` commutes with subtraction. -/
theorem delta_sub (b b' : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ (b - b') =
      delta r₁ r₂ U W h₁ h₂ b - delta r₁ r₂ U W h₁ h₂ b' := by
  simp only [delta_eq, map_sub]
  ring

/-! #### The Leibniz identity -/

/-- **The Leibniz identity, exactly:** `δ(bb') = r₂^♯ b · δ(b') + r₁^♯ b' · δ(b)`. The
coefficient of `δ(b')` is `b` through the *second* retraction and the coefficient of `δ(b)` is
`b'` through the *first*. -/
theorem delta_mul (b b' : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ (b * b') =
      (r₂.appLE U W h₂).hom b * delta r₁ r₂ U W h₁ h₂ b' +
        (r₁.appLE U W h₁).hom b' * delta r₁ r₂ U W h₁ h₂ b := by
  simp only [delta_eq, map_mul]
  ring

/-- **The defect of the symmetric Leibniz rule is a product of two `delta`s.** Taking both
coefficients from the *first* retraction — so that both are the same lift of a section of `𝒪_Z`
as in `delta_mul` — overshoots by exactly `δ(b) · δ(b')`. -/
theorem delta_mul_sub_leibniz (b b' : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ (b * b') -
        ((r₁.appLE U W h₁).hom b * delta r₁ r₂ U W h₁ h₂ b' +
          (r₁.appLE U W h₁).hom b' * delta r₁ r₂ U W h₁ h₂ b) =
      delta r₁ r₂ U W h₁ h₂ b * delta r₁ r₂ U W h₁ h₂ b' := by
  simp only [delta_eq, map_mul]
  ring

/-- The same defect, with both coefficients taken from the *second* retraction: it is the
negative of the product. -/
theorem delta_mul_sub_leibniz' (b b' : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ (b * b') -
        ((r₂.appLE U W h₂).hom b * delta r₁ r₂ U W h₁ h₂ b' +
          (r₂.appLE U W h₂).hom b' * delta r₁ r₂ U W h₁ h₂ b) =
      -(delta r₁ r₂ U W h₁ h₂ b * delta r₁ r₂ U W h₁ h₂ b') := by
  simp only [delta_eq, map_mul]
  ring

/-! #### `delta` lands in the kernel ideal -/

/-- **`delta b` is killed by the map on sections induced by `g`.** -/
theorem app_delta_eq_zero (hr₁ : g ≫ r₁ = 𝟙 Z) (hr₂ : g ≫ r₂ = 𝟙 Z) (hU : U ≤ g ⁻¹ᵁ W)
    (b : Γ(Z, U)) :
    (g.appLE W U hU).hom (delta r₁ r₂ U W h₁ h₂ b) = 0 := by
  rw [delta_eq, map_sub,
    Stacks.DiagonalConormal.appLE_retraction hr₂ U W U h₂ hU le_rfl b,
    Stacks.DiagonalConormal.appLE_retraction hr₁ U W U h₁ hU le_rfl b, sub_self]

/-- `delta b` lies in the kernel of the map on sections induced by `g`. -/
theorem delta_mem_ker (hr₁ : g ≫ r₁ = 𝟙 Z) (hr₂ : g ≫ r₂ = 𝟙 Z) (hU : U ≤ g ⁻¹ᵁ W)
    (b : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ b ∈ RingHom.ker (g.appLE W U hU).hom :=
  app_delta_eq_zero g r₁ r₂ U W h₁ h₂ hr₁ hr₂ hU b

/-- **The defect of the symmetric Leibniz rule lies in the square of the kernel ideal.** -/
theorem delta_mul_delta_mem_sq (hr₁ : g ≫ r₁ = 𝟙 Z) (hr₂ : g ≫ r₂ = 𝟙 Z) (hU : U ≤ g ⁻¹ᵁ W)
    (b b' : Γ(Z, U)) :
    delta r₁ r₂ U W h₁ h₂ b * delta r₁ r₂ U W h₁ h₂ b' ∈
      RingHom.ker (g.appLE W U hU).hom ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul (delta_mem_ker g r₁ r₂ U W h₁ h₂ hr₁ hr₂ hU b)
    (delta_mem_ker g r₁ r₂ U W h₁ h₂ hr₁ hr₂ hU b')

/-! #### Vanishing on sections pulled back along a common factor -/

/-- **`delta` vanishes on sections pulled back along anything the two retractions agree over.**
If `r₁ ≫ k = r₂ ≫ k` then the two maps on sections agree on the image of `k^♯`, so their
difference is zero there. -/
theorem delta_appLE_eq_zero {T : Scheme.{u}} (k : Z ⟶ T) (hk : r₁ ≫ k = r₂ ≫ k) (O : T.Opens)
    (hO : U ≤ k ⁻¹ᵁ O) (a : Γ(T, O)) :
    delta r₁ r₂ U W h₁ h₂ ((k.appLE O U hO).hom a) = 0 := by
  have p₁ : W ≤ (r₁ ≫ k) ⁻¹ᵁ O := h₁.trans (r₁.preimage_mono hO)
  have p₂ : W ≤ (r₂ ≫ k) ⁻¹ᵁ O := h₂.trans (r₂.preimage_mono hO)
  have key : (r₁.appLE U W h₁).hom ((k.appLE O U hO).hom a) =
      (r₂.appLE U W h₂).hom ((k.appLE O U hO).hom a) :=
    calc (r₁.appLE U W h₁).hom ((k.appLE O U hO).hom a)
        = ((k.appLE O U hO ≫ r₁.appLE U W h₁).hom) a := rfl
      _ = ((r₁ ≫ k).appLE O W p₁).hom a :=
            congr($(Scheme.Hom.appLE_comp_appLE r₁ k O U W hO h₁) a)
      _ = ((r₂ ≫ k).appLE O W p₂).hom a :=
            congr($(Stacks.DiagonalConormal.appLE_congr hk O W p₁ p₂) a)
      _ = ((k.appLE O U hO ≫ r₂.appLE U W h₂).hom) a :=
            (congr($(Scheme.Hom.appLE_comp_appLE r₂ k O U W hO h₂) a)).symm
      _ = (r₂.appLE U W h₂).hom ((k.appLE O U hO).hom a) := rfl
  rw [delta_eq, ← key, sub_self]

/-! #### Compatibility with restriction -/

/-- **`delta` commutes with restriction**, in both slots at once: restricting `delta b` from `W`
to a smaller open `W'` of `P` gives `delta` of the restriction of `b` to a smaller open `U'` of
`Z`, provided the two new opens again satisfy the two containments. -/
theorem delta_restrict (U' : Z.Opens) (hU' : U' ≤ U) (W' : P.Opens) (hW' : W' ≤ W)
    (h₁' : W' ≤ r₁ ⁻¹ᵁ U') (h₂' : W' ≤ r₂ ⁻¹ᵁ U') (b : Γ(Z, U)) :
    (P.presheaf.map (homOfLE hW').op).hom (delta r₁ r₂ U W h₁ h₂ b) =
      delta r₁ r₂ U' W' h₁' h₂' ((Z.presheaf.map (homOfLE hU').op).hom b) := by
  have key : ∀ (r : P ⟶ Z) (hr : W ≤ r ⁻¹ᵁ U) (hr' : W' ≤ r ⁻¹ᵁ U'),
      (P.presheaf.map (homOfLE hW').op).hom ((r.appLE U W hr).hom b) =
        (r.appLE U' W' hr').hom ((Z.presheaf.map (homOfLE hU').op).hom b) := by
    intro r hr hr'
    have hW'' : W' ≤ r ⁻¹ᵁ U := hr'.trans (r.preimage_mono hU')
    calc (P.presheaf.map (homOfLE hW').op).hom ((r.appLE U W hr).hom b)
        = ((r.appLE U W hr ≫ P.presheaf.map (homOfLE hW').op).hom) b := rfl
      _ = ((r.appLE U W' hW'').hom) b :=
            congr($(Scheme.Hom.appLE_map r hr (homOfLE hW').op) b)
      _ = ((Z.presheaf.map (homOfLE hU').op ≫ r.appLE U' W' hr').hom) b :=
            (congr($(Scheme.Hom.map_appLE r hr' (homOfLE hU').op) b)).symm
      _ = (r.appLE U' W' hr').hom ((Z.presheaf.map (homOfLE hU').op).hom b) := rfl
  rw [delta_eq, delta_eq, map_sub, key r₂ h₂ h₂', key r₁ h₁ h₁']

end TwoRetractions

/-! ### The diagonal: the two projections as retractions -/

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
  (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
    (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
  (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
    (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))

/-- **`p₁^♯ b`, as a section of `𝒪_{Δ.coborderRange}` over `V`.** -/
noncomputable def liftFst (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, V) :=
  (((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f).appLE
    ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) V
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₁)).hom b

/-- **`p₂^♯ b`, as a section of `𝒪_{Δ.coborderRange}` over `V`.** -/
noncomputable def liftSnd (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, V) :=
  (((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f).appLE
    ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) V
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₂)).hom b

/-- `liftFst` is `p₁^♯ b` read over the image open `Δ.coborderRange.ι ''ᵁ V`. -/
theorem liftFst_eq (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    liftFst f V h₁ b = ((pullback.fst f f).appLE _ _ h₁).hom b :=
  Stacks.DiagonalConormal.appLE_opensι_comp (pullback.diagonal f).coborderRange
    (pullback.fst f f) h₁ b

/-- `liftSnd` is `p₂^♯ b` read over the image open `Δ.coborderRange.ι ''ᵁ V`. -/
theorem liftSnd_eq (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    liftSnd f V h₂ b = ((pullback.snd f f).appLE _ _ h₂).hom b :=
  Stacks.DiagonalConormal.appLE_opensι_comp (pullback.diagonal f).coborderRange
    (pullback.snd f f) h₂ b

/-- **`p₁^♯ b` is a lift of `b` along the structure map of the canonical closed factorization of
the diagonal.** -/
theorem app_liftFst (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).liftCoborder.app V).hom (liftFst f V h₁ b) = b :=
  (congrArg _ (liftFst_eq f V h₁ b)).trans
    (Stacks.DiagonalConormal.liftCoborder_appLE_fst f V h₁ b)

/-- **`p₂^♯ b` is a lift of `b` along the structure map of the canonical closed factorization of
the diagonal.** -/
theorem app_liftSnd (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).liftCoborder.app V).hom (liftSnd f V h₂ b) = b :=
  (congrArg _ (liftSnd_eq f V h₂ b)).trans
    (Stacks.DiagonalConormal.liftCoborder_appLE_snd f V h₂ b)

/-- **The section `p₂^♯ b - p₁^♯ b` of [Stacks, Tag 08S2].** This is `delta` for the two
projections of `X ×_S X`, read on the coborder neighbourhood of the diagonal, with the
containments stated over the image open `Δ.coborderRange.ι ''ᵁ V`. -/
noncomputable def diagonalDelta (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, V) :=
  delta ((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f)
    ((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f)
    ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) V
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₁)
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₂) b

/-- **`diagonalDelta` is `p₂^♯ b - p₁^♯ b` read over the image open
`Δ.coborderRange.ι ''ᵁ V`.** -/
theorem diagonalDelta_eq (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ b =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b := by
  rw [← liftSnd_eq f V h₂ b, ← liftFst_eq f V h₁ b]
  rfl

/-- `diagonalDelta` is the difference of the two lifts of `b`. -/
theorem diagonalDelta_eq_liftSnd_sub_liftFst
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ b = liftSnd f V h₂ b - liftFst f V h₁ b :=
  rfl

/-! #### The derivation axioms for the diagonal -/

/-- `diagonalDelta` sends `0` to `0`. -/
theorem diagonalDelta_zero : diagonalDelta f V h₁ h₂ 0 = 0 :=
  delta_zero _ _ _ _ _ _

/-- `diagonalDelta` is additive. -/
theorem diagonalDelta_add (b b' : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ (b + b') =
      diagonalDelta f V h₁ h₂ b + diagonalDelta f V h₁ h₂ b' :=
  delta_add _ _ _ _ _ _ b b'

/-- `diagonalDelta` commutes with subtraction. -/
theorem diagonalDelta_sub (b b' : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ (b - b') =
      diagonalDelta f V h₁ h₂ b - diagonalDelta f V h₁ h₂ b' :=
  delta_sub _ _ _ _ _ _ b b'

/-- **The Leibniz identity for the diagonal, exactly**, with no quotient: the coefficient of
`δ(b')` is `p₂^♯ b` and the coefficient of `δ(b)` is `p₁^♯ b'`. -/
theorem diagonalDelta_mul (b b' : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ (b * b') =
      liftSnd f V h₂ b * diagonalDelta f V h₁ h₂ b' +
        liftFst f V h₁ b' * diagonalDelta f V h₁ h₂ b :=
  delta_mul _ _ _ _ _ _ b b'

/-- **The defect of the symmetric Leibniz rule for the diagonal.** Taking both coefficients from
the first projection overshoots by exactly `δ(b) · δ(b')`. -/
theorem diagonalDelta_mul_sub_leibniz (b b' : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ (b * b') -
        (liftFst f V h₁ b * diagonalDelta f V h₁ h₂ b' +
          liftFst f V h₁ b' * diagonalDelta f V h₁ h₂ b) =
      diagonalDelta f V h₁ h₂ b * diagonalDelta f V h₁ h₂ b' :=
  delta_mul_sub_leibniz _ _ _ _ _ _ b b'

/-- **`p₂^♯ b - p₁^♯ b` is killed by the structure map of the canonical closed factorization of
the diagonal.** -/
theorem app_diagonalDelta_eq_zero (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    (((pullback.diagonal f).liftCoborder.appLE V
        ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) le_rfl).hom)
      (diagonalDelta f V h₁ h₂ b) = 0 :=
  app_delta_eq_zero _ _ _ _ _ _ _
    (Stacks.DiagonalConormal.liftCoborder_comp_fst f)
    (Stacks.DiagonalConormal.liftCoborder_comp_snd f) le_rfl b

/-- `p₂^♯ b - p₁^♯ b` lies in the ideal of the diagonal, read as the kernel of the map on
sections of the canonical closed factorization. -/
theorem diagonalDelta_mem_ker (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ b ∈
      RingHom.ker (((pullback.diagonal f).liftCoborder.appLE V
        ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) le_rfl).hom) :=
  app_diagonalDelta_eq_zero f V h₁ h₂ b

/-- **The Leibniz defect for the diagonal lies in the square of the ideal.** -/
theorem diagonalDelta_mul_delta_mem_sq
    (b b' : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    diagonalDelta f V h₁ h₂ b * diagonalDelta f V h₁ h₂ b' ∈
      RingHom.ker (((pullback.diagonal f).liftCoborder.appLE V
        ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) le_rfl).hom) ^ 2 :=
  delta_mul_delta_mem_sq _ _ _ _ _ _ _
    (Stacks.DiagonalConormal.liftCoborder_comp_fst f)
    (Stacks.DiagonalConormal.liftCoborder_comp_snd f) le_rfl b b'

/-- **Vanishing on `f⁻¹𝒪_S`.** A section of `𝒪_X` pulled back from `S` has
`p₂^♯ b - p₁^♯ b = 0`. This is the third derivation axiom. -/
theorem diagonalDelta_appLE_eq_zero (O : S.Opens)
    (hO : (pullback.diagonal f).liftCoborder ⁻¹ᵁ V ≤ f ⁻¹ᵁ O) (a : Γ(S, O)) :
    diagonalDelta f V h₁ h₂ ((f.appLE O _ hO).hom a) = 0 :=
  delta_appLE_eq_zero _ _ _ _ _ _ f
    (by rw [Category.assoc, Category.assoc, pullback.condition]) O hO a

/-- **Compatibility with restriction** for the diagonal. -/
theorem diagonalDelta_restrict
    (V' : (pullback.diagonal f).coborderRange.toScheme.Opens) (hV' : V' ≤ V)
    (hU' : (pullback.diagonal f).liftCoborder ⁻¹ᵁ V' ≤
      (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)
    (h₁' : (pullback.diagonal f).coborderRange.ι ''ᵁ V' ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V'))
    (h₂' : (pullback.diagonal f).coborderRange.ι ''ᵁ V' ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V'))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    ((pullback.diagonal f).coborderRange.toScheme.presheaf.map (homOfLE hV').op).hom
        (diagonalDelta f V h₁ h₂ b) =
      diagonalDelta f V' h₁' h₂' ((X.presheaf.map (homOfLE hU').op).hom b) :=
  delta_restrict _ _ _ _ _ _ _ hU' _ hV'
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₁')
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₂') b

/-! #### The section of the ideal sheaf -/

/-- **The section of the ideal sheaf of the diagonal whose image is `p₂^♯ b - p₁^♯ b`.** -/
noncomputable def deltaIdealSection (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V) :=
  (Stacks.DiagonalConormal.exists_idealSheaf_section_snd_sub_fst f V h₁ h₂ b).choose

/-- The characterizing property of `deltaIdealSection`: its image in the structure sheaf is
`p₂^♯ b - p₁^♯ b`. -/
theorem kernel_ι_deltaIdealSection (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V)
      (deltaIdealSection f V h₁ h₂ b) =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b :=
  (Stacks.DiagonalConormal.exists_idealSheaf_section_snd_sub_fst f V h₁ h₂ b).choose_spec

/-- `deltaIdealSection` is determined by its image: any section of the ideal sheaf whose image is
`p₂^♯ b - p₁^♯ b` equals it. -/
theorem eq_deltaIdealSection (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b) :
    x = deltaIdealSection f V h₁ h₂ b :=
  Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder V
    (hx.trans (kernel_ι_deltaIdealSection f V h₁ h₂ b).symm)

end Diagonal

end Stacks.DiagonalDerivation

end
