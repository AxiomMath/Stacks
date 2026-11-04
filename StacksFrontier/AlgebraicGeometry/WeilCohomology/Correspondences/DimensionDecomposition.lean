module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart

/-!
# Correspondences between smooth projective schemes of mixed dimension

Section 0FFZ of the Stacks Project decomposes a smooth projective scheme `X` over `k` as
`X = ∐_d X_d`, with `X_d` open and closed and equidimensional of dimension `d`, and defines

`Corrʳ(X, Y) = ⊕_d CH^{d+r}(X_d × Y) ⊗ ℚ`.

Decomposing `Y = ∐_e Y_e` as well, `X_d × Y = ∐_e X_d × Y_e` and `X_d × Y_e` has dimension
`d + e`, so `CH^{d+r}(X_d × Y) = ⊕_e CH_{e-r}(X_d × Y_e)`. This file builds that group and the
composition, pullback and pushforward of the source on it, piece by piece from the equidimensional
constructions of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition`.

## Main definitions

* `Stacks.WeilCohomology.Corr`: `Corrʳ(X, Y) = ⊕_d ⊕_e CH_{e-r}(X_d × Y_e) ⊗ ℚ`.
* `Stacks.WeilCohomology.CodimChow`: `CH^i(X) ⊗ ℚ = ⊕_d CH_{d-i}(X_d) ⊗ ℚ`, the codimension
  grading on a scheme of mixed dimension.
* `Stacks.WeilCohomology.comp`: composition `Corrʳ(X, Y) × Corrˢ(Y, Z) ⟶ Corr^{r+s}(X, Z)`,
  `(c'∘c)_{d,f} = Σ_e c'_{e,f} ∘ c_{d,e}`.
* `Stacks.WeilCohomology.pullback`: `c^* : CH_m(Y) ⊗ ℚ ⟶ CH_{m-r}(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.pushforward`: `c_* : CH^i(X) ⊗ ℚ ⟶ CH^{i+r}(Y) ⊗ ℚ`.

## Implementation notes

The source's formula `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` on `X × Y × Z` is computed piece by
piece: `pr₂₃` is flat of relative dimension `d` only over `X_d × Y × Z`, so the source itself
forms `pr₂₃^*` on each piece, and the intersection product on the smooth scheme
`X × Y × Z = ∐ X_d × Y_e × Z_f` is the product on each piece. A summand with `c` supported on
`X_d × Y_e` and `c'` on `Y_{e'} × Z_f`, `e ≠ e'`, meets in `X_d × (Y_e ∩ Y_{e'}) × Z_f = ∅` and
contributes nothing; the nested direct sums below encode this by pairing the `e`-component of `c`
only with the `e`-component of `c'`, through `DirectSum.component`, so that no transport between
index types occurs.

The Gysin classes of the diagonals are a `Stacks.WeilCohomology.DiagonalClassFamily`, as in
`Composition`. Projectivity is replaced by properness, which is all that is used.

## References

* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Groups

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
  [Smooth sZ] [IsSeparated sZ]

/-- **Correspondences of degree `r`** from `X` to `Y`, Section 0FFZ:
`Corrʳ(X, Y) = ⊕_d CH^{d+r}(X_d × Y) ⊗ ℚ = ⊕_d ⊕_e CH_{e-r}(X_d × Y_e) ⊗ ℚ`. -/
abbrev Corr (r : ℤ) : Type u :=
  DirectSum ℕ fun d ↦ DirectSum ℕ fun e ↦
    Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r

/-- The rational Chow group of `X` in codimension `i`, `CH^i(X) ⊗ ℚ = ⊕_d CH_{d-i}(X_d) ⊗ ℚ`. -/
abbrev CodimChow (i : ℤ) : Type u :=
  DirectSum ℕ fun d ↦ TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) (d - i))

/-- The scalar action of `ℚ` on `Corrʳ(X, Y)` commutes with itself. -/
instance (r : ℤ) : SMulCommClass ℚ ℚ (Corr k sX sY r) := smulCommClass_self ℚ _

/-- The scalar action of `ℚ` on `CH^i(X) ⊗ ℚ` commutes with itself. -/
instance (i : ℤ) : SMulCommClass ℚ ℚ (CodimChow k sX i) := smulCommClass_self ℚ _

variable (Δ : DiagonalClassFamily k)

/-- The `(d, e)` block of composition: `c ↦ (c' ↦ (f ↦ c'_{e,f} ∘ c))` for
`c ∈ Corrʳ(X_d, Y_e)`. -/
def compBlock [IsProper sY] (r s : ℤ) (d e : ℕ) :
    Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r →ₗ[ℚ]
      Corr k sY sZ s →ₗ[ℚ] DirectSum ℕ fun f ↦
        Correspondence (fieldChowSituation k) (partBase sX d) (partBase sZ f) f (r + s) :=
  (DirectSum.toModule ℚ ℕ _ fun f ↦
      ((composition k (partBase sX d) (partBase sY e) (partBase sZ f) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
          (relativeDimension_partBase sZ f) r s).compr₂
        (DirectSum.lof ℚ ℕ (fun f : ℕ ↦ Correspondence (fieldChowSituation k) (partBase sX d)
          (partBase sZ f) f (r + s)) f)).flip).flip.compl₂
    (DirectSum.component ℚ ℕ _ e)

/-- **Composition of correspondences** `Corrʳ(X, Y) × Corrˢ(Y, Z) ⟶ Corr^{r+s}(X, Z)` of
Section 0FFZ, `(c, c') ↦ c' ∘ c`, as a `ℚ`-bilinear map; on the pieces it is
`(c' ∘ c)_{d,f} = Σ_e c'_{e,f} ∘ c_{d,e}`. -/
def comp [IsProper sY] (r s : ℤ) :
    Corr k sX sY r →ₗ[ℚ] Corr k sY sZ s →ₗ[ℚ] Corr k sX sZ (r + s) :=
  DirectSum.toModule ℚ ℕ _ fun d ↦
    (DirectSum.toModule ℚ ℕ _ fun e ↦ compBlock (k := k) (sX := sX) (sY := sY) (sZ := sZ)
        (Δ := Δ) r s d e).compr₂
      (DirectSum.lof ℚ ℕ (fun d : ℕ ↦ DirectSum ℕ fun f ↦
        Correspondence (fieldChowSituation k) (partBase sX d) (partBase sZ f) f (r + s)) d)

/-- Restriction `CH_m(Y) ⊗ ℚ ⟶ CH_m(Y_e) ⊗ ℚ` to a part of `Y`. -/
def restrictPart (e : ℕ) (m : ℤ) :
    TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY m) →ₗ[ℚ]
      TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sY e) m) :=
  (chowGroupRestrict (fieldChowSituation k) sY (partBase sY e) (dimPart sY e).ι rfl
    m).toIntLinearMap.baseChange ℚ

/-- Pushforward `CH_m(X_d) ⊗ ℚ ⟶ CH_m(X) ⊗ ℚ` along the closed immersion of a part. -/
def includePart (d : ℕ) (m : ℤ) :
    TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) m) →ₗ[ℚ]
      TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX m) :=
  haveI := (isClopenDecomposition_dimPart sX).isProper_ι d
  (properChowPushforward (fieldChowSituation k) (partBase sX d) sX (dimPart sX d).ι rfl m
    (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap.baseChange ℚ

/-- **Pullback by a correspondence**, `c^*(β) = pr₁,*(c · pr₂^* β)` for `c ∈ Corrʳ(X, Y)` and
`β ∈ CH_m(Y) ⊗ ℚ`, landing in `CH_{m-r}(X) ⊗ ℚ`: on the pieces, `Σ_{d,e} c_{d,e}^*(β|_{Y_e})`
pushed into `X`. -/
def pullback [IsProper sX] [IsProper sY] (r m : ℤ) :
    Corr k sX sY r →ₗ[ℚ] TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY m) →ₗ[ℚ]
      TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (m - r)) :=
  DirectSum.toModule ℚ ℕ _ fun d ↦ DirectSum.toModule ℚ ℕ _ fun e ↦
    ((correspondencePullback k (partBase sX d) (partBase sY e) Δ
        (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) r m).compl₂
      (restrictPart k sY e m)).compr₂ (includePart k sX d (m - r))

/-- **Pushforward by a correspondence**, `c_*(α) = pr₂,*(c · pr₁^* α)` for `c ∈ Corrʳ(X, Y)` and
`α ∈ CH^i(X) ⊗ ℚ`, landing in `CH^{i+r}(Y) ⊗ ℚ`: on the pieces,
`(c_* α)_e = Σ_d c_{d,e,*}(α_d)`. -/
def pushforward [IsProper sX] (r i : ℤ) :
    Corr k sX sY r →ₗ[ℚ] CodimChow k sX i →ₗ[ℚ] CodimChow k sY (i + r) :=
  DirectSum.toModule ℚ ℕ _ fun d ↦ DirectSum.toModule ℚ ℕ _ fun e ↦
    ((correspondencePushforward k (partBase sX d) (partBase sY e) Δ
        (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) r i).compl₂
      (DirectSum.component ℚ ℕ _ d)).compr₂
      (DirectSum.lof ℚ ℕ (fun e : ℕ ↦ TensorProduct ℤ ℚ
        (chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - (i + r)))) e)

end Groups

end Stacks.WeilCohomology

end
