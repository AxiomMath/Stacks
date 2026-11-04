module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterMultiplicative
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# The rational Chow ring of a regular scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a Noetherian
(equivalently quasi-compact) regular scheme locally of finite type over `S`, with affine diagonal
and `δ_{X/S}` bounded, so that

  `Φ : K_0(Vect(X)) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,   `α' ↦ ch(α') ∩ [X]`,

is bijective (Stacks 0FEY), and let `α · β = ch(Φ⁻¹ α) ∩ β` be the intersection product of Section
0FEX. Section 0FEX closes with the reformulation: there is a unique commutative, associative
intersection product on `CH^*(X) ⊗ 𝐐`, compatible with the grading, such that `Φ` is an isomorphism
of rings.

## Main definitions

* `Stacks.Chow.RationalIntersectionRing` — `CH_*(X) ⊗ 𝐐` with the intersection product, a
  commutative `𝐐`-algebra with unit `[X]`.
* `Stacks.Chow.rationalChernCharacterAlgEquiv` — `Φ` as an isomorphism of `𝐐`-algebras
  `K_0(Vect(X)) ⊗ 𝐐 ≃ CH_*(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.rationalChernCharacterCap_mul_apply_rationalFundamentalClass` —
  `Φ(α' β') = Φ(α') · Φ(β')`.
* `Stacks.Chow.eq_rationalIntersectionProduct_of_map_mul` — a bilinear product for which `Φ` is
  multiplicative is the product of Section 0FEX.
* `Stacks.Chow.existsUnique_rationalIntersectionProduct` — the reformulation closing
  Section 0FEX: the product of Section 0FEX is the unique bilinear product which is commutative,
  associative, graded by codimension, and for which `Φ` is multiplicative.

## References

* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

section Unit

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`ch(1) ∩ -` is the identity** for `1 ∈ K_0(Vect(X)) ⊗ 𝐐`. -/
theorem rationalChernCharacterCap_one : rationalChernCharacterCap C sX 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, rationalChernCharacterCap_tmul, chernCharacterCap_one,
    one_smul]

end Unit

section Multiplicative

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)
  (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
    relativeDimension C.dimensionFunction sX x ≤ hi)

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

/-- **The map of Stacks 0FEY is multiplicative**:
`ch(α' β') ∩ [X] = (ch(α') ∩ [X]) · (ch(β') ∩ [X])` for the product of Section 0FEX. -/
theorem rationalChernCharacterCap_mul_apply_rationalFundamentalClass
    (a b : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterCap C sX (a * b) (rationalFundamentalClass C sX) =
      rationalIntersectionProduct hX hb
        (rationalChernCharacterCap C sX a (rationalFundamentalClass C sX))
        (rationalChernCharacterCap C sX b (rationalFundamentalClass C sX)) := by
  obtain ⟨lo, _, hlo⟩ := id hb
  rw [rationalChernCharacterCap_mul C sX lo (fun x => (hlo x).1), Module.End.mul_apply,
    rationalIntersectionProduct_rationalChernCharacterCap]

/-- **Uniqueness of the product among those making the map of Stacks 0FEY multiplicative**: a
bilinear product `μ` with `μ (ch(α') ∩ [X]) (ch(β') ∩ [X]) = ch(α' β') ∩ [X]` is the product of
Section 0FEX. -/
theorem eq_rationalIntersectionProduct_of_map_mul {μ : CHQ →ₗ[ℚ] CHQ →ₗ[ℚ] CHQ}
    (h : ∀ a b, μ (rationalChernCharacterCap C sX a (rationalFundamentalClass C sX))
        (rationalChernCharacterCap C sX b (rationalFundamentalClass C sX)) =
      rationalChernCharacterCap C sX (a * b) (rationalFundamentalClass C sX)) :
    μ = rationalIntersectionProduct hX hb := by
  refine eq_rationalIntersectionProduct hX hb fun a β => ?_
  obtain ⟨b, rfl⟩ := (bijective_flip_rationalChernCharacterCap hX hb).2 β
  rw [LinearMap.flip_apply, h, rationalChernCharacterCap_mul_apply_rationalFundamentalClass hX hb,
    rationalIntersectionProduct_rationalChernCharacterCap]

include hX hb in
/-- For `X` as in Stacks 0FEY (Noetherian, equivalently quasi-compact, regular, of finite type over
`S`, with affine diagonal and `δ_{X/S}` bounded), `rationalIntersectionProduct` is the unique
bilinear product on `CH^*(X) ⊗ 𝐐 = CH_*(X) ⊗ 𝐐` which is commutative, associative, graded by the
codimension pieces `codimensionChowSubmodule`, and for which `α' ↦ ch(α') ∩ [X]` is multiplicative,
that is, an isomorphism of rings. -/
@[stacks 0FEX "the closing reformulation of the section: for X as in 0FEY, there is a unique \
commutative, associative intersection product on CH^*(X) ⊗ Q compatible with the grading such \
that K_0(Vect(X)) ⊗ Q → CH^*(X) ⊗ Q is a ring isomorphism, and it is the product of the section"]
theorem existsUnique_rationalIntersectionProduct :
    ∃! μ : CHQ →ₗ[ℚ] CHQ →ₗ[ℚ] CHQ,
      (∀ a b, μ (rationalChernCharacterCap C sX a (rationalFundamentalClass C sX))
          (rationalChernCharacterCap C sX b (rationalFundamentalClass C sX)) =
        rationalChernCharacterCap C sX (a * b) (rationalFundamentalClass C sX)) ∧
      (∀ α β, μ α β = μ β α) ∧ (∀ α β γ, μ (μ α β) γ = μ α (μ β γ)) ∧
      ∀ {i j : ℕ} {α β : CHQ}, α ∈ codimensionChowSubmodule C sX i →
        β ∈ codimensionChowSubmodule C sX j → μ α β ∈ codimensionChowSubmodule C sX (i + j) :=
  ⟨rationalIntersectionProduct hX hb,
    ⟨fun a b => (rationalChernCharacterCap_mul_apply_rationalFundamentalClass hX hb a b).symm,
      rationalIntersectionProduct_comm hX hb, rationalIntersectionProduct_assoc hX hb,
      rationalIntersectionProduct_mem_codimensionChowSubmodule hX hb⟩,
    fun _ hμ => eq_rationalIntersectionProduct_of_map_mul hX hb hμ.1⟩

end Multiplicative

/-! ### The rational Chow ring -/

section Ring

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **The rational Chow ring** of `X`: `CH_*(X) ⊗ 𝐐` with the intersection product of
Section 0FEX, for `X` as in Stacks 0FEY. -/
def RationalIntersectionRing (_hX : IsRegular X)
    (_hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi) : Type u :=
  DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

variable (hX : IsRegular X)
  (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
    relativeDimension C.dimensionFunction sX x ≤ hi)

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

namespace RationalIntersectionRing

/-- The additive group of the rational Chow ring is `CH_*(X) ⊗ 𝐐`. -/
instance : AddCommGroup (RationalIntersectionRing hX hb) :=
  inferInstanceAs (AddCommGroup CHQ)

/-- The `𝐐`-module structure of the rational Chow ring is that of `CH_*(X) ⊗ 𝐐`. -/
instance : Module ℚ (RationalIntersectionRing hX hb) :=
  inferInstanceAs (Module ℚ CHQ)

/-- The intersection product makes `CH_*(X) ⊗ 𝐐` a commutative ring with unit `[X]`. -/
instance : CommRing (RationalIntersectionRing hX hb) where
  __ := (inferInstance : AddCommGroup (RationalIntersectionRing hX hb))
  mul α β := rationalIntersectionProduct hX hb α β
  one := rationalFundamentalClass C sX
  mul_assoc := rationalIntersectionProduct_assoc hX hb
  one_mul := rationalFundamentalClass_rationalIntersectionProduct hX hb
  mul_one := rationalIntersectionProduct_rationalFundamentalClass hX hb
  zero_mul := LinearMap.map_zero₂ (rationalIntersectionProduct hX hb)
  mul_zero α := map_zero (rationalIntersectionProduct hX hb α)
  left_distrib α := map_add (rationalIntersectionProduct hX hb α)
  right_distrib := LinearMap.map_add₂ (rationalIntersectionProduct hX hb)
  mul_comm := rationalIntersectionProduct_comm hX hb

/-- The intersection product is `𝐐`-bilinear, so the rational Chow ring is a `𝐐`-algebra. -/
instance : Algebra ℚ (RationalIntersectionRing hX hb) :=
  Algebra.ofModule (fun r α β => LinearMap.map_smul₂ (rationalIntersectionProduct hX hb) r α β)
    (fun r α β => map_smul (rationalIntersectionProduct hX hb α) r β)

/-- The identity `CH_*(X) ⊗ 𝐐 ≃ RationalIntersectionRing hX hb`, as a `𝐐`-linear equivalence. -/
def equiv : CHQ ≃ₗ[ℚ] RationalIntersectionRing hX hb :=
  LinearEquiv.refl ℚ CHQ

/-- The product of the rational Chow ring is the intersection product of Section 0FEX. -/
theorem equiv_mul_equiv (α β : CHQ) :
    equiv hX hb α * equiv hX hb β = equiv hX hb (rationalIntersectionProduct hX hb α β) :=
  rfl

/-- The unit of the rational Chow ring is the fundamental class `[X]`. -/
theorem one_eq :
    (1 : RationalIntersectionRing hX hb) = equiv hX hb (rationalFundamentalClass C sX) :=
  rfl

end RationalIntersectionRing

/-- **The map of Stacks 0FEY is an isomorphism of rings**: for `X` as in Stacks 0FEY,
`α' ↦ ch(α') ∩ [X]` is an isomorphism of `𝐐`-algebras from `K_0(Vect(X)) ⊗ 𝐐` onto the rational
Chow ring `CH^*(X) ⊗ 𝐐 = CH_*(X) ⊗ 𝐐` with the product `rationalIntersectionProduct`. -/
@[stacks 0FEX "the closing sentence of the section: for X as in 0FEY, K_0(Vect(X)) ⊗ Q → \
CH^*(X) ⊗ Q, α' ↦ ch(α') ∩ [X], is an isomorphism of rings for the product of the section"]
def rationalChernCharacterAlgEquiv :
    ℚ ⊗[ℤ] VectorBundleKZero X ≃ₐ[ℚ] RationalIntersectionRing hX hb :=
  AlgEquiv.ofLinearEquiv ((LinearEquiv.ofBijective _
      (bijective_flip_rationalChernCharacterCap hX hb)).trans
        (RationalIntersectionRing.equiv hX hb))
    (by
      change rationalChernCharacterCap C sX 1 (rationalFundamentalClass C sX) = _
      rw [rationalChernCharacterCap_one, Module.End.one_apply]
      rfl)
    (rationalChernCharacterCap_mul_apply_rationalFundamentalClass hX hb)

/-- `rationalChernCharacterAlgEquiv` is `α' ↦ ch(α') ∩ [X]`. -/
theorem rationalChernCharacterAlgEquiv_apply (a : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterAlgEquiv hX hb a =
      RationalIntersectionRing.equiv hX hb
        (rationalChernCharacterCap C sX a (rationalFundamentalClass C sX)) :=
  rfl

end Ring

end Stacks.Chow

end
