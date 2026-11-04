module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeNormalizationExactSequence
public import StacksFrontier.RingTheory.Derivation.Extension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a vector field from a node to its normalization

Let `A` be a local algebra over a field `k` with normalization
`A' = integralClosure A (FractionRing A)`, and suppose `A'` carries two `k`-algebra maps
`ε₁, ε₂ : A' → k` agreeing on the image of `A` and with `t ↦ ε₁ t - ε₂ t` surjective with kernel
the image of `A` — the exact sequence `0 → A → A' → k → 0` of Tag 0C1X. Then every
`k`-derivation of `A` extends uniquely to a `k`-derivation of `A'`, and the extension fixes both
of the points cut out by `ε₁` and `ε₂`.

This is the left-to-right direction of Tag 0E68 in local ring-theoretic form: a vector field on
`X` is a vector field on `X^ν` fixing the points of `S` above the node. Together with
`Stacks.Curves.existsUnique_restrict_of_fixes`, which is the right-to-left direction, it is the
local content of the equality of the tag.

## Main definitions

There are no definitions.

## Main results

* `Stacks.Curves.existsUnique_extend_integralClosure_of_exact` — the extension and its
  uniqueness, from the exact sequence.
* `Stacks.Curves.mem_maximalIdeal_apply_of_exact` — every `k`-derivation of `A` lands in the
  maximal ideal, so it fixes the node itself.
* `Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra` — the same with the
  exact sequence supplied by nodality.

## Implementation notes

The source extends the vector field using `𝒪_{X^ν, x'} = k + (u)` on each branch. That
presentation is not available for the *semilocal* normalization `A'` that the rest of the
development uses, and on an irreducible nodal curve `A'` is not a product of two branch rings at
all. What replaces it is the exact sequence itself: `A' = A ⊕ k t₀` as `k`-modules for any `t₀`
with `ε₁ t₀ - ε₂ t₀ = 1`, since subtracting `(ε₁ t - ε₂ t) t₀` from `t` lands in the image of
`A`. So `A'` is generated over `A` by a single element satisfying one monic quadratic relation
`t₀ ^ 2 = a₂ + c₂ t₀`, and a derivation extending `D` is forced on `t₀` by the Leibniz rule:
`(2 t₀ - c₂) D' t₀ = D a₂`.

The element `u = 2 t₀ - c₂` is a unit of `A'` in every characteristic, which is what makes the
extension both exist and be unique. The reason is not that `ε₁ u = 1` and `ε₂ u = -1` — that
would need the count of the maximal ideals of `A'` — but that `u ^ 2 = 4 a₂ + c₂ ^ 2` lies in the
image of `A`, where its residue is `(ε₁ u) ^ 2 = 1`; an element of the *local* ring `A` with
nonzero residue is a unit, so `u ^ 2` is a unit and hence so is `u`.

Existence is then obtained by restriction rather than by construction: `D` extends uniquely to
the total ring of fractions by Tag 07PE (`Stacks.DerivationExtension.locDeriv`), which gives the
Leibniz rule for free, and the computation above says exactly that this extension carries `t₀`,
and therefore all of `A' = A ⊕ k t₀`, into `A'`. The base ring there is `ℤ`, since that is how
Tag 07PE is stated; `k`-linearity is recovered on the restriction from
`D (algebraMap k A c) = 0`.

That the extension fixes the two points is not a further hypothesis but a consequence, and the
reason is again the exact sequence. For `a` with residue zero the element `a t₀` has both branch
residues zero, so it comes from `A`, say `a t₀ = b`; applying the extension and then `ε₁` and
`ε₂` gives `ε₁ t₀ · ε (D a) = ε (D b) = ε₂ t₀ · ε (D a)`, and `ε₁ t₀ - ε₂ t₀ = 1` forces
`ε (D a) = 0`. So every `k`-derivation of `A` already lands in the maximal ideal
(`Stacks.Curves.mem_maximalIdeal_apply_of_exact`), hence so does `D a₂`, hence `ε₁` and `ε₂`
kill `D' t₀` and therefore the whole of the image of `D'`. The `Fixes` conditions are then
immediate.

Only the unit argument needs `A` local, and it needs it twice: for `IsUnit q` and for reading
`ε₁ ∘ algebraMap` as the residue map. Dropping locality means supplying the inverse of
`u = 2 t₀ - c₂` instead of deducing it, and then the whole argument survives at an arbitrary
`k`-algebra and at arbitrary degree:
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_adjoin` is this theorem with
the exact sequence replaced by a set of `A`-algebra generators of `A'` each satisfying a
polynomial relation of invertible formal derivative. That is the form the sheaf-level statement
needs, since `Γ(X, U)` is not local; what it does not supply, and what nothing in the development
supplies, is those generators for a nodal affine curve.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Curves.NodalVectorFields Stacks.DerivationExtension

universe u v w

namespace Stacks.Curves

section Extend

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
variable {L : Type w} [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

omit [IsLocalRing A] [IsLocalization (nonZeroDivisors A) L] in
/-- The image in the localization of the image of `a : A` in the integral closure. -/
private theorem coe_algebraMap_integralClosure (a : A) :
    ((algebraMap A ↥(integralClosure A L) a : ↥(integralClosure A L)) : L) =
      algebraMap A L a := rfl

omit [IsLocalRing A] [IsLocalization (nonZeroDivisors A) L] in
/-- A `k`-scalar multiple in the localization, written multiplicatively. -/
private theorem smul_eq_algebraMap_mul (c : k) (z : L) :
    c • z = algebraMap A L (algebraMap k A c) * z := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k A L]

omit [IsLocalRing A] [IsLocalization (nonZeroDivisors A) L] in
/-- A `k`-algebra map of the integral closure to `k` is the identity on scalars. -/
private theorem apply_algebraMap_algebraMap (ε : ↥(integralClosure A L) →ₐ[k] k) (c : k) :
    ε (algebraMap A ↥(integralClosure A L) (algebraMap k A c)) = c := by
  rw [← IsScalarTower.algebraMap_apply k A ↥(integralClosure A L)]
  exact ε.commutes c

/-- **The extension of a derivation to the normalization at a node, with everything it gives.**
From the exact sequence `0 → A → A' → k → 0` alone: the extension exists, it is the only
derivation of `A'` extending `D`, the original derivation lands in the maximal ideal of `A`, and
the extension is killed by both branch residues. -/
private theorem extend_core
    (ε₁ ε₂ : ↥(integralClosure A L) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A L) a) =
      ε₂ (algebraMap A ↥(integralClosure A L) a))
    (hsurj : Function.Surjective
      fun t : ↥(integralClosure A L) => ε₁ t - ε₂ t)
    (hker : ∀ t : ↥(integralClosure A L), ε₁ t - ε₂ t = 0 ↔
      t ∈ Set.range (algebraMap A ↥(integralClosure A L)))
    (D : Derivation k A A) :
    ∃ D' : Derivation k ↥(integralClosure A L)
        ↥(integralClosure A L),
      (∀ a : A, D' (algebraMap A ↥(integralClosure A L) a) =
          algebraMap A ↥(integralClosure A L) (D a)) ∧
        (∀ a : A, D a ∈ maximalIdeal A) ∧
        (∀ t : ↥(integralClosure A L), ε₁ (D' t) = 0) ∧
        (∀ t : ↥(integralClosure A L), ε₂ (D' t) = 0) ∧
        ∀ E : Derivation k ↥(integralClosure A L)
            ↥(integralClosure A L),
          (∀ a : A, E (algebraMap A ↥(integralClosure A L) a) =
            algebraMap A ↥(integralClosure A L) (D a)) → E = D' := by
  classical
  obtain ⟨t₀, ht₀⟩ := hsurj 1
  have ht : ε₁ t₀ - ε₂ t₀ = 1 := ht₀
  -- the `k`-module decomposition `A' = A ⊕ k t₀`
  have decomp : ∀ t : ↥(integralClosure A L), ∃ (a : A) (c : k),
      t = algebraMap A ↥(integralClosure A L) a +
        algebraMap A ↥(integralClosure A L) (algebraMap k A c) * t₀ := by
    intro t
    have h : ε₁ (t - algebraMap A ↥(integralClosure A L)
          (algebraMap k A (ε₁ t - ε₂ t)) * t₀) -
        ε₂ (t - algebraMap A ↥(integralClosure A L)
          (algebraMap k A (ε₁ t - ε₂ t)) * t₀) = 0 := by
      rw [map_sub ε₁, map_sub ε₂, map_mul, map_mul, apply_algebraMap_algebraMap,
        apply_algebraMap_algebraMap]
      linear_combination (ε₂ t - ε₁ t) * ht
    obtain ⟨a, ha⟩ := (hker _).mp h
    exact ⟨a, ε₁ t - ε₂ t, by rw [ha]; ring⟩
  -- the monic quadratic relation satisfied by `t₀`
  obtain ⟨a₂, c₂, ha₂⟩ := decomp (t₀ * t₀)
  have hc₂ : c₂ = ε₁ t₀ + ε₂ t₀ := by
    have h₁ := congrArg ε₁ ha₂
    have h₂ := congrArg ε₂ ha₂
    rw [map_mul, map_add, map_mul, apply_algebraMap_algebraMap] at h₁
    rw [map_mul, map_add, map_mul, apply_algebraMap_algebraMap] at h₂
    rw [← hres a₂] at h₂
    linear_combination -h₁ + h₂ + (ε₁ t₀ + ε₂ t₀ - c₂) * ht
  -- the element `u = 2 t₀ - c₂`, whose square comes from `A`
  obtain ⟨u, hu⟩ : ∃ u : ↥(integralClosure A L),
      u = t₀ + t₀ -
        algebraMap A ↥(integralClosure A L) (algebraMap k A c₂) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : A, q = 4 * a₂ + algebraMap k A (c₂ ^ 2) := ⟨_, rfl⟩
  have hu2 : u * u = algebraMap A ↥(integralClosure A L) q := by
    have hqc : algebraMap A ↥(integralClosure A L) q =
        4 * algebraMap A ↥(integralClosure A L) a₂ +
          algebraMap A ↥(integralClosure A L) (algebraMap k A c₂) ^ 2 := by
      rw [hq, map_add, map_mul, map_pow, map_ofNat, map_pow]
    rw [hu, hqc]
    linear_combination (4 : ↥(integralClosure A L)) * ha₂
  have hε₁u : ε₁ u = 1 := by
    rw [hu, map_sub, map_add, apply_algebraMap_algebraMap]
    linear_combination ht - hc₂
  -- `q` is a unit of the local ring `A`, hence `u` is a unit of `A'`
  have hεq : ε₁ (algebraMap A ↥(integralClosure A L) q) = 1 := by
    rw [← hu2, map_mul, hε₁u, one_mul]
  have hAsurj : Function.Surjective
      ((ε₁ : ↥(integralClosure A L) →ₐ[k] k).toRingHom.comp
        (algebraMap A ↥(integralClosure A L))) := fun c =>
    ⟨algebraMap k A c, apply_algebraMap_algebraMap ε₁ c⟩
  have hqunit : IsUnit q := by
    refine notMem_maximalIdeal.mp ?_
    rw [← IsLocalRing.ker_eq_maximalIdeal _ hAsurj]
    intro hmem
    have hz : ε₁ (algebraMap A ↥(integralClosure A L) q) = 0 := hmem
    rw [hεq] at hz
    exact one_ne_zero hz
  obtain ⟨w, hw⟩ : ∃ w : ↥(integralClosure A L), u * w = 1 := by
    have hUU : IsUnit (u * u) := hu2 ▸ hqunit.map (algebraMap A _)
    exact (isUnit_of_mul_isUnit_left hUU).exists_right_inv
  -- the extension to the total ring of fractions, Tag 07PE
  let DK := locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L
  have hDKa : ∀ a : A, DK (algebraMap A L a) =
      algebraMap A L (D a) := fun a =>
    locDeriv_algebraMap (D.restrictScalars ℤ) (nonZeroDivisors A) L a
  have hDKk : ∀ c : k, DK (algebraMap A L (algebraMap k A c)) = 0 := by
    intro c
    rw [hDKa, Derivation.map_algebraMap, map_zero]
  -- the value of `DK` at `t₀`
  have hcoe : ∀ (t : ↥(integralClosure A L)) (a : A) (c : k),
      t = algebraMap A ↥(integralClosure A L) a +
        algebraMap A ↥(integralClosure A L) (algebraMap k A c) * t₀ →
      (t : L) = algebraMap A L a + algebraMap A L (algebraMap k A c) * (t₀ : L) := by
    intro t a c h
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_integralClosure] using
      congrArg (fun z : ↥(integralClosure A L) => (z : L)) h
  have hKrel : (t₀ : L) * (t₀ : L) = algebraMap A L a₂ +
      algebraMap A L (algebraMap k A c₂) * (t₀ : L) := by
    rw [← Subalgebra.coe_mul]
    exact hcoe _ _ _ ha₂
  have hDKt₀ : DK (t₀ : L) =
      ((w * algebraMap A ↥(integralClosure A L) (D a₂) :
        ↥(integralClosure A L)) : L) := by
    have hL := congrArg DK hKrel
    rw [DK.leibniz, map_add, DK.leibniz, hDKa, hDKk] at hL
    simp only [smul_eq_mul, mul_zero, add_zero] at hL
    have hucoe : (u : L) = (t₀ : L) + (t₀ : L) -
        algebraMap A L (algebraMap k A c₂) := by
      rw [hu]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_add, coe_algebraMap_integralClosure]
    have hstep : (u : L) * DK (t₀ : L) =
        algebraMap A L (D a₂) := by
      rw [hucoe]
      linear_combination hL
    have hwcoe : (u : L) * (w : L) = 1 := by
      have h := congrArg
        (fun z : ↥(integralClosure A L) => (z : L)) hw
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_one] using h
    simp only [Subalgebra.coe_mul, coe_algebraMap_integralClosure]
    calc DK (t₀ : L)
        = (u : L) * (w : L) * DK (t₀ : L) := by
          rw [hwcoe, one_mul]
      _ = (w : L) * ((u : L) * DK (t₀ : L)) := by ring
      _ = (w : L) * algebraMap A L (D a₂) := by rw [hstep]
  -- `DK` carries `A'` into `A'`
  have hstab : ∀ t : ↥(integralClosure A L),
      DK (t : L) ∈ integralClosure A L := by
    intro t
    obtain ⟨a, c, ha⟩ := decomp t
    have hco := hcoe _ _ _ ha
    have hval : DK (t : L) =
        ((algebraMap A ↥(integralClosure A L) (D a) +
          algebraMap A ↥(integralClosure A L) (algebraMap k A c) *
              (w * algebraMap A ↥(integralClosure A L) (D a₂)) :
          ↥(integralClosure A L)) : L) := by
      rw [hco, map_add, DK.leibniz, hDKa, hDKk, hDKt₀]
      simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_integralClosure,
        smul_eq_mul, mul_zero, add_zero]
    rw [hval]
    exact (algebraMap A ↥(integralClosure A L) (D a) +
      algebraMap A ↥(integralClosure A L) (algebraMap k A c) *
        (w * algebraMap A ↥(integralClosure A L) (D a₂))).2
  -- the restriction of `DK` to `A'`
  let D' : Derivation k ↥(integralClosure A L)
      ↥(integralClosure A L) :=
    { toFun := fun t => ⟨DK (t : L), hstab t⟩
      map_add' := fun t s => by
        apply Subtype.ext
        show DK ((t : L) + (s : L)) =
          DK (t : L) + DK (s : L)
        exact map_add _ _ _
      map_smul' := fun c t => by
        apply Subtype.ext
        show DK (c • (t : L)) = c • DK (t : L)
        rw [smul_eq_algebraMap_mul (A := A), smul_eq_algebraMap_mul (A := A), DK.leibniz, hDKk]
        simp only [smul_eq_mul, mul_zero, add_zero]
      map_one_eq_zero' := by
        apply Subtype.ext
        show DK ((1 : ↥(integralClosure A L)) : L) =
          ((0 : ↥(integralClosure A L)) : L)
        rw [Subalgebra.coe_one, Subalgebra.coe_zero, DK.map_one_eq_zero]
      leibniz' := fun t s => by
        apply Subtype.ext
        show DK ((t : L) * (s : L)) =
          (t : L) * DK (s : L) +
            (s : L) * DK (t : L)
        rw [DK.leibniz]
        simp only [smul_eq_mul] }
  have hD'coe : ∀ t : ↥(integralClosure A L),
      ((D' t : ↥(integralClosure A L)) : L) =
        DK (t : L) := fun _ => rfl
  have hD'ext : ∀ a : A, D' (algebraMap A ↥(integralClosure A L) a) =
      algebraMap A ↥(integralClosure A L) (D a) := by
    intro a
    apply Subtype.ext
    rw [hD'coe, coe_algebraMap_integralClosure, coe_algebraMap_integralClosure, hDKa]
  have hD't₀ : D' t₀ = w * algebraMap A ↥(integralClosure A L) (D a₂) := by
    apply Subtype.ext
    rw [hD'coe, hDKt₀]
  -- the value of any extension on a decomposed element
  have hval : ∀ F : Derivation k ↥(integralClosure A L)
        ↥(integralClosure A L),
      (∀ a : A, F (algebraMap A ↥(integralClosure A L) a) =
        algebraMap A ↥(integralClosure A L) (D a)) →
      ∀ (a : A) (c : k), F (algebraMap A ↥(integralClosure A L) a +
          algebraMap A ↥(integralClosure A L) (algebraMap k A c) * t₀) =
        algebraMap A ↥(integralClosure A L) (D a) +
          algebraMap A ↥(integralClosure A L) (algebraMap k A c) * F t₀ := by
    intro F hF a c
    rw [map_add, hF, F.leibniz, hF, Derivation.map_algebraMap, map_zero]
    simp only [smul_eq_mul, mul_zero, add_zero]
  -- every `k`-derivation of `A` lands in the maximal ideal
  have hkey : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A L) a) = 0 →
      ε₁ (algebraMap A ↥(integralClosure A L) (D a)) = 0 := by
    intro a ha
    have ha' : ε₂ (algebraMap A ↥(integralClosure A L) a) = 0 := by
      rw [← hres a, ha]
    have h0 : ε₁ (algebraMap A ↥(integralClosure A L) a * t₀) -
        ε₂ (algebraMap A ↥(integralClosure A L) a * t₀) = 0 := by
      rw [map_mul, map_mul, ha, ha']
      ring
    obtain ⟨b, hb⟩ := (hker _).mp h0
    have hDb : D' (algebraMap A ↥(integralClosure A L) a * t₀) =
        algebraMap A ↥(integralClosure A L) (D b) := by
      rw [← hb, hD'ext]
    have hDl : D' (algebraMap A ↥(integralClosure A L) a * t₀) =
        algebraMap A ↥(integralClosure A L) a * D' t₀ +
          t₀ * algebraMap A ↥(integralClosure A L) (D a) := by
      rw [D'.leibniz, hD'ext]
      simp only [smul_eq_mul]
    have e : ∀ ε : ↥(integralClosure A L) →ₐ[k] k,
        ε (algebraMap A ↥(integralClosure A L) a) = 0 →
        ε t₀ * ε (algebraMap A ↥(integralClosure A L) (D a)) =
          ε (algebraMap A ↥(integralClosure A L) (D b)) := by
      intro ε hε
      rw [← hDb, hDl, map_add, map_mul, map_mul, hε]
      ring
    have e₁ := e ε₁ ha
    have e₂ := e ε₂ ha'
    rw [← hres (D a), ← hres (D b)] at e₂
    have hfin : (ε₁ t₀ - ε₂ t₀) *
        ε₁ (algebraMap A ↥(integralClosure A L) (D a)) = 0 := by
      linear_combination e₁ - e₂
    rwa [ht, one_mul] at hfin
  have hεD : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A L) (D a)) = 0 := by
    intro a
    have h := hkey (a - algebraMap k A
        (ε₁ (algebraMap A ↥(integralClosure A L) a))) ?_
    · rwa [map_sub, Derivation.map_algebraMap, sub_zero] at h
    · rw [map_sub, map_sub, apply_algebraMap_algebraMap, sub_self]
  have hεD₂ : ∀ a : A, ε₂ (algebraMap A ↥(integralClosure A L) (D a)) = 0 := by
    intro a
    rw [← hres (D a)]
    exact hεD a
  have hmax : ∀ a : A, D a ∈ maximalIdeal A := by
    intro a
    rw [← IsLocalRing.ker_eq_maximalIdeal _ hAsurj]
    exact hεD a
  have hεD' : ∀ ε : ↥(integralClosure A L) →ₐ[k] k,
      (∀ a : A, ε (algebraMap A ↥(integralClosure A L) (D a)) = 0) →
      ∀ t : ↥(integralClosure A L), ε (D' t) = 0 := by
    intro ε hε t
    obtain ⟨a, c, ha⟩ := decomp t
    rw [ha, hval D' hD'ext, map_add, map_mul, hε, hD't₀, map_mul, hε, mul_zero, zero_add,
      mul_zero]
  -- uniqueness: the Leibniz rule forces the value at `t₀`, and `u` is a unit
  have hforced : ∀ E : Derivation k ↥(integralClosure A L)
        ↥(integralClosure A L),
      (∀ a : A, E (algebraMap A ↥(integralClosure A L) a) =
        algebraMap A ↥(integralClosure A L) (D a)) →
      u * E t₀ = algebraMap A ↥(integralClosure A L) (D a₂) := by
    intro E hE
    have h1 : E (t₀ * t₀) = t₀ * E t₀ + t₀ * E t₀ := by
      rw [E.leibniz]
      simp only [smul_eq_mul]
    have h2 : E (t₀ * t₀) = algebraMap A ↥(integralClosure A L) (D a₂) +
        algebraMap A ↥(integralClosure A L) (algebraMap k A c₂) * E t₀ := by
      rw [ha₂]
      exact hval E hE a₂ c₂
    rw [hu]
    linear_combination h2 - h1
  have huniq : ∀ E : Derivation k ↥(integralClosure A L)
        ↥(integralClosure A L),
      (∀ a : A, E (algebraMap A ↥(integralClosure A L) a) =
        algebraMap A ↥(integralClosure A L) (D a)) → E = D' := by
    intro E hE
    have ht₀eq : E t₀ = D' t₀ :=
      calc E t₀ = u * w * E t₀ := by rw [hw, one_mul]
        _ = w * (u * E t₀) := by ring
        _ = w * (u * D' t₀) := by rw [hforced E hE, hforced D' hD'ext]
        _ = u * w * D' t₀ := by ring
        _ = D' t₀ := by rw [hw, one_mul]
    refine Derivation.ext fun t => ?_
    obtain ⟨a, c, ha⟩ := decomp t
    rw [ha, hval E hE, hval D' hD'ext, ht₀eq]
  exact ⟨D', hD'ext, hmax, hεD' ε₁ hεD, hεD' ε₂ hεD₂, huniq⟩

/-- **A derivation of the local ring at a node lands in the maximal ideal.** With the exact
sequence `0 → A → A' → k → 0` of a node available, every `k`-derivation of `A` takes values in
the maximal ideal of `A`: it fixes the node itself, which is the local form of the statement that
a vector field on a curve fixes a singular point. -/
theorem mem_maximalIdeal_apply_of_exact
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hsurj : Function.Surjective
      fun t : ↥(integralClosure A (FractionRing A)) => ε₁ t - ε₂ t)
    (hker : ∀ t : ↥(integralClosure A (FractionRing A)), ε₁ t - ε₂ t = 0 ↔
      t ∈ Set.range (algebraMap A ↥(integralClosure A (FractionRing A))))
    (D : Derivation k A A) (a : A) : D a ∈ maximalIdeal A := by
  obtain ⟨-, -, hmax, -⟩ := extend_core ε₁ ε₂ hres hsurj hker D
  exact hmax a

/-- **A derivation of a node extends uniquely to its normalization, fixing both branch
points.** With the exact sequence `0 → A → A' → k → 0` of a node available — two `k`-algebra maps
`ε₁, ε₂ : A' → k` agreeing on `A`, with surjective difference whose kernel is the image of `A` —
every `k`-derivation of `A` is the restriction of a unique `k`-derivation of `A'`, and that
extension automatically fixes the two points cut out by `ε₁` and `ε₂`.

This is the left-to-right direction of Tag 0E68 in local ring-theoretic form. -/
@[sga "7 X 2.33" "special case"]
theorem existsUnique_extend_integralClosure_of_exact
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hsurj : Function.Surjective
      fun t : ↥(integralClosure A (FractionRing A)) => ε₁ t - ε₂ t)
    (hker : ∀ t : ↥(integralClosure A (FractionRing A)), ε₁ t - ε₂ t = 0 ↔
      t ∈ Set.range (algebraMap A ↥(integralClosure A (FractionRing A))))
    (D : Derivation k A A) :
    ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      (∀ a : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
          algebraMap A ↥(integralClosure A (FractionRing A)) (D a)) ∧
        NodalVectorFields.Fixes ε₁ D' ∧ NodalVectorFields.Fixes ε₂ D' := by
  obtain ⟨D', hext, -, h₁, h₂, huniq⟩ := extend_core ε₁ ε₂ hres hsurj hker D
  exact ⟨D', ⟨hext, fun t _ => h₁ t, fun t _ => h₂ t⟩, fun E hE => huniq E hE.1⟩

end Extend

section Node

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [Algebra k A]

/-- **A derivation of a nodal local algebra lands in its maximal ideal.** For `A` a nodal local
`k`-algebra whose normalization carries two distinct `k`-algebra maps to `k` agreeing on `A`,
every `k`-derivation of `A` takes values in the maximal ideal: a vector field fixes the node. -/
theorem mem_maximalIdeal_apply_of_isNodalAlgebra (hA : IsNodalAlgebra k A)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hne : ε₁ ≠ ε₂) (D : Derivation k A A) (a : A) : D a ∈ maximalIdeal A := by
  obtain ⟨-, hsurj, hker⟩ := exact_integralClosure_of_isNodalAlgebra k A hA ε₁ ε₂ hres hne
  exact mem_maximalIdeal_apply_of_exact ε₁ ε₂ hres hsurj hker D a

/-- **The left-to-right direction of Tag 0E68 in local ring-theoretic form.** Let `A` be a nodal
local algebra over `k` with normalization `A' = integralClosure A (FractionRing A)`, and let
`ε₁ ≠ ε₂` be two `k`-algebra maps `A' → k` agreeing on the image of `A` — the residues at the two
points of the normalization above the node. Then every `k`-derivation of `A` is the restriction
of a unique `k`-derivation of `A'`, and that extension fixes the two points.

This is the step "`𝒪_{X^ν, x'} = k + (u)`, so `D` extends" of the proof of Tag 0E68, with the
semilocal normalization in place of the product of the two branch rings and with the extension's
fixing of the two points proved rather than assumed. -/
@[sga "7 X 2.33" "special case"]
theorem existsUnique_extend_integralClosure_of_isNodalAlgebra (hA : IsNodalAlgebra k A)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hne : ε₁ ≠ ε₂) (D : Derivation k A A) :
    ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      (∀ a : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
          algebraMap A ↥(integralClosure A (FractionRing A)) (D a)) ∧
        NodalVectorFields.Fixes ε₁ D' ∧ NodalVectorFields.Fixes ε₂ D' := by
  obtain ⟨-, hsurj, hker⟩ := exact_integralClosure_of_isNodalAlgebra k A hA ε₁ ε₂ hres hne
  exact existsUnique_extend_integralClosure_of_exact ε₁ ε₂ hres hsurj hker D

end Node

end Stacks.Curves

end
