module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.Fintype.Option
public import Mathlib.RingTheory.Localization.Integer
public import StacksFrontier.AlgebraicGeometry.Properties.DenseRestriction

/-!
# The ideal of denominators of a family of sections on a dense open subset

Let `Y` be a scheme, `Ω` an open subset of `Y` and `c : ι → Γ(Y, Ω)` a family of sections of the
structure sheaf over `Ω`. The *ideal of denominators* of `c` over an open set `W` consists of the
sections `ρ` over `W` for which every product `c i * ρ`, which a priori lives only on `W ⊓ Ω`,
is the restriction of a section over the whole of `W`.

## Main definitions

* `Stacks.DenseDenominators.denom`: the ideal of denominators of `c` over an open set.

## Main results

* `Stacks.DenseDenominators.denom_res`: the ideal of denominators is compatible with restriction.
* `Stacks.DenseDenominators.denom_eq_top`: over an open subset of `Ω` every section is a
  denominator.
* `Stacks.DenseDenominators.exists_pow_mul_eq_resHom_of_mem_denom`: **clearing denominators**. On a
  reduced scheme in which `Ω` is dense, a denominator over the basic open set of a section `r` of
  an affine open becomes, after multiplication by a power of `r`, the restriction of a denominator
  over the affine open itself.

## Implementation notes

The ideal of denominators is defined by an existential statement — "the product extends" — and not
as the image of a map, so no choice of extension is made. Nothing in the definition needs `Ω` dense
or `Y` reduced.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

namespace Stacks.DenseDenominators

variable {Y : Scheme.{u}}

/-- Restriction of sections of the structure sheaf along an inclusion of opens, as a ring
homomorphism. -/
abbrev resHom {W V : Y.Opens} (h : V ≤ W) : Γ(Y, W) →+* Γ(Y, V) :=
  (Y.presheaf.map (homOfLE h).op).hom

/-- Restriction along an inclusion of opens, followed by restriction along a further inclusion,
is restriction along the composite. -/
lemma resHom_resHom {W V U : Y.Opens} (h : V ≤ W) (h' : U ≤ V) (s : Γ(Y, W)) :
    resHom h' (resHom h s) = resHom (h'.trans h) s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction along the identity inclusion is the identity. -/
lemma resHom_self {W : Y.Opens} (s : Γ(Y, W)) : resHom (le_refl W) s = s := by
  show (Y.presheaf.map (homOfLE (le_refl W)).op).hom s = s
  rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, Y.presheaf.map_id]
  rfl

/-- Restriction along any proof that an open subset is contained in itself is the identity. -/
lemma resHom_self' {W : Y.Opens} (h : W ≤ W) (s : Γ(Y, W)) : resHom h s = s := resHom_self s

variable {Ω : Y.Opens} {ι : Type v}

/-- Restricting a section over `W` to `W ⊓ Ω` and then to `V ⊓ Ω` is the same as restricting it to
`V` and then to `V ⊓ Ω`. -/
lemma resHom_inf_left_comm {V W : Y.Opens} (h : V ≤ W) (s : Γ(Y, W)) :
    resHom (inf_le_inf h (le_refl Ω)) (resHom (inf_le_left : W ⊓ Ω ≤ W) s)
      = resHom (inf_le_left : V ⊓ Ω ≤ V) (resHom h s) := by
  rw [resHom_resHom, resHom_resHom]

/-- Restricting a section over `Ω` to `W ⊓ Ω` and then to `V ⊓ Ω` is the same as restricting it to
`V ⊓ Ω` directly. -/
lemma resHom_inf_right_comm {V W : Y.Opens} (h : V ≤ W) (s : Γ(Y, Ω)) :
    resHom (inf_le_inf h (le_refl Ω)) (resHom (inf_le_right : W ⊓ Ω ≤ Ω) s)
      = resHom (inf_le_right : V ⊓ Ω ≤ Ω) s := by
  rw [resHom_resHom]

/-- The **ideal of denominators** over `W` of a family `c` of sections over `Ω`: the sections
`ρ` over `W` such that, for every `i`, the product of `c i` with `ρ` — which is defined over
`W ⊓ Ω` — is the restriction of a section over `W`. -/
def denom (c : ι → Γ(Y, Ω)) (W : Y.Opens) : Ideal Γ(Y, W) where
  carrier := {ρ | ∀ i, ∃ s : Γ(Y, W), resHom (inf_le_left : W ⊓ Ω ≤ W) s =
    resHom (inf_le_right : W ⊓ Ω ≤ Ω) (c i) * resHom (inf_le_left : W ⊓ Ω ≤ W) ρ}
  add_mem' {ρ σ} hρ hσ i := by
    obtain ⟨s, hs⟩ := hρ i
    obtain ⟨t, ht⟩ := hσ i
    refine ⟨s + t, ?_⟩
    rw [map_add, hs, ht, map_add, mul_add]
  zero_mem' i := ⟨0, by rw [map_zero, mul_zero]⟩
  smul_mem' a ρ hρ i := by
    obtain ⟨s, hs⟩ := hρ i
    refine ⟨a * s, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, hs]
    ring

/-- Membership in the ideal of denominators, unfolded. -/
lemma mem_denom_iff (c : ι → Γ(Y, Ω)) (W : Y.Opens) (ρ : Γ(Y, W)) :
    ρ ∈ denom c W ↔ ∀ i, ∃ s : Γ(Y, W), resHom (inf_le_left : W ⊓ Ω ≤ W) s =
      resHom (inf_le_right : W ⊓ Ω ≤ Ω) (c i) * resHom (inf_le_left : W ⊓ Ω ≤ W) ρ := Iff.rfl

/-- The ideal of denominators is compatible with restriction. -/
lemma denom_res (c : ι → Γ(Y, Ω)) {V W : Y.Opens} (h : V ≤ W) {ρ : Γ(Y, W)}
    (hρ : ρ ∈ denom c W) : resHom h ρ ∈ denom c V := by
  intro i
  obtain ⟨s, hs⟩ := hρ i
  refine ⟨resHom h s, ?_⟩
  have hres := congrArg (resHom (inf_le_inf h (le_refl Ω))) hs
  rw [map_mul, resHom_inf_left_comm h, resHom_inf_right_comm h, resHom_inf_left_comm h] at hres
  exact hres

/-- Over an open contained in `Ω` every section is a denominator. -/
lemma denom_eq_top (c : ι → Γ(Y, Ω)) {W : Y.Opens} (hW : W ≤ Ω) : denom c W = ⊤ := by
  refine eq_top_iff.mpr fun ρ _ i => ⟨resHom hW (c i) * ρ, ?_⟩
  rw [map_mul, resHom_resHom]

/-- The algebra structure making the sections over a basic open set a localization is given by
restriction. -/
lemma algebraMap_basicOpen_eq {U : Y.Opens} (r : Γ(Y, U)) :
    (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen r)) = resHom (Y.basicOpen_le r) :=
  RingHom.algebraMap_toAlgebra _

/-- **Clearing denominators.** On a reduced scheme in which `Ω` is dense, a denominator over the
basic open set of `r` becomes, after multiplication by a power of `r`, the restriction of a
denominator over the affine open itself. -/
theorem exists_pow_mul_eq_resHom_of_mem_denom [IsReduced Y] (hΩ : Dense (Ω : Set Y))
    [Finite ι] (c : ι → Γ(Y, Ω)) {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Y, U))
    (ρ : Γ(Y, Y.basicOpen r)) (hρ : ρ ∈ denom c (Y.basicOpen r)) :
    ∃ (m : ℕ) (ρ' : Γ(Y, U)), ρ' ∈ denom c U ∧
      resHom (Y.basicOpen_le r) ρ' = resHom (Y.basicOpen_le r) r ^ m * ρ := by
  have := hU.isLocalization_basicOpen r
  choose S hS using (mem_denom_iff c (Y.basicOpen r) ρ).mp hρ
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers r)
    (fun j : Option ι => j.elim ρ S)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (b : Γ(Y, U)) r).mp b.2
  have hclear : ∀ j : Option ι, ∃ a : Γ(Y, U),
      resHom (Y.basicOpen_le r) a = resHom (Y.basicOpen_le r) r ^ n * j.elim ρ S := by
    intro j
    obtain ⟨a, ha⟩ := hb j
    refine ⟨a, ?_⟩
    rw [← algebraMap_basicOpen_eq r, ha, Algebra.smul_def, ← hn, map_pow,
      algebraMap_basicOpen_eq]
  choose G hG using hclear
  have hGnone : resHom (Y.basicOpen_le r) (G none) = resHom (Y.basicOpen_le r) r ^ n * ρ :=
    hG none
  have hGsome : ∀ i, resHom (Y.basicOpen_le r) (G (some i))
      = resHom (Y.basicOpen_le r) r ^ n * S i := fun i => hG (some i)
  refine ⟨n + 1, r * G none, fun i => ⟨r * G (some i), ?_⟩, ?_⟩
  · have hd : resHom (inf_le_inf (Y.basicOpen_le r) (le_refl Ω))
        (resHom (inf_le_left : U ⊓ Ω ≤ U) (G (some i))
          - resHom (inf_le_right : U ⊓ Ω ≤ Ω) (c i)
            * resHom (inf_le_left : U ⊓ Ω ≤ U) (G none)) = 0 := by
      rw [map_sub, map_mul, resHom_inf_left_comm (Y.basicOpen_le r),
        resHom_inf_left_comm (Y.basicOpen_le r), resHom_inf_right_comm (Y.basicOpen_le r),
        hGsome i, hGnone]
      simp only [map_mul, map_pow]
      rw [hS i]
      ring
    have hbas : Y.basicOpen ((Y.presheaf.map
        (homOfLE (inf_le_left : U ⊓ Ω ≤ U)).op).hom r) ≤ Y.basicOpen r ⊓ Ω := by
      rw [Scheme.basicOpen_res]
      exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    have hzero := Stacks.DenseRestriction.mul_eq_zero_of_res_eq_zero_of_basicOpen_le
      (inf_le_inf (Y.basicOpen_le r) (le_refl Ω))
      (resHom (inf_le_left : U ⊓ Ω ≤ U) r) _ hbas hd
    rw [map_mul, map_mul]
    linear_combination hzero
  · rw [map_mul, hGnone, pow_succ]
    ring

end Stacks.DenseDenominators

end
