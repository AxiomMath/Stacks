module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.Koszul.DualExactness

/-!
# Wedging against a basis of the complementary exterior power

Let `M` be a free module over a commutative ring `R` with a basis `v` indexed by a finite linearly
ordered type `ι`, and let `a + b = #ι`. The wedge product `⋀ᵃ M × ⋀ᵇ M → ⋀ᵃ⁺ᵇ M` lands in the top
exterior power, which is free of rank one, and this file proves that it is a perfect pairing in
the form

`⋀ᵃ M ⟶ (powersetCard ι b → ⋀ᵃ⁺ᵇ M)`, `x ↦ (s ↦ x ∧ e_s)`,

is bijective, where `e_s` is the basis wedge of `⋀ᵇ M` at the `b`-element subset `s`. On the basis
of `⋀ᵃ M` the map is `e_t ↦ ±(Pi.single tᶜ e_⊤)`, a basis up to signs and a reindexing by
complements.

This is the module-theoretic input of the isomorphism `⋀^{d - p} F ≅ SheafHom(⋀^p F, ⋀^d F)` for a
locally free sheaf of modules `F` of rank `d`, which the proof of [Stacks, Tag 0FW4] uses for
`F = Ω_{X/k}`. `Koszul.wedgePairing_bijective` is the same statement for the standard basis of
`Rⁿ` with the top power identified with `R`.

## Main definitions

* `exteriorPower.wedgeBasisMap`: the map `x ↦ (s ↦ x ∧ e_s)`.

## Main results

* `exteriorPower.wedgeBasisMap_basis`: its value on the basis wedges.
* `exteriorPower.wedgeBasisMap_bijective`: it is bijective.

## References

* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
-/

@[expose] public section

open Set Set.powersetCard

namespace exteriorPower

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder ι]

/-- **Wedging against the basis of `⋀ᵇ M`.** For a basis `v` of `M`, the map
`⋀ᵃ M → (powersetCard ι b → ⋀ᵃ⁺ᵇ M)` sending `x` to the family `s ↦ x ∧ e_s` of its wedges with
the basis wedges of `⋀ᵇ M`. -/
noncomputable def wedgeBasisMap (v : Module.Basis ι R M) (a b : ℕ) :
    ⋀[R]^a M →ₗ[R] (powersetCard ι b → ⋀[R]^(a + b) M) :=
  LinearMap.pi fun s => (wedgeMul a b).flip (v.exteriorPower b s)

/-- The component of `wedgeBasisMap v a b x` at `s` is the wedge of `x` with the basis wedge
`e_s`. -/
@[simp]
theorem wedgeBasisMap_apply (v : Module.Basis ι R M) (a b : ℕ) (x : ⋀[R]^a M)
    (s : powersetCard ι b) :
    wedgeBasisMap v a b x s = wedgeMul a b x (v.exteriorPower b s) :=
  rfl

/-- **The wedge of two basis wedges** is the sign of the shuffle sorting `t ⊔ s` times the basis
wedge of `t ∪ s` when `t` and `s` are disjoint, and `0` otherwise. -/
theorem wedgeBasisMap_basis (v : Module.Basis ι R M) {a b : ℕ} (t : powersetCard ι a)
    (s : powersetCard ι b) :
    wedgeBasisMap v a b (v.exteriorPower a t) s =
      if h : Disjoint t.val s.val then
        (permOfDisjoint h).sign • v.exteriorPower (a + b) (disjUnion h)
      else 0 := by
  rw [wedgeBasisMap_apply]
  apply Subtype.ext
  rw [wedgeMul_apply_coe, exteriorPower.basis_apply, exteriorPower.basis_apply]
  by_cases h : Disjoint t.val s.val
  · rw [dite_eq_left h, Submodule.coe_smul_of_tower, exteriorPower.basis_apply]
    simp only [exteriorPower.ιMulti_family_apply_coe]
    exact ExteriorAlgebra.ιMulti_family_mul_of_disjoint R _ t s h
  · rw [dite_eq_right h]
    simp only [exteriorPower.ιMulti_family_apply_coe, Submodule.coe_zero]
    exact ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint R _ t s h

variable [Fintype ι]

omit [LinearOrder ι] in
/-- There is exactly one subset of `ι` with `#ι` elements. -/
theorem subsingleton_powersetCard_card {n : ℕ} (hn : n = Fintype.card ι) :
    Subsingleton (powersetCard ι n) :=
  ⟨fun x y => Subtype.ext ((Finset.eq_univ_of_card _ (by rw [card_eq x, hn])).trans
    (Finset.eq_univ_of_card _ (by rw [card_eq y, hn])).symm)⟩

/-- **The wedge pairing against a basis is perfect.** If `M` has a basis indexed by a finite
linearly ordered type `ι` and `a + b = #ι`, then `x ↦ (s ↦ x ∧ e_s)` is a bijection from `⋀ᵃ M`
onto the families of top-degree forms indexed by the `b`-element subsets of `ι`. It sends the
basis wedge `e_t` to a sign times the family supported at the complement of `t`, hence a basis to
a basis. -/
theorem wedgeBasisMap_bijective (v : Module.Basis ι R M) {a b : ℕ}
    (hab : a + b = Fintype.card ι) :
    Function.Bijective (wedgeBasisMap v a b) := by
  classical
  have := subsingleton_powersetCard_card (ι := ι) hab
  have hd : ∀ t : powersetCard ι a, Disjoint t.val ((compl hab).symm t).val := fun t =>
    disjoint_compl_right
  have : Unique (powersetCard ι (a + b)) :=
    { default := ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, hab]⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  let eI : (Σ _ : powersetCard ι b, powersetCard ι (a + b)) ≃ powersetCard ι a :=
    (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodUnique _ _).trans (compl hab))
  let w : powersetCard ι a → Rˣ := fun t =>
    Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign (permOfDisjoint (hd t)))
  let B : Module.Basis (powersetCard ι a) R (powersetCard ι b → ⋀[R]^(a + b) M) :=
    ((Pi.basis fun _ : powersetCard ι b => v.exteriorPower (a + b)).reindex eI).unitsSMul w
  have key : wedgeBasisMap v a b =
      ((v.exteriorPower a).equiv B (Equiv.refl _)).toLinearMap := by
    refine (v.exteriorPower a).ext fun t => funext fun s => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, wedgeBasisMap_basis,
      Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, Pi.smul_apply]
    have he : eI.symm t = ⟨(compl hab).symm t, default⟩ := rfl
    rw [he, Pi.basis_apply]
    by_cases hs : s = (compl hab).symm t
    · subst hs
      rw [dite_eq_left (hd t), Pi.single_eq_same, Subsingleton.elim (disjUnion (hd t)) default,
        Units.smul_def, Units.smul_def]
      simp [w, Int.cast_smul_eq_zsmul]
    · have hnd : ¬Disjoint t.val s.val := fun h =>
        hs (by rw [(disjoint_iff_eq_compl hab (s := t) (t := s)).1 h, Equiv.symm_apply_apply])
      rw [dite_eq_right hnd, Pi.single_eq_of_ne hs, smul_zero]
  rw [key]
  exact LinearEquiv.bijective _

end exteriorPower
