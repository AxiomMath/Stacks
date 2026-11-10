module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nilpotent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Rig.Algebraization.PrincipalIsomorphism
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# Algebraizing a rig-étale algebra by one étale off `V(I)`

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an object of the category of Stacks
0AL4 which is rig-étale over `(A, I)`.  Suppose `B` is already known to be the `I`-adic
completion of *some* finite type `A`-algebra `C`.  Then `C` may be chosen so that
`Spec(C) → Spec(A)` is in addition étale over `Spec(A) ∖ V(I)`: this is the step "by Lemma
0ALQ we may assume `Spec(C) → Spec(A)` is étale over the complement" which occurs in the
proof of **Stacks 0AKA**, and which is also all that separates **Stacks 0AKA** from condition
(8) of **Stacks 0AKG**.

The improvement is `Rig.exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj`
(Stacks 0ALQ part (2)), which replaces `C` by a principal localization `C_g` at an element
`g ∈ 1 + IC`.  What has to be supplied is that this replacement does not disturb the
completion: inverting an element congruent to `1` modulo `IC` changes neither the quotients
`C/(IC)ⁿ` nor therefore the `I`-adic completion.  That is the "small detail omitted" of the
proof of Stacks 0AKG, and it is proved here.

Combined with `Rig.exists_finiteType_algEquiv_of_isRigEtale_principal` (Stacks 0ALS) the
improvement gives condition (8) of Stacks 0AKG over a principal ideal.

## Main results

* `Rig.isUnit_quotientMk_pow_of_sub_one_mem`: an element of `1 + IC` is a unit modulo every
  power of `IC`, its difference from `1` being nilpotent there.
* `Rig.bijective_quotientMap_pow_localizationAway`: for `g ∈ 1 + IC` the canonical map
  `C/(IC)ⁿ → C_g/(IC)ⁿC_g` is bijective, for every `n`.
* `Rig.nonempty_algEquiv_adicCompletion_localizationAway`: hence `C^∧ ≅ (C_g)^∧` as
  `A`-algebras — the completion is unchanged by the localization.
* `Rig.exists_isEtaleOutside_finiteType_algEquiv_of_algEquiv_adicCompletion`: the improvement
  step itself, for an arbitrary ideal `I`: an algebraization of a rig-étale `B` can be chosen
  étale over `Spec(A) ∖ V(I)`.
* `Rig.exists_isEtaleOutside_finiteType_algEquiv_of_isRigEtale_principal`: **Stacks 0AKG**,
  the implication from the equivalent conditions of Stacks 0AJU to condition (8), over a
  principal ideal.

## Implementation notes

The identification of the completions is obtained levelwise:
`Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective` turns bijectivity
of all the maps `C/(IC)ⁿ → C_g/(IC)ⁿC_g` into bijectivity of `C^∧ → (C_g)^∧`, and the ideal
`(IC)·C_g` is the extension `I·C_g` of `I` to `C_g` by `Ideal.map_map`, which is the shape in
which the statements of Stacks 0ALS and 0AKG take the completion.  The resulting ring
isomorphism is an `A`-algebra isomorphism because `adicCompletionMap` commutes with the maps
from the uncompleted rings (`adicCompletionMap_comp_algebraMap`).

Both halves of the levelwise bijectivity use the same element: rig-étaleness is not involved,
only `g - 1 ∈ IC`.  Surjectivity writes an element of `C_g` as `a/gᵏ` by
`IsLocalization.Away.surj` and corrects it by the inverse `u` of `g` modulo `(IC)ⁿ`; injectivity
clears the denominator of a membership in `(IC)ⁿC_g` with
`IsLocalization.mem_map_algebraMap_iff`, removes the resulting annihilator with
`IsLocalization.map_eq_zero_iff`, and divides by the same unit.

Over a general ideal the hypothesis that `B` is *some* completion is not available: it is
Stacks 0AKA, which this library does not carry, and for which this file is the final step
only.  Over a principal ideal it is Stacks 0ALS,
`Rig.exists_finiteType_algEquiv_of_isRigEtale_principal`.

## References

* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0ALS](https://stacks.math.columbia.edu/tag/0ALS)
* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
-/

@[expose] public noncomputable section

universe u v w

namespace Rig

/-! ## Inverting an element congruent to one modulo the ideal -/

section Away

variable {A : Type u} [CommRing A] (I : Ideal A) {C : Type v} [CommRing C] [Algebra A C]

/-- An element of `1 + IC` is a unit modulo every power of `IC`: its difference from `1` lies
in `IC`, hence is nilpotent modulo `(IC)ⁿ`. -/
public theorem isUnit_quotientMk_pow_of_sub_one_mem {g : C}
    (hg : g - 1 ∈ I.map (algebraMap A C)) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) g) := by
  set J := I.map (algebraMap A C)
  have hnil : IsNilpotent (Ideal.Quotient.mk (J ^ n) (g - 1)) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hg n
  have h1 : (1 : C ⧸ J ^ n) + Ideal.Quotient.mk (J ^ n) (g - 1) =
      Ideal.Quotient.mk (J ^ n) g := by
    rw [map_sub, map_one]
    ring
  rw [← h1]
  exact hnil.isUnit_one_add

/-- An inverse modulo `(IC)ⁿ` of an element `g` of `1 + IC`, in the form of an element `u` of `C`
with `(gu)ᵏ - 1 ∈ (IC)ⁿ` for every `k`. -/
private theorem exists_forall_mul_pow_sub_one_mem_pow {g : C}
    (hg : g - 1 ∈ I.map (algebraMap A C)) (n : ℕ) :
    ∃ u : C, ∀ k : ℕ, (g * u) ^ k - 1 ∈ (I.map (algebraMap A C)) ^ n := by
  obtain ⟨v, hv⟩ := (isUnit_quotientMk_pow_of_sub_one_mem I hg n).exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  refine ⟨u, fun k => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_mul, hv, one_pow, map_one,
    sub_self]

/-- If `g - 1 ∈ IC`, then `gᵏ x ∈ (IC)ⁿ` implies `x ∈ (IC)ⁿ`. -/
private theorem mem_pow_of_pow_mul_mem {g : C} (hg : g - 1 ∈ I.map (algebraMap A C))
    {n k : ℕ} {x : C} (hx : g ^ k * x ∈ (I.map (algebraMap A C)) ^ n) :
    x ∈ (I.map (algebraMap A C)) ^ n := by
  obtain ⟨u, hu⟩ := exists_forall_mul_pow_sub_one_mem_pow I hg n
  rw [show x = u ^ k * (g ^ k * x) - ((g * u) ^ k - 1) * x by ring]
  exact Submodule.sub_mem _ (Ideal.mul_mem_left _ _ hx)
    (Ideal.mul_mem_right _ _ (hu k))

/-- For `g - 1 ∈ IC` the canonical map `C/(IC)ⁿ → C_g/(IC)ⁿ C_g` is injective. -/
private theorem injective_quotientMap_pow_localizationAway {g : C}
    (hg : g - 1 ∈ I.map (algebraMap A C)) (n : ℕ) :
    Function.Injective (Ideal.quotientMap
      (((I.map (algebraMap A C)) ^ n).map (algebraMap C (Localization.Away g)))
      (algebraMap C (Localization.Away g)) Ideal.le_comap_map) := by
  intro w₁ w₂ hw
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w₁
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w₂
  rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    ← map_sub] at hw
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  obtain ⟨⟨c, s⟩, hcs⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) (Localization.Away g)).mp hw
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff (s : C) g).mp s.2
  have hzero : algebraMap C (Localization.Away g) ((x - y) * (s : C) - (c : C)) = 0 := by
    rw [map_sub, map_mul, hcs, sub_self]
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g)
    (Localization.Away g) ((x - y) * (s : C) - (c : C))).mp hzero
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff (m : C) g).mp m.2
  refine mem_pow_of_pow_mul_mem I hg (k := i + j) ?_
  have hexp : g ^ (i + j) * (x - y) = (m : C) * ((x - y) * (s : C) - (c : C))
      + (m : C) * (c : C) := by
    rw [← hi, ← hj]
    ring
  rw [hexp, hm, zero_add]
  exact Ideal.mul_mem_left _ _ c.2

/-- For `g - 1 ∈ IC` the canonical map `C/(IC)ⁿ → C_g/(IC)ⁿ C_g` is surjective. -/
private theorem surjective_quotientMap_pow_localizationAway {g : C}
    (hg : g - 1 ∈ I.map (algebraMap A C)) (n : ℕ) :
    Function.Surjective (Ideal.quotientMap
      (((I.map (algebraMap A C)) ^ n).map (algebraMap C (Localization.Away g)))
      (algebraMap C (Localization.Away g)) Ideal.le_comap_map) := by
  set φ := algebraMap C (Localization.Away g)
  obtain ⟨u, hu⟩ := exists_forall_mul_pow_sub_one_mem_pow I hg n
  intro w
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨k, a, hza⟩ := IsLocalization.Away.surj g z
  refine ⟨Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (a * u ^ k), ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hrw : φ (a * u ^ k) - z = z * φ ((g * u) ^ k - 1) := by
    rw [map_sub, map_one, map_mul, map_pow, map_pow, map_mul, ← hza]
    ring
  rw [hrw]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hu k))

/-- **Inverting an element of `1 + IC` does not change the quotients by the powers of `IC`.**
For `g - 1 ∈ IC` the canonical map `C/(IC)ⁿ → C_g/(IC)ⁿ C_g` is bijective, for every `n`.

Surjectivity: an element of `C_g` is `a/gᵏ`, and `g` is invertible modulo `(IC)ⁿ`, so the
class of `a uᵏ` does it, `u` being an inverse of `g` there.  Injectivity: if `x` lands in
`(IC)ⁿ C_g`, then `gᵏ x ∈ (IC)ⁿ` for some `k` after clearing the denominator and the
annihilator of the localization, and dividing by the unit `gᵏ` gives `x ∈ (IC)ⁿ`. -/
public theorem bijective_quotientMap_pow_localizationAway {g : C}
    (hg : g - 1 ∈ I.map (algebraMap A C)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap
      (((I.map (algebraMap A C)) ^ n).map (algebraMap C (Localization.Away g)))
      (algebraMap C (Localization.Away g)) Ideal.le_comap_map) :=
  ⟨injective_quotientMap_pow_localizationAway I hg n,
    surjective_quotientMap_pow_localizationAway I hg n⟩

/-- **Inverting an element of `1 + IC` does not change the `I`-adic completion.** For
`g - 1 ∈ IC` the completion of `C_g` is the completion of `C`, as `A`-algebras.

The map of completions induced by `C → C_g` is bijective because it is bijective on every
level (`Rig.bijective_quotientMap_pow_localizationAway`), and it commutes with the maps from
the uncompleted rings, hence with the structure maps from `A`. -/
public theorem nonempty_algEquiv_adicCompletion_localizationAway {g : C}
    (hg : g - 1 ∈ I.map (algebraMap A C)) :
    Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A (Localization.Away g))) (Localization.Away g)) := by
  have hmap : (I.map (algebraMap A C)).map (algebraMap C (Localization.Away g)) =
      I.map (algebraMap A (Localization.Away g)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [← hmap]
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _
    (Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective
      (algebraMap C (Localization.Away g)) (I.map (algebraMap A C))
      (bijective_quotientMap_pow_localizationAway I hg))) fun a => ?_⟩
  have hcomm := RingHom.congr_fun (adicCompletionMap_comp_algebraMap
    (algebraMap C (Localization.Away g)) (I.map (algebraMap A C))
    ((I.map (algebraMap A C)).map (algebraMap C (Localization.Away g))) le_rfl)
    (algebraMap A C a)
  simp only [RingHom.comp_apply] at hcomm
  change adicCompletionMap (algebraMap C (Localization.Away g)) (I.map (algebraMap A C))
      ((I.map (algebraMap A C)).map (algebraMap C (Localization.Away g))) le_rfl
      (algebraMap A (AdicCompletion (I.map (algebraMap A C)) C) a) = _
  rw [IsScalarTower.algebraMap_apply A C (AdicCompletion (I.map (algebraMap A C)) C), hcomm,
    ← IsScalarTower.algebraMap_apply A C (Localization.Away g),
    ← IsScalarTower.algebraMap_apply A (Localization.Away g)
      (AdicCompletion ((I.map (algebraMap A C)).map (algebraMap C (Localization.Away g)))
        (Localization.Away g))]

end Away

/-! ## The improvement step -/

section Improve

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **An algebraization of a rig-étale algebra can be chosen étale off `V(I)`.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal and `B` an object of the category of Stacks 0AL4 which is
rig-étale over `(A, I)`. If `B` is isomorphic to the `I`-adic completion of a finite type
`A`-algebra `C`, then there is a finite type `A`-algebra `C'` with `Spec(C') → Spec(A)` étale
over `Spec(A) ∖ V(I)` and `B ≅ (C')^∧`.

This is the step "by Lemma 0ALQ we may assume `Spec(C) → Spec(A)` is étale over the
complement" of the proof of Stacks 0AKA: `C'` is a principal localization `C_g` at an element
`g ∈ 1 + IC` produced by Stacks 0ALQ part (2), and the localization does not change the
completion. -/
public theorem exists_isEtaleOutside_finiteType_algEquiv_of_algEquiv_adicCompletion
    {B : AdicFiniteTypeAlgebra.{u, w} A I} (hB : IsRigEtale B)
    {C : Type v} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (e : B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) :
    ∃ (C' : Type v) (_ : CommRing C') (_ : Algebra A C'),
      Algebra.FiniteType A C' ∧ IsEtaleOutside I C' ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C')) C') := by
  have hC : IsRigEtale (adicCompletionObj I (B := C)) := isRigEtale_of_algEquiv e.symm hB
  obtain ⟨g, hg, hetale⟩ :=
    exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj I hC
  obtain ⟨E⟩ := nonempty_algEquiv_adicCompletion_localizationAway I hg
  have hfp : Algebra.FinitePresentation C (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  exact ⟨Localization.Away g, inferInstance, inferInstance,
    Algebra.FiniteType.trans (R := A) (S := C) inferInstance inferInstance, hetale, ⟨e.trans E⟩⟩

/-- **Stacks 0AKG, the equivalent conditions of Stacks 0AJU imply condition (8), over a
principal ideal.** Let `A` be a Noetherian ring and `I = (a)` a principal ideal. Let `B` be an
object of the category of `I`-adically complete `A`-algebras of finite type modulo `I` (Stacks
0AL4) which is rig-étale over `(A, I)`. Then there is a finite type `A`-algebra `C` with
`Spec(C) → Spec(A)` étale over `Spec(A) ∖ V(I)` and an isomorphism `B ≅ C^∧`.

Stacks 0ALS (`Rig.exists_finiteType_algEquiv_of_isRigEtale_principal`) algebraizes `B` over a
principal ideal, and
`Rig.exists_isEtaleOutside_finiteType_algEquiv_of_algEquiv_adicCompletion` improves the
algebraization to one étale off `V(I)`. -/
@[stacks 0AKG "the converse implication, over a PRINCIPAL ideal: the equivalent conditions of \
Stacks 0AJU imply condition (8). Stacks 0ALS algebraizes a rig-étale object over a principal \
ideal and the improvement step above makes the algebraization étale over the complement of \
V(I); that improvement step, \
`Rig.exists_isEtaleOutside_finiteType_algEquiv_of_algEquiv_adicCompletion`, is proved for an \
arbitrary ideal"]
public theorem exists_isEtaleOutside_finiteType_algEquiv_of_isRigEtale_principal
    (hI : I.IsPrincipal) (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigEtale B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧ IsEtaleOutside I C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨C, _, _, hCft, ⟨e⟩⟩ := exists_finiteType_algEquiv_of_isRigEtale_principal hI B hB
  exact exists_isEtaleOutside_finiteType_algEquiv_of_algEquiv_adicCompletion I hB e

end Improve

end Rig

end
