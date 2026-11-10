module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequenceOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces

/-!
# Products of Chow cohomology classes vanishing on the members of a finite open cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. Let `X = U_1 ∪ ⋯ ∪ U_m` be a finite open cover and let
`c_1, …, c_m ∈ ∏_p A^p(X)` be total Chow cohomology classes such that `c_j` restricts to zero on
`U_j` (Stacks 0B7F). Then

  `c_1 c_2 ⋯ c_m = 0`.

The proof is by induction on `m`. Let `i : Z ⟶ X` be a closed immersion onto the complement of
`U_m`. On a test scheme `g : T ⟶ X` and a class `α ∈ CH_*(T)`, the class `c_m ∩ α` restricts to
`(c_m|_{U_m}) ∩ (α|_{g^{-1}U_m}) = 0` on `g^{-1} U_m`, so by the localization sequence
(Stacks 02RX) it is the pushforward of a class on `T ×_X Z`. Since a bivariant class commutes with
proper pushforward, the product `c_1 ⋯ c_{m-1}` caps it to the pushforward of the cap product of
its restriction to `Z`; and the restrictions of `c_1, …, c_{m-1}` to `Z` vanish on the members of
the open cover `Z = (U_1 ∩ Z) ∪ ⋯ ∪ (U_{m-1} ∩ Z)`, so their product is zero by induction.

This is the cup-length argument behind the last sentence of Stacks 0FET: on a quasi-compact
scheme, the power sums and the Chern classes of positive degree of a finite locally free module
are nilpotent, because each of them vanishes on the members of a finite open cover trivializing
the module.

## Main results

* `Stacks.Chow.BivariantClass.mulId_eq_zero_of_vanishesOver` — if `a ∈ A^p(X)` vanishes over a
  closed immersion `i : Z ⟶ X` and `b ∈ A^q(X)` vanishes over an open immersion `u : U ⟶ X` whose
  image is the complement of that of `i`, then `a b = 0`.
* `Stacks.Chow.TotalChowClass.mul_eq_zero_of_res_eq_zero_of_range_compl` — the same for total
  classes.
* `Stacks.Chow.TotalChowClass.prod_ofFn_eq_zero_of_res_eq_zero` — the cup-length vanishing: the
  product of total classes `c_1, …, c_m` with `c_j|_{U_j} = 0` for an open cover
  `X = U_1 ∪ ⋯ ∪ U_m` vanishes.
* `Stacks.Chow.TotalChowClass.pow_eq_zero_of_res_eq_zero` — a total class vanishing on every member
  of a finite open cover by `m` members has vanishing `m`-th power.

## References

* [Stacks Project, Tag 0FET](https://stacks.math.columbia.edu/tag/0FET)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Homogeneous

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- **The product of a class vanishing over a closed subscheme and a class vanishing over its
open complement is zero.** Let `i : Z ⟶ X` be a closed immersion and `u : U ⟶ X` an open
immersion with complementary images. If `a ∈ A^p(X)` vanishes over `i` and `b ∈ A^q(X)` vanishes
over `u`, then `a b = 0` in `A^{p+q}(X)`: on a test scheme `g : T ⟶ X` the class `b ∩ α`
restricts to zero on `T ×_X U`, so it is pushed forward from `T ×_X Z` (Stacks 02RX), where `a`
caps to zero. -/
theorem BivariantClass.mulId_eq_zero_of_vanishesOver {p q : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q}
    {Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (u : U ⟶ X) [IsOpenImmersion u]
    (hiu : Set.range i.base = (Set.range u.base)ᶜ) (ha : BivariantClass.VanishesOver a i)
    (hb : BivariantClass.VanishesOver b u) : a.mulId C sX b = 0 := by
  refine BivariantClass.eq_of_idRule_eq C sX _ _ _ fun {T} g _ k α ↦ ?_
  rw [BivariantClass.idRule_zero]
  have cast_zero : ∀ {n n' : ℤ} (_ : n = n') (x : chowGroup C (g ≫ sX) n),
      x ≍ (0 : chowGroup C (g ≫ sX) n') → x = 0 := by
    rintro n _ rfl x hx
    exact eq_of_heq hx
  refine cast_zero (by ring) _ ((BivariantClass.idRule_mulId C sX a b g k α).trans
    (heq_of_eq ?_))
  -- `b ∩ α` restricts to zero on `T ×_X U`
  set β := b.idRule C sX (gysinSystemOfInvertible C) g k α
  have hβ : chowGroupRestrict C (g ≫ sX) ((pullback.snd u g ≫ g) ≫ sX) (pullback.snd u g)
      (by rw [Category.assoc]) (k - q) β = 0 := by
    rw [BivariantClass.idRule_chowGroupRestrict b g (pullback.snd u g) (pullback.snd u g ≫ g)
      rfl k α]
    exact hb.idRule_eq_zero (pullback.fst u g) (pullback.snd u g ≫ g) pullback.condition k _
  -- so it is pushed forward from `T ×_X Z`
  have hcompl : Set.range (pullback.snd i g).base = (Set.range (pullback.snd u g).base)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_compl]
    exact congrArg _ hiu
  obtain ⟨γ, hγ⟩ := (exact_chowPushforward_chowGroupRestrict C (g ≫ sX)
    ((pullback.snd u g ≫ g) ≫ sX) (pullback.snd u g) (by rw [Category.assoc]) (k - q)
    ((pullback.snd i g ≫ g) ≫ sX) (pullback.snd i g) (by rw [Category.assoc]) hcompl β).mp hβ
  rw [← hγ]
  -- where `a` caps to zero
  change a.idRule C sX (gysinSystemOfInvertible C) g (k - q)
    (chowPush C ((pullback.snd i g ≫ g) ≫ sX) (g ≫ sX) (pullback.snd i g)
      (by rw [Category.assoc]) (k - q) γ) = 0
  rw [BivariantClass.idRule_chowPush C _ sX a g (pullback.snd i g) (pullback.snd i g ≫ g) rfl,
    ha.idRule_eq_zero (pullback.fst i g) (pullback.snd i g ≫ g) pullback.condition, map_zero]

end Homogeneous

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- A total class restricts to zero along `z` exactly when each of its components vanishes over
`z`. -/
theorem res_eq_zero_iff_forall_vanishesOver {W : Scheme.{u}} (z : W ⟶ X) [LocallyOfFiniteType z]
    (c : TotalChowClass C sX) :
    res z rfl c = 0 ↔ ∀ n : ℕ, BivariantClass.VanishesOver (c n) z := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ext fun n ↦ ?_⟩
  · rw [← chowCohomologyRestriction_eq_zero_iff_vanishesOver, ← res_rfl_apply, h, zero_apply]
  · rw [res_rfl_apply, zero_apply, chowCohomologyRestriction_eq_zero_iff_vanishesOver]
    exact h n

/-- **The product of a total class vanishing on a closed subscheme and a total class vanishing on
its open complement is zero.** Let `i : Z ⟶ X` be a closed immersion and `u : U ⟶ X` an open
immersion with complementary images. If `c|_Z = 0` and `d|_U = 0`, then `c d = 0`. -/
theorem mul_eq_zero_of_res_eq_zero_of_range_compl {Z U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (u : U ⟶ X) [IsOpenImmersion u]
    (hiu : Set.range i.base = (Set.range u.base)ᶜ)
    {c d : TotalChowClass C sX} (hc : res i rfl c = 0) (hd : res u rfl d = 0) : c * d = 0 := by
  rw [res_eq_zero_iff_forall_vanishesOver] at hc hd
  refine ext fun m ↦ ?_
  rw [mul_apply, zero_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [mulTerm]
  split_ifs
  · rw [BivariantClass.mulId_eq_zero_of_vanishesOver i u hiu (hc (m - j)) (hd j), map_zero]
  · rfl

/-- **Cup-length vanishing.** Let `X = U_1 ∪ ⋯ ∪ U_m` be a finite open cover and let
`c_1, …, c_m` be total Chow cohomology classes of `X` with `c_j|_{U_j} = 0` for every `j`. Then
`c_1 c_2 ⋯ c_m = 0`. -/
theorem prod_ofFn_eq_zero_of_res_eq_zero {m : ℕ} (U : Fin m → X.Opens)
    (hU : ∀ x : X, ∃ j, x ∈ U j) (c : Fin m → TotalChowClass C sX)
    (hc : ∀ j, res (U j).ι rfl (c j) = 0) : (List.ofFn c).prod = 0 := by
  induction m generalizing X with
  | zero =>
    have : IsEmpty X := ⟨fun x ↦ (hU x).elim fun j _ ↦ j.elim0⟩
    exact (subsingleton_of_isEmpty sX).elim _ _
  | succ m ih =>
    -- the reduced closed subscheme on the complement of the last member
    let Zc : TopologicalSpace.Closeds X :=
      ⟨(U (Fin.last m) : Set X)ᶜ, (U (Fin.last m)).isOpen.isClosed_compl⟩
    let i := (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
    have hi : Set.range i.base = (Set.range (U (Fin.last m)).ι.base)ᶜ := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
      rfl
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    refine mul_eq_zero_of_res_eq_zero_of_range_compl i (U (Fin.last m)).ι hi ?_ (hc (Fin.last m))
    rw [map_list_prod, List.map_ofFn]
    refine ih (sX := i ≫ sX) (fun j ↦ i ⁻¹ᵁ U j.castSucc) (fun z ↦ ?_) _ fun j ↦ ?_
    · obtain ⟨j, hj⟩ := hU (i.base z)
      have hz : i.base z ∈ (Set.range (U (Fin.last m)).ι.base)ᶜ := hi ▸ Set.mem_range_self z
      rw [Scheme.Opens.range_ι] at hz
      obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr (fun h ↦ hz (h ▸ hj))
      exact ⟨j', hj⟩
    · change res (i ⁻¹ᵁ U j.castSucc).ι rfl (res i rfl (c j.castSucc)) = 0
      have hs : i ∣_ U j.castSucc ≫ (U j.castSucc).ι ≫ sX = (i ⁻¹ᵁ U j.castSucc).ι ≫ i ≫ sX := by
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      rw [res_res, res_congr (morphismRestrict_ι i (U j.castSucc)).symm _
        (by rw [Category.assoc, hs]), ← res_res (U j.castSucc).ι rfl _ hs, hc, map_zero]

/-- **A total class vanishing on every member of a finite open cover is nilpotent**: its `m`-th
power is zero for a cover by `m` members. -/
theorem pow_eq_zero_of_res_eq_zero {m : ℕ} (U : Fin m → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j)
    (c : TotalChowClass C sX) (hc : ∀ j, res (U j).ι rfl c = 0) : c ^ m = 0 := by
  have h := prod_ofFn_eq_zero_of_res_eq_zero U hU (fun _ ↦ c) hc
  rwa [List.ofFn_const, List.prod_replicate] at h

end TotalChowClass

end Stacks.Chow

end
