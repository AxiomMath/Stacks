module

public import StacksFrontier.Algebra.Module.CharacterModule.MulOpposite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Character modules of finite modules

Let `R` be a ring, not necessarily commutative, and `A` a left `R`-module. Its character module
`A^∨ = Hom_ℤ(A, ℚ/ℤ)` (Mathlib's `CharacterModule A`) is a left `Rᵐᵒᵖ`-module
(`CharacterModule.MulOppositeAction.moduleMulOpposite`). This file proves, in arbitrary
universes, the facts about `A ↦ A^∨` needed to dualize finite modules:

* if `A` is finite then so is `A^∨`, with the same number of elements
  (`CharacterModule.natCard_eq`);
* if `A` is finite, evaluation `A → (A^∨)^∨` is an isomorphism, `R`-linear for a left `R`-module
  and `Rᵐᵒᵖ`-linear for a left `Rᵐᵒᵖ`-module (`CharacterModule.evalEquiv`,
  `CharacterModule.evalEquivOfMulOpposite`);
* characters of a finite product are the product of the characters
  (`CharacterModule.piEquiv`);
* a finite abelian group is (non-canonically) isomorphic to its character group
  (`CharacterModule.nonempty_addEquiv`).

Exactness of `A ↦ A^∨` holds for arbitrary groups and is in `MulOpposite.lean`
(`CharacterModule.exact_comp_of_exact`).

## Implementation notes

The count `#A^∨ = #A` is by dévissage: for a cyclic subgroup `C = ⟨a⟩` of order `m` a character
of `C` is determined by its value at `a`, an `m`-torsion point of `ℚ/ℤ`, of which there are at most
`m`; a character of `A` vanishing on `C` is one of `A/C`. Hence `#A^∨ ≤ #(A/C)^∨ · #C^∨ ≤ #A` by
induction, and `#A ≤ #(A^∨)^∨ ≤ #A^∨` because evaluation is injective.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CharacterModule

section Finite

variable (A : Type v) [AddCommGroup A]

/-- A character of a finite group is killed by the order of the group. -/
lemma natCard_nsmul_apply [Finite A] (c : CharacterModule A) (a : A) : Nat.card A • c a = 0 := by
  rw [← map_nsmul, card_nsmul_eq_zero', map_zero]

/-- **The character module of a finite group is finite**: a character takes values in the
`#A`-torsion of `ℚ/ℤ`, which is finite. -/
instance finite [Finite A] : Finite (CharacterModule A) := by
  have hn : 0 < Nat.card A := Nat.card_pos
  let S := {x : AddCircle (1 : ℚ) | Nat.card A • x = 0}
  have : Finite S := (AddCircle.finite_torsion (1 : ℚ) hn).to_subtype
  refine Finite.of_injective (fun c : CharacterModule A ↦ fun a : A ↦
    (⟨c a, natCard_nsmul_apply A c a⟩ : S)) ?_
  intro c c' hcc'
  ext a
  exact congrArg Subtype.val (congrFun hcc' a)

/-- There are at most `n` points of order dividing `n` in `ℚ/ℤ`. -/
lemma natCard_torsion_le (n : ℕ) (hn : 0 < n) :
    Nat.card {x : AddCircle (1 : ℚ) | n • x = 0} ≤ n := by
  have hsurj : Function.Surjective (fun m : Fin n ↦
      (⟨((m : ℚ) / n * 1 : ℚ), by
        rw [Set.mem_ofPred_eq, AddCircle.nsmul_eq_zero_iff hn]
        exact ⟨m, m.2, rfl⟩⟩ : {x : AddCircle (1 : ℚ) | n • x = 0})) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, hm, rfl⟩ := (AddCircle.nsmul_eq_zero_iff hn).mp hx
    exact ⟨⟨m, hm⟩, rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_fin] at this

/-- A cyclic group of order `m` has at most `m` characters: a character is determined by its
value at the generator, a point of order dividing `m` of `ℚ/ℤ`. -/
lemma natCard_characterModule_zmultiples_le [Finite A] (a : A) :
    Nat.card (CharacterModule (AddSubgroup.zmultiples a)) ≤ addOrderOf a := by
  let g : AddSubgroup.zmultiples a := ⟨a, AddSubgroup.mem_zmultiples a⟩
  have hm : 0 < Nat.card (AddSubgroup.zmultiples a) := Nat.card_pos
  let ev : CharacterModule (AddSubgroup.zmultiples a) →
      {x : AddCircle (1 : ℚ) | Nat.card (AddSubgroup.zmultiples a) • x = 0} := fun c ↦
    ⟨c g, natCard_nsmul_apply _ c g⟩
  have hinj : Function.Injective ev := by
    intro c c' hcc'
    have h1 : c g = c' g := congrArg Subtype.val hcc'
    ext ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    have : (⟨k • a, hy⟩ : AddSubgroup.zmultiples a) = k • g := rfl
    rw [this, map_zsmul, map_zsmul, h1]
  have : Finite {x : AddCircle (1 : ℚ) | Nat.card (AddSubgroup.zmultiples a) • x = 0} :=
    (AddCircle.finite_torsion (1 : ℚ) hm).to_subtype
  rw [← Nat.card_zmultiples]
  exact (Nat.card_le_card_of_injective ev hinj).trans (natCard_torsion_le _ hm)

/-- **`#A^∨ ≤ #A`** for a finite group `A`, by dévissage along a cyclic subgroup. -/
theorem natCard_le [Finite A] : Nat.card (CharacterModule A) ≤ Nat.card A := by
  induction h : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  subst h
  by_cases hA : Subsingleton A
  · have : Subsingleton (CharacterModule A) := ⟨fun c c' ↦ by
      ext a
      rw [Subsingleton.elim a 0, map_zero, map_zero]⟩
    rw [Nat.card_unique (α := A)]
    exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hA ⟨fun x y ↦ (hcon x).trans (hcon y).symm⟩
  let C := AddSubgroup.zmultiples a
  -- restriction of characters to `C`
  let res : CharacterModule A →+ CharacterModule C :=
    { toFun := fun c ↦ c.comp C.subtype
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  -- a character vanishing on `C` is a character of `A ⧸ C`
  let toQ : res.ker → CharacterModule (A ⧸ C) := fun c ↦
    QuotientAddGroup.lift C c.1 (fun x hx ↦ by
      have := DFunLike.congr_fun c.2 ⟨x, hx⟩
      exact this)
  have htoQ : Function.Injective toQ := by
    intro c c' hcc'
    ext x
    exact DFunLike.congr_fun hcc' (QuotientAddGroup.mk x)
  have hcardA : Nat.card A = Nat.card (A ⧸ C) * Nat.card C :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C
  have hC : 1 < Nat.card C := by
    rw [Nat.card_zmultiples]
    exact Nat.lt_of_le_of_ne (addOrderOf_pos a)
      (fun h ↦ ha (AddMonoid.addOrderOf_eq_one_iff.mp h.symm))
  have hQ : Nat.card (A ⧸ C) < Nat.card A := by
    rw [hcardA]
    exact lt_mul_of_one_lt_right Nat.card_pos hC
  have hQdual : Nat.card (CharacterModule (A ⧸ C)) ≤ Nat.card (A ⧸ C) := ih _ hQ _ rfl
  have hsplit : Nat.card (CharacterModule A) = Nat.card res.ker * Nat.card res.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup res.ker, mul_comm,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange res).toEquiv]
  have hker : Nat.card res.ker ≤ Nat.card (CharacterModule (A ⧸ C)) :=
    Nat.card_le_card_of_injective toQ htoQ
  have hrange : Nat.card res.range ≤ Nat.card (CharacterModule C) :=
    Nat.card_le_card_of_injective (fun x : res.range ↦ (x : CharacterModule C))
      Subtype.val_injective
  have hCdual : Nat.card (CharacterModule C) ≤ Nat.card C := by
    rw [Nat.card_zmultiples]
    exact natCard_characterModule_zmultiples_le A a
  rw [hsplit, hcardA]
  exact Nat.mul_le_mul (hker.trans hQdual) (hrange.trans hCdual)

/-- **`#A^∨ = #A`** for a finite group `A`. -/
theorem natCard_eq [Finite A] : Nat.card (CharacterModule A) = Nat.card A := by
  refine le_antisymm (natCard_le A) ?_
  calc Nat.card A ≤ Nat.card (CharacterModule (CharacterModule A)) :=
        Nat.card_le_card_of_injective _ (eval_injective A)
    _ ≤ Nat.card (CharacterModule A) := natCard_le _

/-- Evaluation into the double character module of a finite group is bijective. -/
theorem eval_bijective [Finite A] :
    Function.Bijective (AddMonoidHom.eval : A →+ CharacterModule (CharacterModule A)) := by
  have : Finite ((A →+ AddCircle (1 : ℚ)) →+ AddCircle (1 : ℚ)) :=
    inferInstanceAs (Finite (CharacterModule (CharacterModule A)))
  refine (eval_injective A).bijective_of_nat_card_le ?_
  change Nat.card (CharacterModule (CharacterModule A)) ≤ Nat.card A
  rw [natCard_eq, natCard_eq]

open scoped MulOppositeAction

variable (R : Type u) [Ring R]

/-- **Pontryagin duality for a finite left `R`-module**: evaluation `A ≃ₗ[R] (A^∨)^∨`. -/
noncomputable def evalEquiv [Module R A] [Finite A] :
    A ≃ₗ[R] CharacterModule (CharacterModule A) :=
  LinearEquiv.ofBijective (evalMulOpposite R A) (eval_bijective A)

/-- `evalEquiv A R a` is evaluation at `a`, the character `c ↦ c a` of `A^∨`. -/
@[simp]
lemma evalEquiv_apply [Module R A] [Finite A] (a : A) (c : CharacterModule A) :
    evalEquiv A R a c = c a :=
  rfl

/-- **Pontryagin duality for a finite left `Rᵐᵒᵖ`-module**: evaluation
`A ≃ₗ[Rᵐᵒᵖ] (A^∨)^∨`. -/
noncomputable def evalEquivOfMulOpposite [Module Rᵐᵒᵖ A] [Finite A] :
    A ≃ₗ[Rᵐᵒᵖ] CharacterModule (CharacterModule A) :=
  LinearEquiv.ofBijective (evalOfMulOpposite R A) (eval_bijective A)

/-- `evalEquivOfMulOpposite A R a` is evaluation at `a`, the character `c ↦ c a` of `A^∨`. -/
@[simp]
lemma evalEquivOfMulOpposite_apply [Module Rᵐᵒᵖ A] [Finite A] (a : A) (c : CharacterModule A) :
    evalEquivOfMulOpposite A R a c = c a :=
  rfl

end Finite

section Products

open scoped MulOppositeAction

variable (R : Type u) [Ring R]

/-- **Characters of a finite product**: `(Π i, A i)^∨ ≃ (Π i, (A i)^∨)`,
`c ↦ (i ↦ c ∘ single i)`, `Rᵐᵒᵖ`-linear for left `R`-modules `A i`. -/
noncomputable def piEquiv (ι : Type*) [Finite ι] [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    CharacterModule (Π i, A i) ≃ₗ[Rᵐᵒᵖ] (Π i, CharacterModule (A i)) :=
  letI : Fintype ι := Fintype.ofFinite ι
  { toFun := fun c i ↦ dualMulOpposite (LinearMap.single R A i) c
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun r c ↦ funext fun i ↦
      map_smul (dualMulOpposite (LinearMap.single R A i)) r c
    invFun := fun φ ↦ ∑ i, dualMulOpposite (LinearMap.proj (R := R) (φ := A) i) (φ i)
    left_inv := fun c ↦ DFunLike.ext _ _ fun f ↦ by
      change (∑ i, dualMulOpposite (LinearMap.proj (R := R) (φ := A) i)
        (dualMulOpposite (LinearMap.single R A i) c)) f = c f
      refine (AddMonoidHom.finsetSum_apply _ _ f).trans ?_
      change ∑ i, c (Pi.single i (f i)) = c f
      rw [← map_sum, Finset.univ_sum_single]
    right_inv := fun φ ↦ funext fun i ↦ DFunLike.ext _ _ fun a ↦ by
      change (∑ j, dualMulOpposite (LinearMap.proj (R := R) (φ := A) j) (φ j))
        (Pi.single i a) = φ i a
      refine (AddMonoidHom.finsetSum_apply _ _ _).trans ?_
      rw [Finset.sum_eq_single i]
      · change φ i ((Pi.single i a : Π j, A j) i) = φ i a
        rw [Pi.single_eq_same]
      · intro j _ hj
        change φ j ((Pi.single i a : Π j, A j) j) = 0
        rw [Pi.single_eq_of_ne hj, map_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h }

/-- The `i`-th component of `piEquiv R ι A c` is the character `a ↦ c (Pi.single i a)`. -/
lemma piEquiv_apply (ι : Type*) [Finite ι] [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (c : CharacterModule (Π i, A i)) (i : ι)
    (a : A i) : piEquiv R ι A c i a = c (Pi.single i a) :=
  rfl

end Products

section SelfDual

open scoped MulOppositeAction

/-- The character `x ↦ x / m` of `ℤ/m`. -/
def zmodCharacter (m : ℕ) : CharacterModule (ZMod m) :=
  ZMod.lift m ⟨zmultiplesHom (AddCircle (1 : ℚ)) (((m : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)), by
    change ((m : ℤ) • (((m : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ))) = 0
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · rw [← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast,
        mul_inv_cancel₀ (by exact_mod_cast h.ne'), AddCircle.coe_period]⟩

/-- The character `zmodCharacter m` sends `1` to the class of `1 / m` in `ℚ/ℤ`. -/
lemma zmodCharacter_one (m : ℕ) :
    zmodCharacter m 1 = (((m : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← Int.cast_one (R := ZMod m)]
  exact (ZMod.lift_coe m _ 1).trans (one_zsmul _)

/-- `k ↦ k · (x ↦ x / m)`, from `ℤ/m` to its characters. -/
def zmodToCharacter (m : ℕ) : ZMod m →+ CharacterModule (ZMod m) :=
  ZMod.lift m ⟨zmultiplesHom (CharacterModule (ZMod m)) (zmodCharacter m), by
    change (m : ℤ) • zmodCharacter m = 0
    apply CharacterModule.ext
    intro x
    change (m : ℤ) • zmodCharacter m x = 0
    rw [← map_zsmul, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, map_zero]⟩

/-- `zmodToCharacter m` sends the class of a natural number `k` to `k • zmodCharacter m`. -/
lemma zmodToCharacter_natCast (m : ℕ) (k : ℕ) :
    zmodToCharacter m (k : ZMod m) = k • zmodCharacter m := by
  rw [← Int.cast_natCast (R := ZMod m) k]
  exact (ZMod.lift_coe m _ (k : ℤ)).trans (natCast_zsmul _ _)

/-- **`ℤ/m ≅ (ℤ/m)^∨`** for `m ≠ 0`, `k ↦ (x ↦ kx/m)`. -/
noncomputable def zmodAddEquivCharacterModule (m : ℕ) [NeZero m] :
    ZMod m ≃+ CharacterModule (ZMod m) := by
  refine AddEquiv.ofBijective (zmodToCharacter m) ?_
  have hinj : Function.Injective (zmodToCharacter m) := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    have h0 : (k.val • zmodCharacter m) 1 = 0 := by
      have h := DFunLike.congr_fun hk 1
      rw [← ZMod.natCast_zmod_val k, zmodToCharacter_natCast] at h
      exact h
    have h1 : k.val • (((m : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      rw [← zmodCharacter_one]
      exact h0
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hord : addOrderOf (((m : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) = m := by
      have := AddCircle.addOrderOf_period_div (p := (1 : ℚ)) hm
      rwa [one_div] at this
    have hdvd : m ∣ k.val := by
      have := addOrderOf_dvd_of_nsmul_eq_zero h1
      rwa [hord] at this
    rw [← ZMod.natCast_zmod_val k, ZMod.natCast_eq_zero_iff]
    exact hdvd
  have : Finite (ZMod m) := inferInstance
  refine hinj.bijective_of_nat_card_le ?_
  rw [natCard_eq]

/-- **A finite abelian group is isomorphic to its character group** (non-canonically). -/
theorem nonempty_addEquiv (A : Type v) [AddCommGroup A] [Finite A] :
    Nonempty (A ≃+ CharacterModule A) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  have : ∀ i, NeZero (p i ^ e i) := fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let g : A ≃+ Π i, ZMod (p i ^ e i) :=
    f.trans (DirectSum.linearEquivFunOnFintype ℤ ι fun i => ZMod (p i ^ e i)).toAddEquiv
  let dg : CharacterModule (Π i, ZMod (p i ^ e i)) ≃+ CharacterModule A :=
    { toFun := fun c ↦ c.comp g.toAddMonoidHom
      invFun := fun c ↦ c.comp g.symm.toAddMonoidHom
      left_inv := fun c ↦ DFunLike.ext _ _ fun x ↦ congrArg c (g.apply_symm_apply x)
      right_inv := fun c ↦ DFunLike.ext _ _ fun x ↦ congrArg c (g.symm_apply_apply x)
      map_add' := fun _ _ ↦ rfl }
  exact ⟨g.trans ((AddEquiv.piCongrRight fun i ↦ zmodAddEquivCharacterModule (p i ^ e i)).trans
    ((piEquiv ℤ ι fun i ↦ ZMod (p i ^ e i)).toAddEquiv.symm.trans dg))⟩

end SelfDual


end CharacterModule

end
