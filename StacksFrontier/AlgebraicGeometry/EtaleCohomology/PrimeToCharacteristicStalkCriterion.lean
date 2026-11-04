module

public import StacksFrontier.AlgebraicGeometry.Etale.RefinedTorsionStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsion prime to `p` on the small étale site is detected on stalks

An abelian sheaf on the small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology` of a
scheme `X` whose stalks at all geometric points are annihilated, elementwise, by positive integers
prime to `p` is of torsion prime to `p`, and conversely.

This is the stalk criterion
`AlgebraicGeometry.SmallEtale.isPrimeToCharacteristicTorsion_iff_forall_etaleStalk`, proved there
for the size-bounded small étale site of a big étale site, transported to the small étale site of
`X`: the condition is the same on both sites
(`AlgebraicGeometry.SmallEtale.isPrimeToCharacteristicTorsion_toEtaleSite_iff`), and the stalks
at a geometric point agree (`AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso`).

For a field `K`, the positive integers prime to the exponential characteristic of `K` are exactly
the positive integers invertible in `K`, so this also reads the condition "the stalks are torsion
of orders invertible in `K`" of [Stacks, Tag 0F1C] as torsion prime to `ringExpChar K`.

## Main results

* `AlgebraicGeometry.isPrimeToCharacteristicTorsion_iff_forall_smallEtaleStalkAb` — the stalk
  criterion for torsion prime to `p` on the small étale site.
* `AlgebraicGeometry.isPrimeToCharacteristicTorsion_ringExpChar_iff_forall_smallEtaleStalkAb` —
  torsion prime to the exponential characteristic of a field `K` is torsion of orders invertible
  in `K` on stalks.

## References

* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Torsion Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-- A positive integer is invertible in a field `K` exactly when it is prime to the exponential
characteristic of `K`. -/
@[sga "3 VIIA 8.4"]
theorem isUnit_natCast_iff_coprime_ringExpChar (K : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    IsUnit (n : K) ↔ n.Coprime (ringExpChar K) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · rw [ringExpChar, max_eq_left hp.one_le, CharP.isUnit_natCast_iff hp, Nat.coprime_comm,
      hp.coprime_iff_not_dvd]
  · have : CharP K 0 := hp ▸ inferInstance
    have : CharZero K := CharP.charP_to_charZero _
    simp only [ringExpChar.eq_one, Nat.coprime_one_right_eq_true, iff_true]
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')

variable {X : Scheme.{u}} (p : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The stalk of an abelian sheaf on the small étale site of `X` at a geometric point is the stalk
of its restriction to the size-bounded small étale site of the big étale site containing `X`. -/
def smallEtaleStalkAbIsoEtaleStalk (t : GeometricPoint X) :
    (smallEtaleStalkAb t.hom).obj F ≅
      etaleStalk (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X) t
        ((sheafToPresheaf _ _).obj
          ((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X
            (BigEtaleSite.contains_containing X) AddCommGrpCat.{u + 1}).inverse.obj F)) :=
  (smallEtaleStalkAb t.hom).mapIso
      ((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X
        (BigEtaleSite.contains_containing X) AddCommGrpCat.{u + 1}).counitIso.app F).symm ≪≫
    smallEtaleStalkAb_sheafEquiv_obj_iso (BigEtaleSite.containing X)
      ⟨X, BigEtaleSite.contains_containing X⟩ t _

/-- An isomorphism of abelian groups carries the property "every element is annihilated by a
member of `N`" across. -/
theorem forall_exists_nsmul_eq_zero_of_iso {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B)
    (N : ℕ → Prop) (h : ∀ x : A, ∃ n : ℕ, N n ∧ n • x = 0) (y : B) :
    ∃ n : ℕ, N n ∧ n • y = 0 := by
  obtain ⟨n, hn, hkill⟩ := h (e.inv y)
  refine ⟨n, hn, ?_⟩
  have hy : e.hom (e.inv y) = y := by
    rw [← CategoryTheory.comp_apply, e.inv_hom_id]
    rfl
  rw [← hy, ← map_nsmul, hkill, map_zero]

/-- **The stalk criterion for torsion prime to `p` on the small étale site.** An abelian sheaf on
the small étale site of `X` is of torsion prime to `p` exactly when every element of every stalk
at a geometric point is annihilated by a positive integer prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_iff_forall_smallEtaleStalkAb :
    IsPrimeToCharacteristicTorsion X.smallEtaleTopology p F ↔
      ∀ (t : GeometricPoint X) (a : ↑((smallEtaleStalkAb t.hom).obj F)),
        ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • a = 0 := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  rw [← SmallEtale.isPrimeToCharacteristicTorsion_toEtaleSite_iff B X hX F p,
    SmallEtale.isPrimeToCharacteristicTorsion_iff_forall_etaleStalk.{u, 0}]
  have key : ∀ {A B : AddCommGrpCat.{u + 1}}, (A ≅ B) →
      (∀ x : A, ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • x = 0) →
        ∀ y : B, ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • y = 0 := fun e h y ↦ by
    simpa [and_assoc] using forall_exists_nsmul_eq_zero_of_iso e
      (fun n ↦ 0 < n ∧ n.Coprime p) (by simpa [and_assoc] using h) y
  exact forall_congr' fun t ↦ ⟨key (smallEtaleStalkAbIsoEtaleStalk F t).symm,
    key (smallEtaleStalkAbIsoEtaleStalk F t)⟩

/-- **Torsion of orders invertible in a field.** For a field `K`, an abelian sheaf on the small
étale site of `X` is of torsion prime to the exponential characteristic of `K` exactly when every
element of every stalk at a geometric point is annihilated by a positive integer invertible
in `K`. -/
theorem isPrimeToCharacteristicTorsion_ringExpChar_iff_forall_smallEtaleStalkAb
    (K : Type*) [Field K] :
    IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar K) F ↔
      ∀ (t : GeometricPoint X) (a : ↑((smallEtaleStalkAb t.hom).obj F)),
        ∃ n : ℕ, 0 < n ∧ IsUnit (n : K) ∧ n • a = 0 := by
  rw [isPrimeToCharacteristicTorsion_iff_forall_smallEtaleStalkAb]
  refine forall₂_congr fun t a ↦ exists_congr fun n ↦ ?_
  exact ⟨fun ⟨hn, hc, h⟩ ↦ ⟨hn, (isUnit_natCast_iff_coprime_ringExpChar K hn).2 hc, h⟩,
    fun ⟨hn, hc, h⟩ ↦ ⟨hn, (isUnit_natCast_iff_coprime_ringExpChar K hn).1 hc, h⟩⟩

end AlgebraicGeometry

end
