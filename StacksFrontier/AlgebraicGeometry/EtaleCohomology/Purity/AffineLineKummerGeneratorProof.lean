module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineKummerOrder
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineStalkCount

/-!
# The Kummer class of the coordinate generates `R¹ j_* μ_N` at the origin of `𝔸¹_k`

For every field `k`, every `N` invertible on `𝐆_m` and every geometric point `x` of `𝐀¹_k` over
the origin, `n ↦ n • (∂ t)_x` is a bijection from `ℤ/N` onto the stalk of `R¹ j_* μ_N` at `x`:
this is `Stacks.EtaleCohomology.Purity.AffineLineKummerGenerator k`
(`Stacks.EtaleCohomology.Purity.affineLineKummerGenerator`), input A1c of relative purity.

The map is injective because `(∂ t)_x` has order exactly `N`
(`Stacks.EtaleCohomology.Purity.dvd_of_nsmul_germ_localKummerClass_eq_zero`: `t^n` is not an
`N`-th power near the origin unless `N ∣ n`, étale locally), and the stalk has exactly `N`
elements (`Stacks.EtaleCohomology.Purity.natCard_stalk_rightDerived_one_rootsOfUnity`).

## Main results

* `Stacks.EtaleCohomology.Purity.affineLineKummerGenerator`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  TopologicalSpace Opposite

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [-instance] CategoryTheory.catToReflQuiver

/-- An integer invertible on `𝐆_m` over `k` is invertible in `k`. -/
theorem isUnit_natCast_of_isUnit_punctured {k : Type u} [Field k] {N : ℕ}
    (hN : IsUnit ((N : ℕ) : Γ((punctured k).toScheme, ⊤))) : IsUnit (N : k) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  let φ : k →+* Γ((punctured k).toScheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k))).appTop).hom
  rw [← map_natCast φ N, h0, map_zero] at hN
  obtain ⟨⟨p, hp⟩⟩ := nonempty_punctured k
  have : Nonempty (⊤ : (punctured k).toScheme.Opens) := ⟨⟨⟨p, hp⟩, trivial⟩⟩
  have : Nontrivial Γ((punctured k).toScheme, ⊤) := Scheme.component_nontrivial _ ⊤
  exact zero_ne_one (isUnit_zero_iff.1 hN)

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- **The Kummer class of the coordinate generates `R¹ j_* μ_N` at the origin, freely over
`ℤ/N`** (input A1c of relative purity), for every field `k`. Stated, like the proposition, in the
standard model of the derived categories. -/
theorem affineLineKummerGenerator (k : Type u) [Field k] : AffineLineKummerGenerator k := by
  intro N hN0 hN ht Ω _ _ x hx y
  have : NeZero N := ⟨hN0⟩
  set g := (Scheme.pointSmallEtale x).toPresheafFiber ((opensToEtale (affineLine k)).obj ⊤) y
    (kummerTarget (punctured k).ι N).obj
    (localKummerClass (punctured k).ι hN0 hN ⊤ (coordinate k) ht) with hg
  have hinj : Function.Injective (fun n : ZMod N => n.val • g) := by
    have key : ∀ a b : ZMod N, a.val ≤ b.val → a.val • g = b.val • g → a = b := by
      intro a b hab h
      have h0 := dvd_of_nsmul_germ_localKummerClass_eq_zero hN0 hN ht x hx y (b.val - a.val)
        (by rw [sub_nsmul _ hab, ← hg, h]; simp)
      exact ZMod.val_injective N (le_antisymm hab (Nat.sub_eq_zero_iff_le.1
        (Nat.eq_zero_of_dvd_of_lt h0 ((Nat.sub_le _ _).trans_lt (ZMod.val_lt b)))))
    intro a b h
    rcases le_total a.val b.val with hab | hab
    · exact key a b hab h
    · exact (key b a hab h.symm).symm
  have hcard := natCard_stalk_rightDerived_one_rootsOfUnity k (Nat.pos_of_ne_zero hN0)
    (isUnit_natCast_of_isUnit_punctured hN) x hx
  have : Finite (ToType ((Scheme.pointSmallEtale x).presheafFiber.obj
      (kummerTarget (punctured k).ι N).obj)) :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard hN0)
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_zmod]
  exact hcard.le

end StandardModel

end Stacks.EtaleCohomology.Purity

end
