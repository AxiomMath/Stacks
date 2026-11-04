module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Set.Function

/-!
# Torsion coprime to a degree is unchanged by maps composing to that degree

Let `n` be an integer and let `A` be an abelian group. The *`n`-torsion* of `A` is the set of
`x : A` with `n • x = 0`. A homomorphism of abelian groups is a bijection on `n`-torsion as soon
as there is a homomorphism in the other direction with which it composes, in both orders, to
multiplication by an integer `N` coprime to `n`.

## Main definitions

* `Stacks.Picard.zsmulTorsion` — the `n`-torsion of an abelian group, as a set.

## Main results

* `Stacks.Picard.bijOn_zsmul_zsmulTorsion` — multiplication by `N` is a bijection of the
  `n`-torsion of an abelian group onto itself when `N` and `n` are coprime.
* `Stacks.Picard.bijOn_zsmulTorsion_of_comp_eq_zsmul` — a homomorphism paired with one in the
  other direction, with both composites equal to multiplication by an integer coprime to `n`,
  is a bijection from the `n`-torsion of its source onto the `n`-torsion of its target.
* `Stacks.Picard.bijOn_zsmulTorsion_of_comp_eq_prime_pow_zsmul` — the same conclusion from
  composites equal to multiplication by `p ^ m`, with `n` prime to `p`.

## References

* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
-/

@[expose] public section

namespace Stacks.Picard

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The `n`-torsion of an abelian group: the set of elements killed by `n`. -/
def zsmulTorsion (A : Type*) [AddCommGroup A] (n : ℤ) : Set A :=
  {x : A | n • x = 0}

/-- Membership in the `n`-torsion is exactly being killed by `n`. -/
@[simp]
theorem mem_zsmulTorsion {n : ℤ} {x : A} : x ∈ zsmulTorsion A n ↔ n • x = 0 := Iff.rfl

/-- The `n`-torsion is preserved by multiplication by any integer. -/
theorem zsmul_mem_zsmulTorsion {n N : ℤ} {x : A} (hx : x ∈ zsmulTorsion A n) :
    N • x ∈ zsmulTorsion A n := by
  rw [mem_zsmulTorsion, smul_smul, mul_comm, ← smul_smul, mem_zsmulTorsion.1 hx, smul_zero]

/-- If `N` and `n` are coprime then multiplication by `N` is injective on the `n`-torsion. -/
theorem injOn_zsmul_zsmulTorsion {N n : ℤ} (h : IsCoprime N n) :
    Set.InjOn (fun x : A => N • x) (zsmulTorsion A n) := by
  obtain ⟨a, b, hab⟩ := h
  intro x hx y hy hxy
  have hN : N • (x - y) = 0 := by
    rw [smul_sub, show N • x = N • y from hxy, sub_self]
  have hn : n • (x - y) = 0 := by
    rw [smul_sub, mem_zsmulTorsion.1 hx, mem_zsmulTorsion.1 hy, sub_zero]
  have h1 : (1 : ℤ) • (x - y) = 0 := by
    rw [← hab, add_smul, mul_smul, mul_smul, hN, hn, smul_zero, smul_zero, add_zero]
  rwa [one_smul, sub_eq_zero] at h1

/-- If `N` and `n` are coprime then multiplication by `N` is a bijection of the `n`-torsion
onto itself, with inverse multiplication by a Bézout coefficient of `N` modulo `n`. -/
theorem bijOn_zsmul_zsmulTorsion {N n : ℤ} (h : IsCoprime N n) :
    Set.BijOn (fun x : A => N • x) (zsmulTorsion A n) (zsmulTorsion A n) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨fun _ hx => zsmul_mem_zsmulTorsion hx, injOn_zsmul_zsmulTorsion ⟨a, b, hab⟩,
    fun y hy => ⟨a • y, zsmul_mem_zsmulTorsion hy, ?_⟩⟩
  show N • a • y = y
  have hNa : N * a = 1 - b * n := by rwa [mul_comm N a, eq_sub_iff_add_eq]
  rw [← mul_smul, hNa, sub_smul, one_smul, mul_smul, mem_zsmulTorsion.1 hy, smul_zero, sub_zero]

/-- A homomorphism carries `n`-torsion to `n`-torsion. -/
theorem mapsTo_zsmulTorsion (f : A →+ B) (n : ℤ) :
    Set.MapsTo f (zsmulTorsion A n) (zsmulTorsion B n) := fun _ hx => by
  rw [mem_zsmulTorsion, ← map_zsmul, mem_zsmulTorsion.1 hx, map_zero]

/-- Let `f : A →+ B` and `g : B →+ A` be homomorphisms of abelian groups whose two composites are
both multiplication by an integer `N` coprime to `n`. Then `f` is a bijection from the
`n`-torsion of `A` onto the `n`-torsion of `B`. -/
theorem bijOn_zsmulTorsion_of_comp_eq_zsmul (f : A →+ B) (g : B →+ A) {N n : ℤ}
    (h : IsCoprime N n) (hgf : ∀ x, g (f x) = N • x) (hfg : ∀ y, f (g y) = N • y) :
    Set.BijOn f (zsmulTorsion A n) (zsmulTorsion B n) := by
  refine ⟨mapsTo_zsmulTorsion f n, ?_, ?_⟩
  · intro x hx y hy hxy
    refine injOn_zsmul_zsmulTorsion h hx hy ?_
    show N • x = N • y
    rw [← hgf, ← hgf, hxy]
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := (bijOn_zsmul_zsmulTorsion (A := B) h).surjOn hy
    exact ⟨g z, mapsTo_zsmulTorsion g n hz, by rwa [hfg]⟩

/-- Let `f : A →+ B` and `g : B →+ A` be homomorphisms of abelian groups whose two composites are
both multiplication by `p ^ m`, and let `n` be prime to `p`. Then `f` is a bijection from the
`n`-torsion of `A` onto the `n`-torsion of `B`. -/
theorem bijOn_zsmulTorsion_of_comp_eq_prime_pow_zsmul (f : A →+ B) (g : B →+ A) {n : ℤ}
    {p m : ℕ} (hn : n.natAbs.Coprime p)
    (hgf : ∀ x, g (f x) = ((p : ℤ) ^ m) • x) (hfg : ∀ y, f (g y) = ((p : ℤ) ^ m) • y) :
    Set.BijOn f (zsmulTorsion A n) (zsmulTorsion B n) := by
  have hp : IsCoprime (p : ℤ) n := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.Coprime] using hn.symm
  exact bijOn_zsmulTorsion_of_comp_eq_zsmul f g (hp.pow_left (m := m)) hgf hfg

end Stacks.Picard

end
