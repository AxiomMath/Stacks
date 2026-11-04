module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityStalkEval
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOne

/-!
# Compatible generators of the stalks of `μ_{ℓⁿ⁺¹}` at a geometric point

Let `s : Spec Ω ⟶ X` be a geometric point with `Ω` algebraically closed, `X` a scheme over a field
`k` in which the prime `ℓ` is invertible. A germ of `μ_N` at `s` is determined by its value in `Ω`
(`Stacks.Kummer.eq_of_rootEval_eq`), so a compatible system `εₙ₊₁^ℓ = εₙ` of primitive
`ℓⁿ⁺¹`-th roots of unity in `Ω` gives germs `eₙ` of primitive roots on the neighbourhoods
`X ×_k k(ζ_{ℓⁿ⁺¹})` with `eₙ₊₁^ℓ = eₙ` (`Stacks.Kummer.exists_compatible_rootGerms`): the
generators of the stalk of the Tate module `ℤ_ℓ(1)` at `s`.

## Main results

* `Stacks.Kummer.eq_of_rootEval_eq`: a germ of `μ_N` with the same value as the germ of a
  primitive `N`-th root of unity is that germ.
* `Stacks.Kummer.exists_compatible_rootGerms`: germs `eₙ` of primitive `ℓⁿ⁺¹`-th roots of unity
  with `eₙ₊₁^ℓ = eₙ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GrothendieckTopology

universe u

namespace Stacks.Kummer

/-- An `ℓ`-th root of a primitive `ℓⁿ⁺¹`-th root of unity is a primitive `ℓⁿ⁺²`-th root. -/
theorem isPrimitiveRoot_of_pow_prime {M : Type*} [CommMonoid M] {ℓ n : ℕ} (hℓ : ℓ.Prime) {y : M}
    (h : IsPrimitiveRoot (y ^ ℓ) (ℓ ^ (n + 1))) : IsPrimitiveRoot y (ℓ ^ (n + 1 + 1)) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  have h1 : y ^ (ℓ ^ (n + 1 + 1)) = 1 := by rw [pow_succ', pow_mul, h.pow_eq_one]
  obtain ⟨j, hj, hy⟩ := (Nat.dvd_prime_pow hℓ).1 (orderOf_dvd_of_pow_eq_one h1)
  rcases Nat.lt_or_ge j (n + 1 + 1) with hlt | hge
  · exfalso
    have h2 : y ^ (ℓ ^ (n + 1)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hy]
      exact pow_dvd_pow ℓ (by omega)
    have h3 : (y ^ ℓ) ^ (ℓ ^ n) = 1 := by rwa [← pow_mul, ← pow_succ']
    have h4 := (h.pow_eq_one_iff_dvd _).1 h3
    rw [Nat.pow_dvd_pow_iff_le_right hℓ.one_lt] at h4
    omega
  · rw [hy, le_antisymm hj hge]

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- The value of the `ℓ`-th power of a section is the `ℓ`-th power of its value. -/
theorem rootEval_powMap (ℓ N N' : ℕ) (hN : ℓ * N = N') [NeZero N] [NeZero N'] {U : X.Etale}
    (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N').obj.obj (op U))) :
    rootEval s N u ((rootsOfUnityModulePowMap.{u, 0} X ℓ N N' hN).hom.app (op U) z) =
      rootEval s N' u z ^ ℓ := by
  have h : (rootsOfUnitySection.{u, 0} X N (op U)
      ((rootsOfUnityPowMap.{u, 0} X ℓ N N' hN).hom.app (op U) z)).1 =
        (rootsOfUnitySection.{u, 0} X N' (op U) z).1 ^ ℓ :=
    ofUnit_injective.{u, 0}
      ((rootsOfUnityι_rootsOfUnityPowMap_apply.{u, 0} X ℓ N N' hN (op U) z).trans
        (powMap_app_ofUnit _ _ _ _))
  show (Scheme.ΓSpecIso (.of Ω)).hom.hom ((fiberLift s u).appTop.hom
    ((rootsOfUnitySection.{u, 0} X N (op U)
      ((rootsOfUnityPowMap.{u, 0} X ℓ N N' hN).hom.app (op U) z)).1 : Γ(U.left, ⊤))) = _
  rw [h, Units.val_pow_eq_pow_val, map_pow, map_pow]
  rfl

/-- **A germ of `μ_N` is determined by its value**: a germ with the same value as the germ of a
primitive `N`-th root `ζ` is that germ. -/
theorem eq_of_rootEval_eq (N : ℕ) [NeZero N] [Fact (1 < N)] {V : X.Etale}
    (v : (Scheme.pointSmallEtale s).fiber.obj V) {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤))
    {ζ : k} (hζ : IsPrimitiveRoot ζ N) {U : X.Etale} (u : (Scheme.pointSmallEtale s).fiber.obj U)
    (z : ToType ((rootsOfUnityModule.{u, 0} X N).obj.obj (op U)))
    (h : rootEval s N u z = rootEval s N v (rootSection N κ hζ 1)) :
    (Scheme.pointSmallEtale s).toPresheafFiber U u (rootsOfUnityModule.{u, 0} X N).obj z =
      (Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
        (rootSection N κ hζ 1) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, u} (ZMod N)
  obtain ⟨i, hi⟩ := exists_nsmul_eq_germ_sliceRootSection s N v κ hζ
    ((Scheme.pointSmallEtale s).toPresheafFiber U u (rootsOfUnityModule.{u, 0} X N).obj z)
  have hi' := hi
  rw [← map_nsmul] at hi'
  have hev := rootEval_eq_of_germ_eq s N _ _ _ _ hi'
  rw [rootEval_nsmul, h, rootEval_sliceRootSection, ZMod.val_one, pow_one] at hev
  have hε := isPrimitiveRoot_rootFieldMap s N v κ hζ
  rw [pow_eq_pow_mod_of_pow_eq_one hε.pow_eq_one i] at hev
  have hi1 : i % N = 1 := hε.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N)))
    (Fact.out : 1 < N) (hev.symm.trans (pow_one _).symm)
  rw [hi]
  set e := (Scheme.pointSmallEtale s).toPresheafFiber V v (rootsOfUnityModule.{u, 0} X N).obj
    (rootSection N κ hζ 1)
  have hN : N • e = 0 := ZModModule.char_nsmul_eq_zero N e
  rw [nsmul_eq_mod_nsmul_of_nsmul_eq_zero N hN i, hi1, one_nsmul]

section Compatible

attribute [local instance] Stacks.EtaleCohomology.neZero_pow_of_fact_prime
  Stacks.EtaleCohomology.neZero_natCast_pow

variable {k : Type u} [Field k] (fX : X ⟶ Spec (.of k)) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : k)]

/-- The primitive `ℓⁿ⁺¹`-th root of unity of the cyclotomic field `k(ζ_{ℓⁿ⁺¹})`. -/
abbrev cyclotomicZeta (n : ℕ) : CyclotomicField (ℓ ^ (n + 1)) k :=
  IsCyclotomicExtension.zeta (ℓ ^ (n + 1)) k (CyclotomicField (ℓ ^ (n + 1)) k)

/-- A positive power of a prime is greater than one. -/
theorem one_lt_pow_succ_of_prime (n : ℕ) : 1 < ℓ ^ (n + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero n) (Fact.out : ℓ.Prime).one_lt

include fX in
/-- **Compatible germs of primitive roots of unity**: at a geometric point with algebraically
closed `Ω`, lifts `vₙ` to `X ×_k k(ζ_{ℓⁿ⁺¹})` of a neighbourhood and exponents `jₙ` such that the
germs `eₙ` of the primitive roots `ζ_{ℓⁿ⁺¹}^{jₙ}` satisfy `eₙ₊₁^ℓ = eₙ`. -/
theorem exists_compatible_rootGerms {U₀ : X.Etale} (u₀ : (Scheme.pointSmallEtale s).fiber.obj U₀) :
    ∃ (v : ∀ n : ℕ, (Scheme.pointSmallEtale s).fiber.obj
        (cyclotomicBaseChange fX (ℓ ^ (n + 1)) U₀)) (j : ℕ → ℕ)
      (hj : ∀ n, IsPrimitiveRoot (cyclotomicZeta (k := k) ℓ n ^ j n) (ℓ ^ (n + 1))),
      ∀ n, (Scheme.pointSmallEtale s).toPresheafFiber _ (v (n + 1))
          (rootsOfUnityModule.{u, 0} X (ℓ ^ (n + 1))).obj
          ((rootsOfUnityModulePowMap.{u, 0} X ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
            (pow_succ' ℓ (n + 1)).symm).hom.app (op _)
            (rootSection (ℓ ^ (n + 1 + 1)) (cyclotomicBaseChangeStructMap fX _ U₀)
              (hj (n + 1)) 1)) =
        (Scheme.pointSmallEtale s).toPresheafFiber _ (v n)
          (rootsOfUnityModule.{u, 0} X (ℓ ^ (n + 1))).obj
          (rootSection (ℓ ^ (n + 1)) (cyclotomicBaseChangeStructMap fX _ U₀) (hj n) 1) := by
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hv : ∀ n : ℕ, Nonempty ((Scheme.pointSmallEtale s).fiber.obj
      (cyclotomicBaseChange fX (ℓ ^ (n + 1)) U₀)) := fun n => by
    have hcov : Sieve.ofArrows (fun _ : PUnit.{u + 2} => cyclotomicBaseChange fX (ℓ ^ (n + 1)) U₀)
        (fun _ => cyclotomicBaseChangeπ fX (ℓ ^ (n + 1)) U₀) ∈ X.smallEtaleTopology U₀ := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
        rw [range_cyclotomicBaseChangeπ]; trivial⟩
    obtain ⟨Y, g, ⟨Z, h, -, ⟨⟩, -⟩, y, -⟩ := (Scheme.pointSmallEtale s).jointly_surjective _ hcov u₀
    exact ⟨(Scheme.pointSmallEtale s).fiber.map h y⟩
  let v : ∀ n : ℕ, (Scheme.pointSmallEtale s).fiber.obj
      (cyclotomicBaseChange fX (ℓ ^ (n + 1)) U₀) := fun n => (hv n).some
  let κ := fun n : ℕ => cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1)) U₀
  have hz : ∀ n, IsPrimitiveRoot (cyclotomicZeta (k := k) ℓ n) (ℓ ^ (n + 1)) := fun n =>
    IsCyclotomicExtension.zeta_spec _ k _
  let ε' := fun n : ℕ => rootFieldMap s (v n) (κ n) (cyclotomicZeta (k := k) ℓ n)
  have hε' : ∀ n, IsPrimitiveRoot (ε' n) (ℓ ^ (n + 1)) := fun n =>
    isPrimitiveRoot_rootFieldMap s _ (v n) (κ n) (hz n)
  let ε : ℕ → Ω := fun n => Nat.rec (ε' 0)
    (fun _ e => (IsAlgClosed.exists_pow_nat_eq e hℓ).choose) n
  have hεs : ∀ n, ε (n + 1) ^ ℓ = ε n := fun n =>
    (IsAlgClosed.exists_pow_nat_eq (ε n) hℓ).choose_spec
  have hε : ∀ n, IsPrimitiveRoot (ε n) (ℓ ^ (n + 1)) := fun n => by
    induction n with
    | zero => exact hε' 0
    | succ n ih =>
      rw [← hεs n] at ih
      exact isPrimitiveRoot_of_pow_prime (Fact.out : ℓ.Prime) ih
  have hj : ∀ n, ∃ j : ℕ, ε' n ^ j = ε n := fun n =>
    ((hε' n).eq_pow_of_pow_eq_one (hε n).pow_eq_one).imp fun _ h => h.2
  choose j hjε using hj
  have hjp : ∀ n, IsPrimitiveRoot (cyclotomicZeta (k := k) ℓ n ^ j n) (ℓ ^ (n + 1)) := fun n =>
    (hz n).pow_of_coprime _
      (((hε' n).pow_iff_coprime (by positivity) (j n)).1 (by rw [hjε]; exact hε n))
  refine ⟨v, j, hjp, fun n => ?_⟩
  have : Fact (1 < ℓ ^ (n + 1)) := ⟨one_lt_pow_succ_of_prime ℓ n⟩
  have : Fact (1 < ℓ ^ (n + 1 + 1)) := ⟨one_lt_pow_succ_of_prime ℓ (n + 1)⟩
  refine eq_of_rootEval_eq s _ (v n) (κ n) (hjp n) (v (n + 1)) _ ?_
  rw [rootEval_powMap, rootEval_sliceRootSection, rootEval_sliceRootSection, ZMod.val_one,
    ZMod.val_one, pow_one, pow_one, map_pow, map_pow]
  show (ε' (n + 1) ^ j (n + 1)) ^ ℓ = ε' n ^ j n
  rw [hjε, hjε, hεs]

end Compatible

end Stacks.Kummer

end
