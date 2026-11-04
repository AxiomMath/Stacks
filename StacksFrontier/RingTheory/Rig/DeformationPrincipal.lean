module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.Rig.Lifting

/-!
# Lifting a map into a quotient of a complete algebra with power torsion (Stacks 0AK7)

Let `A` be a Noetherian ring, `I = (a)` a principal ideal of `A`, and `B` an `I`-adically
complete `A`-algebra of finite type modulo `I`, with `a ^ c` annihilating
`Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`. Stacks 0AK6 lifts an `A`-algebra map
`ψₙ : B → C / aⁿC` to an `A`-algebra map `B → C` when `a` is a nonzerodivisor on the
`I`-adically complete `A`-algebra `C`. Stacks 0AK7 removes the regularity hypothesis: it
suffices that the `a`-power torsion `C[a^∞]` of `C` meet `a^d C` in `0` for some `d`, at the
price of asking `n > max (2c) (c + d)` instead of `n > 2c`.

The proof divides `C` into its torsion part and a torsion-free part and reassembles. Write
`T = C[a^∞]`. On the quotient `C̄ = C / T` the element `a` becomes a nonzerodivisor and the
quotient stays `I`-adically complete, so Stacks 0AK6 applies to `C̄` and produces
`φ̄ : B → C̄` agreeing with `ψₙ` modulo `a^{n-c}`. The hypothesis `T ∩ a^d C = 0` and
`d ≤ n - c` give `T ∩ a^{n-c} C = 0`, so `C` is the fibre product of `C̄` and
`C / a^{n-c} C` over `C / (T + a^{n-c} C)`; the maps `φ̄` and the reduction of `ψₙ` agree
there, hence glue to the required `φ : B → C`.

## Main results

* `Rig.exists_algHom_lift_of_torsion_disjoint`: **Stacks 0AK7**.

Auxiliary, and reusable:

* `Rig.isHausdorff_quotient_torsionIdeal` and `Rig.isAdicComplete_quotient_torsionIdeal`:
  killing the `b`-power torsion of a complete ring leaves it complete, as soon as that
  torsion meets one power of the ideal of definition in `0`.
* `Rig.isRegular_quotientMk_torsionIdeal`: an element becomes a nonzerodivisor after its
  power torsion is killed.
* `Rig.quotientMk_prod_injective_of_disjoint` and `Rig.exists_ringHom_comp_eq_of_disjoint`:
  a ring is the fibre product of its quotients by two ideals meeting in `0`.

## Implementation notes

`C[a^∞]` is `torsionIdeal C (algebraMap A C a)`, and the hypothesis `C[a^∞] ∩ a^d C = 0` is
phrased as disjointness of that ideal and the `d`-th power of `I C`.

The completed naive cotangent complex `NL^∧_{B/A}` is read off a completed polynomial
presentation `P` of `B`, exactly as in Stacks 0AK6, so `P` appears among the hypotheses.

Completeness of `C / C[a^∞]` is where the hypothesis on the torsion is used twice over: it
makes the quotient Hausdorff, whereas precompleteness is automatic for a quotient of a
precomplete ring.

## References

* [Stacks Project, Tag 0AK7](https://stacks.math.columbia.edu/tag/0AK7)
* [Stacks Project, Tag 0AK6](https://stacks.math.columbia.edu/tag/0AK6)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v w

section Torsion

variable {C : Type w} [CommRing C]

/-- The `b`-power torsion of `C` is closed in the `J`-adic topology as soon as it meets one
power of `J` in `0`; equivalently, the quotient `C / C[b^∞]` is `J`-adically Hausdorff. -/
public theorem isHausdorff_quotient_torsionIdeal (J : Ideal C) (b : C) (d : ℕ)
    (hdisj : Disjoint (torsionIdeal C b) (J ^ d)) [IsHausdorff J C] :
    IsHausdorff (J.map (Ideal.Quotient.mk (torsionIdeal C b)))
      (C ⧸ torsionIdeal C b) := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmem (n : ℕ) : x ∈ J ^ n ⊔ torsionIdeal C b := by
    apply (Ideal.mem_quotient_iff_mem_sup (I := torsionIdeal C b) (J := J ^ n)).mp
    simpa only [smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] using SModEq.zero.mp (hx n)
  choose u hu t ht huxt using fun n ↦ Submodule.mem_sup.mp (hmem n)
  have ht_eq (n : ℕ) (hdn : d ≤ n) : t n = t d := by
    apply sub_eq_zero.mp
    apply hdisj.le_bot
    refine ⟨(torsionIdeal C b).sub_mem (ht n) (ht d), ?_⟩
    rw [show t n - t d = u d - u n by linear_combination huxt n - huxt d]
    exact (J ^ d).sub_mem (hu d) (Ideal.pow_le_pow_right hdn (hu n))
  have hxd : x - t d ∈ J ^ d := by
    rw [← huxt d]
    simpa using hu d
  have hxT : x - t d = 0 := by
    apply IsHausdorff.haus (I := J) (M := C) inferInstance (x - t d)
    intro n
    by_cases hdn : d ≤ n
    · rw [show x - t d = u n by linear_combination ht_eq n hdn - huxt n]
      exact SModEq.zero.2 (by simpa using hu n)
    · exact SModEq.mono (Submodule.pow_smul_top_le J C (Nat.le_of_not_ge hdn))
        (SModEq.zero.2 (by simpa using hxd))
  rw [Ideal.Quotient.eq_zero_iff_mem, sub_eq_zero.mp hxT]
  exact ht d

/-- Killing the `b`-power torsion of a `J`-adically complete ring leaves it `J`-adically
complete, provided that torsion meets one power of `J` in `0`. Precompleteness passes to any
quotient; the hypothesis on the torsion supplies the Hausdorff half. -/
public theorem isAdicComplete_quotient_torsionIdeal (J : Ideal C) (b : C) (d : ℕ)
    (hdisj : Disjoint (torsionIdeal C b) (J ^ d)) [IsAdicComplete J C] :
    IsAdicComplete (J.map (Ideal.Quotient.mk (torsionIdeal C b)))
      (C ⧸ torsionIdeal C b) := by
  have : IsPrecomplete (J.map (Ideal.Quotient.mk (torsionIdeal C b)))
      (C ⧸ torsionIdeal C b) :=
    isPrecomplete_map_of_surjective (I := J)
      (f := Ideal.Quotient.mk (torsionIdeal C b)) Ideal.Quotient.mk_surjective
  have : IsHausdorff (J.map (Ideal.Quotient.mk (torsionIdeal C b)))
      (C ⧸ torsionIdeal C b) :=
    isHausdorff_quotient_torsionIdeal J b d hdisj
  exact ⟨⟩

/-- An element becomes a nonzerodivisor once its power torsion is killed. -/
public theorem isRegular_quotientMk_torsionIdeal (b : C) :
    IsRegular (Ideal.Quotient.mk (torsionIdeal C b) b) := by
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff]
  have key (x : C) (hx : b * x ∈ torsionIdeal C b) :
      Ideal.Quotient.mk (torsionIdeal C b) x = 0 := by
    obtain ⟨n, hn⟩ := (mem_torsionIdeal_iff C b (b * x)).mp hx
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [mem_torsionIdeal_iff]
    exact ⟨n + 1, by linear_combination hn⟩
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x <;>
    exact key x (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [mul_comm] using hx))

end Torsion

section FibreProduct

/-- A ring injects into the product of its quotients by two ideals meeting in `0`. -/
public theorem quotientMk_prod_injective_of_disjoint {C : Type*} [CommRing C]
    (I J : Ideal C) (hIJ : Disjoint I J) :
    Function.Injective fun z : C => (Ideal.Quotient.mk I z, Ideal.Quotient.mk J z) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hi : x - y ∈ I := Ideal.Quotient.eq.mp (congrArg Prod.fst hxy)
  have hj : x - y ∈ J := Ideal.Quotient.eq.mp (congrArg Prod.snd hxy)
  exact Ideal.mem_bot.mp (hIJ.le_bot ⟨hi, hj⟩)

/-- Two ring maps into the quotients of `C` by ideals `I` and `J` meeting in `0` glue to a
single ring map into `C` as soon as they agree modulo `I + J`: the square expressing `C` as
the fibre product of `C / I` and `C / J` over `C / (I + J)` is cartesian. -/
@[ega "0 19.3.10.2" "partial"]
public theorem exists_ringHom_comp_eq_of_disjoint {R C : Type*} [CommRing R] [CommRing C]
    (I J : Ideal C) (hIJ : Disjoint I J) (f : R →+* C ⧸ I) (g : R →+* C ⧸ J)
    (hcompat : ∀ x, Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J) (f x) =
      Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J) (g x)) :
    ∃ h : R →+* C,
      (Ideal.Quotient.mk I).comp h = f ∧ (Ideal.Quotient.mk J).comp h = g := by
  have hpair (x : C ⧸ I) (y : C ⧸ J)
      (hxy : Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J) x =
        Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J) y) :
      ∃ z : C, Ideal.Quotient.mk I z = x ∧ Ideal.Quotient.mk J z = y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hab : a - b ∈ I ⊔ J :=
      Ideal.Quotient.eq.mp (by simpa only [Ideal.Quotient.factor_mk] using hxy)
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hab
    refine ⟨b + j, ?_, ?_⟩
    · refine Ideal.Quotient.eq.mpr ?_
      rw [show b + j - a = -i by linear_combination hij]
      exact I.neg_mem hi
    · exact Ideal.Quotient.eq.mpr (by simpa using hj)
  have hinj := quotientMk_prod_injective_of_disjoint (C := C) I J hIJ
  choose liftFun hlift using fun x : R => hpair (f x) (g x) (hcompat x)
  refine ⟨{ toFun := liftFun
            map_one' := hinj (by simp [hlift])
            map_mul' := fun x y ↦ hinj (by simp [hlift, map_mul])
            map_zero' := hinj (by simp [hlift])
            map_add' := fun x y ↦ hinj (by simp [hlift, map_add]) }, ?_, ?_⟩
  · exact RingHom.ext fun x => (hlift x).1
  · exact RingHom.ext fun x => (hlift x).2

/-- Two `A`-algebra maps into the quotients of `C` by ideals `I` and `J` meeting in `0` glue
to a single `A`-algebra map into `C` as soon as they agree modulo `I + J`. -/
public theorem exists_algHom_comp_eq_of_disjoint {A R C : Type*} [CommRing A] [CommRing R]
    [CommRing C] [Algebra A R] [Algebra A C]
    (I J : Ideal C) (hIJ : Disjoint I J) (f : R →ₐ[A] C ⧸ I) (g : R →ₐ[A] C ⧸ J)
    (hcompat : ∀ x, Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J) (f x) =
      Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J) (g x)) :
    ∃ h : R →ₐ[A] C,
      (Ideal.Quotient.mkₐ A I).comp h = f ∧ (Ideal.Quotient.mkₐ A J).comp h = g := by
  obtain ⟨h, hf, hg⟩ :=
    exists_ringHom_comp_eq_of_disjoint I J hIJ f.toRingHom g.toRingHom hcompat
  refine ⟨{ toRingHom := h
            commutes' := fun r ↦ quotientMk_prod_injective_of_disjoint I J hIJ
              (Prod.ext ?_ ?_) }, ?_, ?_⟩
  · exact (RingHom.congr_fun hf _).trans (f.commutes r)
  · exact (RingHom.congr_fun hg _).trans (g.commutes r)
  · exact AlgHom.ext fun x ↦ RingHom.congr_fun hf x
  · exact AlgHom.ext fun x ↦ RingHom.congr_fun hg x

/-- For ideals `T` and `K` of `C`, the composite of `C ⧸ T → (C ⧸ T) ⧸ K (C ⧸ T)` with the
isomorphism `(C ⧸ T) ⧸ K (C ⧸ T) ≃ C ⧸ (T ⊔ K)` is the quotient map `C ⧸ T → C ⧸ (T ⊔ K)`. -/
public theorem quotQuotEquivQuotSup_quotEquivOfEq_mk {C : Type*} [CommRing C] (T K : Ideal C)
    {L : Ideal (C ⧸ T)} (hL : L = K.map (Ideal.Quotient.mk T)) (z : C ⧸ T) :
    DoubleQuot.quotQuotEquivQuotSup T K (Ideal.quotEquivOfEq hL (Ideal.Quotient.mk L z)) =
      Ideal.Quotient.factor (le_sup_left : T ≤ T ⊔ K) z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.quotEquivOfEq_mk]
  show DoubleQuot.quotQuotEquivQuotSup T K (DoubleQuot.quotQuotMk T K z) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.Quotient.factor_mk]

/-- Extending an ideal of `A` to a quotient `C ⧸ T` is extending it to `C` and then mapping it
along the quotient map. -/
public theorem map_algebraMap_quotient {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) (T : Ideal C) :
    I.map (algebraMap A (C ⧸ T)) = (I.map (algebraMap A C)).map (Ideal.Quotient.mk T) := by
  have h : algebraMap A (C ⧸ T) = (Ideal.Quotient.mk T).comp (algebraMap A C) := by
    ext r
    rw [IsScalarTower.algebraMap_apply A C (C ⧸ T) r]
    rfl
  rw [h, ← Ideal.map_map]

end FibreProduct

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0AK7.** Let `I = (a)` be a principal ideal of a Noetherian ring `A`, let `B` be
an `I`-adically complete `A`-algebra of finite type modulo `I`, and suppose `a ^ c`
annihilates `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`. Let `C` be an `I`-adically
complete `A`-algebra whose `a`-power torsion `C[a^∞]` meets `a^d C` in `0`, and let
`n > max (2c) (c + d)`. Then every `A`-algebra map `B → C / aⁿC` agrees modulo `a ^ (n - c)`
with the reduction of an `A`-algebra map `B → C`.

This drops the regularity hypothesis of Stacks 0AK6: the torsion is killed, 0AK6 is applied
to `C / C[a^∞]`, and the resulting map is glued with the reduction of `ψₙ` along the
cartesian square of quotients of `C` by `C[a^∞]` and `a^{n-c}C`. -/
@[stacks 0AK7]
public theorem exists_algHom_lift_of_torsion_disjoint
    (a : A) (I : Ideal A) (hI : I = Ideal.span {a})
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B)
    (c : ℕ)
    (hExt : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) ^ c • ξ = 0)
    {C : Type w} [CommRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (d : ℕ)
    (htorsion : Disjoint (torsionIdeal C (algebraMap A C a))
      ((I.map (algebraMap A C)) ^ d))
    (n : ℕ) (hn : max (2 * c) (c + d) < n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (Nat.sub_le n c))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - c))).comp φ := by
  let K : Ideal C := I.map (algebraMap A C)
  let b : C := algebraMap A C a
  let T : Ideal C := torsionIdeal C b
  let Cbar := C ⧸ T
  let Kbar : Ideal Cbar := I.map (algebraMap A Cbar)
  let k := n - c
  let Kk : Ideal C := K ^ k
  have hk_n : k ≤ n := Nat.sub_le _ _
  have hdisjKk : Disjoint T Kk := htorsion.mono_right (Ideal.pow_le_pow_right (by omega))
  have hKbar : Kbar = K.map (Ideal.Quotient.mk T) := map_algebraMap_quotient I T
  have : IsAdicComplete (I.map (algebraMap A Cbar)) Cbar := by
    rw [show I.map (algebraMap A Cbar) = K.map (Ideal.Quotient.mk T) from hKbar]
    exact isAdicComplete_quotient_torsionIdeal K b d htorsion
  have hKpow (m : ℕ) : (K ^ m).map (Ideal.Quotient.mk T) = Kbar ^ m := by
    rw [Ideal.map_pow, ← hKbar]
  have hle_n : K ^ n ≤ Ideal.comap (Ideal.Quotient.mkₐ A T) (Kbar ^ n) :=
    Ideal.map_le_iff_le_comap.mp (hKpow n).le
  let qn : C ⧸ K ^ n →ₐ[A] Cbar ⧸ Kbar ^ n :=
    Ideal.quotientMapₐ (Kbar ^ n) (Ideal.Quotient.mkₐ A T) hle_n
  obtain ⟨φbar, hbar⟩ := exists_algHom_lift_of_isRegular a I hI B P c hExt
    (C := Cbar) (isRegular_quotientMk_torsionIdeal b) n (by omega) (qn.comp ψn)
  have hlebar : Kbar ^ n ≤ Kbar ^ k := Ideal.pow_le_pow_right hk_n
  let ψlow : B.carrier →ₐ[A] C ⧸ Kk :=
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hk_n)).comp ψn
  let e : Cbar ⧸ Kbar ^ k ≃+* C ⧸ (T ⊔ Kk) :=
    (Ideal.quotEquivOfEq (hKpow k).symm).trans (DoubleQuot.quotQuotEquivQuotSup T Kk)
  have he_mk (z : Cbar) : e (Ideal.Quotient.mk (Kbar ^ k) z) =
      Ideal.Quotient.factor (le_sup_left : T ≤ T ⊔ Kk) z :=
    quotQuotEquivQuotSup_quotEquivOfEq_mk T Kk (hKpow k).symm z
  have hmaps (w : C ⧸ K ^ n) :
      e (Ideal.Quotient.factor hlebar (qn w)) =
        Ideal.Quotient.factor (le_sup_right : Kk ≤ T ⊔ Kk)
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right hk_n) w) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hqn : qn (Ideal.Quotient.mk (K ^ n) z) =
        Ideal.Quotient.mk (Kbar ^ n) (Ideal.Quotient.mk T z) :=
      congrArg (Ideal.Quotient.mk (Kbar ^ n)) (congrFun (Ideal.Quotient.mkₐ_eq_mk A T) z)
    simp only [hqn, Ideal.Quotient.factor_mk, he_mk]
    rw [Ideal.Quotient.factor_mk]
  have hcompat (x : B.carrier) :
      Ideal.Quotient.factor (le_sup_left : T ≤ T ⊔ Kk) (φbar x) =
        Ideal.Quotient.factor (le_sup_right : Kk ≤ T ⊔ Kk) (ψlow x) :=
    calc
      _ = e (Ideal.Quotient.mk (Kbar ^ k) (φbar x)) := (he_mk _).symm
      _ = e (Ideal.Quotient.factor hlebar (qn (ψn x))) :=
        congrArg e (AlgHom.ext_iff.mp hbar x).symm
      _ = _ := hmaps (ψn x)
  obtain ⟨φ, -, hφ⟩ := exists_algHom_comp_eq_of_disjoint T Kk hdisjKk φbar ψlow hcompat
  exact ⟨φ, hφ.symm⟩

end Main

end Rig

end
