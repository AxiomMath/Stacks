module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.FinitePresentation
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Products, localizations and descent of étale algebras

## Main results

* `formallyEtale_prod`, `etale_prod`: a product of two (formally) étale algebras is (formally)
  étale.
* `isLocalizationAway_prod`: the localization of a product at an element is the product of the
  localizations.
* `eq_top_of_forall_map_eval`: an ideal of a finite product of rings whose image in every factor
  is the unit ideal is the unit ideal.
* `finiteType_of_surjective_of_ker`: an algebra which is of finite type modulo a nilpotent ideal
  of the base is of finite type.
* `etale_of_faithfullyFlat_of_etale`: if `S → U` is formally étale and faithfully flat, `R → U`
  is étale and `S` is of finite presentation over `R`, then `R → S` is étale.
* `etale_away_of_faithfullyFlat`: if `B → Γ` is étale and faithfully flat, `B` is of finite
  presentation over `A` and `Γ_a` is étale over `A`, then `B_a` is étale over `A`.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.Etale.PushoutLift

section Prod

variable (R : Type*) [CommRing R] (S T : Type u) [CommRing S] [CommRing T] [Algebra R S]
  [Algebra R T]

/-- The family `true ↦ S`, `false ↦ T`. -/
def boolFam : Bool → Type u := fun b => cond b S T

/-- Each member of `boolFam S T` is a commutative ring. -/
instance boolFam.commRing : ∀ b, CommRing (boolFam S T b)
  | true => inferInstanceAs (CommRing S)
  | false => inferInstanceAs (CommRing T)

/-- Each member of `boolFam S T` is an `R`-algebra. -/
instance boolFam.algebra : ∀ b, Algebra R (boolFam S T b)
  | true => inferInstanceAs (Algebra R S)
  | false => inferInstanceAs (Algebra R T)

/-- `Π b, boolFam S T b ≃ S × T`. -/
def piBoolEquiv : (∀ b, boolFam S T b) ≃ₐ[R] S × T where
  toFun f := (f true, f false)
  invFun p := fun b => match b with
    | true => p.1
    | false => p.2
  left_inv f := by
    funext b
    cases b <;> rfl
  right_inv p := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A product of two formally étale algebras is formally étale. -/
theorem formallyEtale_prod [Algebra.FormallyEtale R S] [Algebra.FormallyEtale R T] :
    Algebra.FormallyEtale R (S × T) := by
  have : ∀ b, Algebra.FormallyEtale R (boolFam S T b) := fun b => by cases b <;> assumption
  exact Algebra.FormallyEtale.of_equiv (piBoolEquiv R S T)

/-- A product of two étale algebras is étale. -/
theorem etale_prod [Algebra.Etale R S] [Algebra.Etale R T] : Algebra.Etale R (S × T) := by
  have : ∀ b, Algebra.Etale R (boolFam S T b) := fun b => by cases b <;> assumption
  exact Algebra.Etale.of_equiv (piBoolEquiv R S T)

end Prod

section LocalizationProd

variable {S T S' T' : Type*} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
  [Algebra S S'] [Algebra T T']

/-- **The localization of a product is the product of the localizations.** -/
theorem isLocalizationAway_prod (x : S) (y : T) [IsLocalization.Away x S']
    [IsLocalization.Away y T'] :
    letI : Algebra (S × T) (S' × T') :=
      (RingHom.prodMap (algebraMap S S') (algebraMap T T')).toAlgebra
    IsLocalization.Away ((x, y) : S × T) (S' × T') := by
  let : Algebra (S × T) (S' × T') :=
    (RingHom.prodMap (algebraMap S S') (algebraMap T T')).toAlgebra
  have hmap : ∀ p : S × T, algebraMap (S × T) (S' × T') p =
      (algebraMap S S' p.1, algebraMap T T' p.2) := fun _ => rfl
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun a b h => ?_)
  · rw [hmap, Prod.isUnit_iff]
    exact ⟨IsLocalization.Away.algebraMap_isUnit x, IsLocalization.Away.algebraMap_isUnit y⟩
  · obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj x z.1
    obtain ⟨n, d, hd⟩ := IsLocalization.Away.surj y z.2
    refine ⟨m + n, (c * x ^ n, d * y ^ m), ?_⟩
    rw [hmap, hmap]
    ext
    · show z.1 * (algebraMap S S' x) ^ (m + n) = algebraMap S S' (c * x ^ n)
      rw [pow_add, ← mul_assoc, hc, map_mul, map_pow]
    · show z.2 * (algebraMap T T' y) ^ (m + n) = algebraMap T T' (d * y ^ m)
      rw [pow_add, mul_comm ((algebraMap T T' y) ^ m), ← mul_assoc, hd, map_mul, map_pow]
  · rw [hmap, hmap] at h
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq x (congrArg Prod.fst h)
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq y (congrArg Prod.snd h)
    refine ⟨m + n, ?_⟩
    ext
    · show x ^ (m + n) * a.1 = x ^ (m + n) * b.1
      rw [pow_add, mul_comm (x ^ m), mul_assoc, mul_assoc, hm]
    · show y ^ (m + n) * a.2 = y ^ (m + n) * b.2
      rw [pow_add, mul_assoc, mul_assoc, hn]

end LocalizationProd

section PiIdeal

/-- An ideal of a finite product of rings whose image in every factor is the unit ideal is the unit
ideal. -/
theorem eq_top_of_forall_map_eval {ι : Type*} [Finite ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (𝔞 : Ideal (∀ i, R i))
    (h : ∀ i, 𝔞.map (Pi.evalRingHom R i) = ⊤) : 𝔞 = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hsingle : ∀ i, Pi.single i (1 : R i) ∈ 𝔞 := by
    intro i
    have h1 : (1 : R i) ∈ 𝔞.map (Pi.evalRingHom R i) := by simp [h i]
    obtain ⟨x, hx, hx1⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (Function.surjective_eval i)).mp h1
    have hxi : x i = 1 := hx1
    have : Pi.single i (1 : R i) * x = Pi.single i (1 : R i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hxi]
      · simp [hj]
    rw [← this]
    exact Ideal.mul_mem_left _ _ hx
  rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : ∀ i, R i)]
  exact Ideal.sum_mem _ fun i _ => hsingle i

end PiIdeal

section FiniteType

variable {A B B₀ : Type*} [CommRing A] [CommRing B] [CommRing B₀] [Algebra A B] [Algebra A B₀]

/-- **Finite type modulo a nilpotent ideal of the base.** If `π : B → B₀` is a surjection of
`A`-algebras with kernel `J B` for a nilpotent ideal `J ⊆ A` and `B₀` is of finite type over `A`,
then so is `B`. -/
theorem finiteType_of_surjective_of_ker {J : Ideal A} (hJ : IsNilpotent J)
    (π : B →ₐ[A] B₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : B →+* B₀) = J.map (algebraMap A B)) [Algebra.FiniteType A B₀] :
    Algebra.FiniteType A B := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B₀).out
  let t : Finset B := s.image (Function.surjInv hπ)
  let S : Subalgebra A B := Algebra.adjoin A (t : Set B)
  have hmapS : S.map π = ⊤ := by
    rw [AlgHom.map_adjoin, eq_top_iff, ← hs]
    apply Algebra.adjoin_mono
    intro y hy
    refine ⟨Function.surjInv hπ y, ?_, Function.surjInv_eq hπ y⟩
    simp only [t, Finset.coe_image]
    exact Set.mem_image_of_mem _ hy
  have hstep : ∀ b : B, ∃ x ∈ S, b - x ∈ J.map (algebraMap A B) := by
    intro b
    obtain ⟨x, hx, hxb⟩ : π b ∈ S.map π := by simp [hmapS]
    refine ⟨x, hx, ?_⟩
    rw [← hker, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr hxb.symm
  let P : Submodule A B := Subalgebra.toSubmodule S
  have hbase : (⊤ : Submodule A B) ≤ P ⊔ J • ⊤ := by
    intro b _
    obtain ⟨x, hx, hbx⟩ := hstep b
    have hJ' : b - x ∈ J • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]
      exact hbx
    simpa using Submodule.add_mem_sup (show x ∈ P from hx) hJ'
  have hpow : ∀ k : ℕ, (⊤ : Submodule A B) ≤ P ⊔ (J ^ k) • ⊤ := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact le_sup_right
    | succ k ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (J ^ k) • (⊤ : Submodule A B) ≤ (J ^ k) • (P ⊔ J • ⊤) :=
            Submodule.smul_mono (le_refl _) hbase
        _ = (J ^ k) • P ⊔ (J ^ k) • (J • (⊤ : Submodule A B)) := Submodule.smul_sup _ _ _
        _ ≤ P ⊔ (J ^ (k + 1)) • ⊤ := by
            refine sup_le_sup (Submodule.smul_le_right) ?_
            rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_succ]
  obtain ⟨n, hn⟩ := hJ
  have htop := hpow n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at htop
  exact ⟨⟨t, eq_top_iff.mpr fun b _ => htop Submodule.mem_top⟩⟩

end FiniteType

section Descent

variable {R S U : Type*} [CommRing R] [CommRing S] [CommRing U] [Algebra R S] [Algebra S U]
  [Algebra R U] [IsScalarTower R S U]

/-- **Étaleness descends along a faithfully flat étale map.** If `S → U` is formally étale and
faithfully flat, `R → U` is étale and `S` is of finite presentation over `R`, then `R → S` is
étale. -/
theorem etale_of_faithfullyFlat_of_etale [Algebra.FormallyEtale S U] [Module.FaithfullyFlat S U]
    [Algebra.Etale R U] [Algebra.FinitePresentation R S] : Algebra.Etale R S := by
  have : Module.Flat R S :=
    Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat (R := R) (S := S) U
  have : Algebra.FormallyUnramified R S := by
    constructor
    have : Subsingleton (U ⊗[S] Ω[S⁄R]) :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S U).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality S U _
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Descent

section AwayDescent

variable {A B Γ : Type*} [CommRing A] [CommRing B] [CommRing Γ] [Algebra A B] [Algebra B Γ]
  [Algebra A Γ] [IsScalarTower A B Γ]

/-- **Étaleness of a localization descends along a faithfully flat étale map.** If `B → Γ` is
étale and faithfully flat, `B` is of finite presentation over `A` and `Γ_a` is étale over `A`,
then `B_a` is étale over `A`. -/
theorem etale_away_of_faithfullyFlat [Algebra.Etale B Γ] [Module.FaithfullyFlat B Γ]
    [Algebra.FinitePresentation A B] (a : A)
    (ha : Algebra.Etale A (Localization.Away (algebraMap A Γ a))) :
    Algebra.Etale A (Localization.Away (algebraMap A B a)) := by
  set y := algebraMap A B a
  rw [IsScalarTower.algebraMap_apply A B Γ] at ha
  let Bx := Localization.Away y
  let Γy := Localization.Away (algebraMap B Γ y)
  let : Algebra Bx Γy := (Localization.awayMap (algebraMap B Γ) y).toAlgebra
  have : IsScalarTower B Bx Γy := IsScalarTower.of_algebraMap_eq fun b => by
    show algebraMap B Γy b = Localization.awayMap (algebraMap B Γ) y (algebraMap B Bx b)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ (Submonoid.powers y)) Γy := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have : Algebra.IsPushout B Bx Γ Γy :=
    (Algebra.isPushout_of_isLocalization (A := Bx) (Submonoid.powers y) Γ Γy).symm
  let e : Bx ⊗[B] Γ ≃ₐ[Bx] Γy := Algebra.IsPushout.equiv B Bx Γ Γy
  have : Module.FaithfullyFlat Bx Γy :=
    Module.FaithfullyFlat.of_linearEquiv Bx (Bx ⊗[B] Γ) e.symm.toLinearEquiv
  have : Algebra.FormallyEtale Bx Γy := Algebra.FormallyEtale.of_equiv e
  have : IsScalarTower A Bx Γy := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A B Bx, ← IsScalarTower.algebraMap_apply B Bx Γy,
      IsScalarTower.algebraMap_apply A B Γy]
  have : Algebra.FinitePresentation B Bx := IsLocalization.Away.finitePresentation y
  have : Algebra.FinitePresentation A Bx := Algebra.FinitePresentation.trans A B Bx
  exact etale_of_faithfullyFlat_of_etale (S := Bx) (U := Γy)

end AwayDescent

end Stacks.Etale.PushoutLift

end
