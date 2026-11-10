module

public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import Mathlib.RingTheory.AdicCompletion.Topology
import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.Tactic.Abel
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting to adic topological rings

A formally smooth homomorphism admits continuous lifts from quotients by closed ideals in an
adic complete ring when a positive power of the quotient ideal lies in an ideal of definition.

## Main results

* `RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic`: continuous lifting from a
  closed quotient of an adic complete ring.

## References

* [Stacks Project, Tag 07NJ](https://stacks.math.columbia.edu/tag/07NJ)
-/

@[expose] public section

universe u v w

namespace RingHom.FormallySmoothTop

private theorem discrete_quotient_of_adic_power
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I K : Ideal A) (hI : IsAdic I) {n : ℕ} (_hn : 1 ≤ n) (hIK : I ^ n ≤ K) :
    DiscreteTopology (A ⧸ K) := by
  have hpowOpen : IsOpen ((I ^ n : Ideal A) : Set A) := (isAdic_iff.mp hI).1 n
  have himage : Ideal.Quotient.mk K '' ((I ^ n : Ideal A) : Set A) =
      ({0} : Set (A ⧸ K)) := by
    ext y
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIK hx)
    · rintro rfl
      exact ⟨0, (I ^ n).zero_mem, by simp⟩
  have hzero : IsOpen ({0} : Set (A ⧸ K)) := by
    rw [← himage]
    exact QuotientRing.isOpenMap_coe K _ hpowOpen
  exact discreteTopology_iff_isOpen_singleton_zero.mpr hzero

private theorem sup_square_le {A : Type*} [CommRing A]
    (P Q T : Ideal A) (hPP : P * P ≤ T) (hPQ : P * Q ≤ T)
    (hQP : Q * P ≤ T) (hQQ : Q * Q ≤ T) :
    (P ⊔ Q) ^ 2 ≤ T := by
  rw [pow_two, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
  exact sup_le (sup_le hPP hPQ) (sup_le hQP hQQ)

private theorem exists_formallySmooth_lift
    {R : Type u} {S : Type v} {E : Type w} {B : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing E] [TopologicalSpace E] [DiscreteTopology E]
    [CommRing B] [TopologicalSpace B] [DiscreteTopology B]
    (f : R →+* S) (hfs : FormallySmoothTop.{w} f)
    (p : E →+* B) (hp : Function.Surjective p)
    (g : R →+* E) (hg : Continuous g)
    (ψ : S →+* B) (hψ : Continuous ψ)
    (hcomm : ψ.comp f = p.comp g)
    (hker : (RingHom.ker p) ^ 2 = ⊥) :
    ∃ φ : S →+* E, Continuous φ ∧ φ.comp f = g ∧ p.comp φ = ψ := by
  let L := RingHom.ker p
  let e : E ⧸ L ≃+* B := RingHom.quotientKerEquivOfSurjective hp
  let ψ' : S →+* E ⧸ L := e.symm.toRingHom.comp ψ
  let : DiscreteTopology (E ⧸ L) :=
    QuotientAddGroup.discreteTopology (isOpen_discrete (L : Set E))
  have hψ' : Continuous ψ' :=
    (continuous_of_discreteTopology : Continuous (e.symm : B → E ⧸ L)).comp hψ
  have he_mk (x : E) : e (Ideal.Quotient.mk L x) = p x :=
    RingHom.quotientKerEquivOfSurjective_apply_mk hp x
  have hcomm' : ψ'.comp f = (Ideal.Quotient.mk L).comp g := by
    ext r
    apply e.injective
    change e (e.symm (ψ (f r))) = e (Ideal.Quotient.mk L (g r))
    rw [RingEquiv.apply_symm_apply, he_mk]
    exact DFunLike.congr_fun hcomm r
  obtain ⟨φ, hφc, hφf, hφq⟩ := hfs E L hker g hg ψ' hψ' hcomm'
  refine ⟨φ, hφc, hφf, ?_⟩
  ext s
  calc
    p (φ s) = e (Ideal.Quotient.mk L (φ s)) := (he_mk _).symm
    _ = e (ψ' s) := congrArg e (DFunLike.congr_fun hφq s)
    _ = ψ s := by simp [ψ']

private theorem continuous_factor_quotient_adic_discrete
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (J K : Ideal A) (hJK : J ≤ K) :
    Continuous (Ideal.Quotient.factor hJK : A ⧸ J →+* A ⧸ K) := by
  rw [(QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.continuous_iff]
  have hmk : Continuous (Ideal.Quotient.mk K : A → A ⧸ K) :=
    (QuotientRing.isOpenQuotientMap_mk K).isQuotientMap.continuous
  convert hmk using 1
  ext x
  simp

/-- Reducing a lift modulo a larger ideal preserves compatibility with the base map. -/
private theorem factor_comp_comp_eq_mk_comp
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (g : R →+* A) {J K : Ideal A} (h : J ≤ K) {φ : S →+* A ⧸ J}
    (hφ : φ.comp f = (Ideal.Quotient.mk J).comp g) :
    ((Ideal.Quotient.factor h).comp φ).comp f = (Ideal.Quotient.mk K).comp g := by
  rw [RingHom.comp_assoc, hφ, ← RingHom.comp_assoc, Ideal.Quotient.factor_comp_mk]

private theorem quotient_factor_ker_sq
    {A : Type*} [CommRing A] {K₁ K₂ : Ideal A}
    (h₁₂ : K₁ ≤ K₂) (h₂₁ : K₂ ^ 2 ≤ K₁) :
    (RingHom.ker (Ideal.Quotient.factor h₁₂)) ^ 2 = ⊥ := by
  rw [Ideal.Quotient.factor_ker h₁₂, ← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  simpa [Ideal.mk_ker] using h₂₁

private theorem exists_lift_quotient_step
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (hfs : FormallySmoothTop.{w} f)
    (I : Ideal A) (hI : IsAdic I)
    (g : R →+* A) (hg : Continuous g)
    (K₁ K₂ : Ideal A) (h₁₂ : K₁ ≤ K₂) (h₂₁ : K₂ ^ 2 ≤ K₁)
    {n : ℕ} (hn : 1 ≤ n) (hIK : I ^ n ≤ K₁)
    (ψ : S →+* A ⧸ K₂)
    (hψ : Continuous ψ)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk K₂).comp g) :
    ∃ φ : S →+* A ⧸ K₁,
      Continuous φ ∧
      φ.comp f = (Ideal.Quotient.mk K₁).comp g ∧
      (Ideal.Quotient.factor h₁₂).comp φ = ψ := by
  let : DiscreteTopology (A ⧸ K₁) := discrete_quotient_of_adic_power I K₁ hI hn hIK
  let : DiscreteTopology (A ⧸ K₂) :=
    discrete_quotient_of_adic_power I K₂ hI hn (le_trans hIK h₁₂)
  have hg' : Continuous ((Ideal.Quotient.mk K₁).comp g) :=
    (QuotientRing.isOpenQuotientMap_mk K₁).isQuotientMap.continuous.comp hg
  exact exists_formallySmooth_lift f hfs
    (Ideal.Quotient.factor h₁₂) (Ideal.Quotient.factor_surjective h₁₂)
    ((Ideal.Quotient.mk K₁).comp g) hg' ψ hψ hcomm (quotient_factor_ker_sq h₁₂ h₂₁)

private abbrev gridIdeal {A : Type*} [CommRing A]
    (J I : Ideal A) (t n : ℕ) : Ideal A := J ^ (t * n) ⊔ I ^ n

private abbrev quotientIdeal {A : Type*} [CommRing A]
    (J I : Ideal A) (n : ℕ) : Ideal A := J ⊔ I ^ n

private theorem grid_ideal_power_le
    {A : Type*} [CommRing A] (J I : Ideal A) (t n : ℕ)
    (hJI : J ^ t ≤ I) : J ^ (t * n) ≤ I ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono hJI n

private theorem grid_ideal_succ_le {A : Type*} [CommRing A] (J I : Ideal A) (t n : ℕ) :
    gridIdeal J I t (n + 1) ≤ gridIdeal J I t n :=
  sup_le ((Ideal.pow_le_pow_right (Nat.mul_le_mul_left t n.le_succ)).trans le_sup_left)
    ((Ideal.pow_le_pow_right n.le_succ).trans le_sup_right)

private theorem grid_ideal_le_quotient_ideal {A : Type*} [CommRing A] (J I : Ideal A) {t : ℕ}
    (hJI : J ^ t ≤ I) (n : ℕ) : gridIdeal J I t n ≤ quotientIdeal J I n :=
  sup_le ((grid_ideal_power_le J I t n hJI).trans le_sup_right) le_sup_right

private theorem grid_ideal_square_le
    {A : Type*} [CommRing A] (J I : Ideal A) (t n : ℕ)
    (hn : 1 ≤ n) (hJI : J ^ t ≤ I) :
    (gridIdeal J I t n) ^ 2 ≤ gridIdeal J I t (n + 1) := by
  let P := J ^ (t * n)
  let Q := I ^ n
  let T := J ^ (t * (n + 1)) ⊔ I ^ (n + 1)
  have hP : P ≤ Q := grid_ideal_power_le J I t n hJI
  have ht_le : t ≤ t * n := by simpa using Nat.mul_le_mul_left t hn
  have hPP : P * P ≤ T := by
    apply le_trans ?_ (le_sup_left : J ^ (t * (n + 1)) ≤ T)
    calc
      P * P = J ^ (t * n + t * n) := by
        simp [P, ← pow_add]
      _ ≤ J ^ (t * (n + 1)) :=
        Ideal.pow_le_pow_right (by nlinarith [ht_le])
  have hPQ : P * Q ≤ T := by
    apply le_trans ?_ (le_sup_right : I ^ (n + 1) ≤ T)
    calc
      P * Q ≤ I ^ n * I ^ n := Ideal.mul_mono hP le_rfl
      _ = I ^ (n + n) := (pow_add I n n).symm
      _ ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  have hQP : Q * P ≤ T := by rwa [mul_comm Q P]
  have hQQ : Q * Q ≤ T := by
    apply le_trans ?_ (le_sup_right : I ^ (n + 1) ≤ T)
    calc
      Q * Q = I ^ (n + n) := by simp [Q, ← pow_add]
      _ ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  simpa [P, Q, T, gridIdeal] using sup_square_le P Q T hPP hPQ hQP hQQ

private theorem exists_diagonal_lift
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (hfs : FormallySmoothTop.{w} f)
    (I J : Ideal A) (hI : IsAdic I)
    (g : R →+* A) (hg : Continuous g)
    (t n : ℕ) (_ht : 1 ≤ t) (hn : 1 ≤ n) (hJI : J ^ t ≤ I)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (hψf : ψ.comp f = (Ideal.Quotient.mk J).comp g)
    (φ : S →+* A ⧸ gridIdeal J I t n)
    (hφc : Continuous φ)
    (hφf : φ.comp f = (Ideal.Quotient.mk (gridIdeal J I t n)).comp g)
    (hφψ : (Ideal.Quotient.factor
      (grid_ideal_le_quotient_ideal J I hJI n)).comp φ =
      (Ideal.Quotient.factor (show J ≤ quotientIdeal J I n from le_sup_left)).comp ψ) :
    ∃ φ' : S →+* A ⧸ gridIdeal J I t (n + 1),
      Continuous φ' ∧
      φ'.comp f = (Ideal.Quotient.mk (gridIdeal J I t (n + 1))).comp g ∧
      ((Ideal.Quotient.factor
        (grid_ideal_succ_le J I t n)).comp φ') = φ ∧
      (Ideal.Quotient.factor
        (grid_ideal_le_quotient_ideal J I hJI (n + 1))).comp φ' =
        (Ideal.Quotient.factor (show J ≤ quotientIdeal J I (n + 1) from le_sup_left)).comp ψ := by
  let K₀ := gridIdeal J I t n
  let K₁ := gridIdeal J I t (n + 1)
  let C₀ := quotientIdeal J I n
  let C₁ := quotientIdeal J I (n + 1)
  have hK₀C₀ : K₀ ≤ C₀ := grid_ideal_le_quotient_ideal J I hJI n
  have hC₁C₀ : C₁ ≤ C₀ := by
    dsimp [C₁, C₀, quotientIdeal]
    exact sup_le le_sup_left ((Ideal.pow_le_pow_right (I := I) (Nat.le_succ n)).trans le_sup_right)
  have hK₁K₀ : K₁ ≤ K₀ := grid_ideal_succ_le J I t n
  have hK₁C₁ : K₁ ≤ C₁ := grid_ideal_le_quotient_ideal J I hJI (n + 1)
  have hK₀sq : K₀ ^ 2 ≤ K₁ := grid_ideal_square_le J I t n hn hJI
  have hsup : K₀ ⊔ C₁ = C₀ := by
    apply le_antisymm
    · exact sup_le hK₀C₀ hC₁C₀
    · dsimp [C₀, quotientIdeal]
      exact sup_le (le_trans le_sup_left le_sup_right) (le_trans le_sup_right le_sup_left)
  let ψ₀ : S →+* A ⧸ C₀ :=
    (Ideal.Quotient.factor (show J ≤ C₀ from le_sup_left)).comp ψ
  let ψ₁ : S →+* A ⧸ C₁ :=
    (Ideal.Quotient.factor (show J ≤ C₁ from le_sup_left)).comp ψ
  have hψ₁c : Continuous ψ₁ :=
    (continuous_factor_quotient_adic_discrete J C₁ le_sup_left).comp hψ
  have hψ₁f : ψ₁.comp f = (Ideal.Quotient.mk C₁).comp g := by
    exact factor_comp_comp_eq_mk_comp f g _ hψf
  have hψ₁red : (Ideal.Quotient.factor hC₁C₀).comp ψ₁ =
      (Ideal.Quotient.factor (show J ≤ C₀ from le_sup_left)).comp ψ := by
    dsimp [ψ₁]
    rw [← RingHom.comp_assoc, Ideal.Quotient.factor_comp]
  have hcompat :
      (Ideal.Quotient.factor hK₀C₀).comp φ =
        (Ideal.Quotient.factor hC₁C₀).comp ψ₁ := hφψ.trans hψ₁red.symm
  let B₀ := A ⧸ K₀
  let B₁ := A ⧸ C₁
  let C := A ⧸ C₀
  let E := A ⧸ K₁
  let u : B₀ →+* C := Ideal.Quotient.factor hK₀C₀
  let v : B₁ →+* C := Ideal.Quotient.factor hC₁C₀
  let a : E →+* B₀ := Ideal.Quotient.factor hK₁K₀
  let b : E →+* B₁ := Ideal.Quotient.factor hK₁C₁
  let P := RingHom.pullback u v
  let pair : S →+* P := RingHom.codRestrict (RingHom.prod φ ψ₁) P (by
    intro s
    change u (φ s) = v (ψ₁ s)
    exact congrArg (fun q : S →+* C => q s) hcompat)
  let q : E →+* P := RingHom.codRestrict (RingHom.prod a b) P (by
    intro x
    change u (a x) = v (b x)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.factor hK₀C₀
        (Ideal.Quotient.factor hK₁K₀ (Ideal.Quotient.mk K₁ x)) =
      Ideal.Quotient.factor hC₁C₀
        (Ideal.Quotient.factor hK₁C₁ (Ideal.Quotient.mk K₁ x))
    simp only [Ideal.Quotient.factor_mk])
  let gE : R →+* E := (Ideal.Quotient.mk K₁).comp g
  let : DiscreteTopology B₀ := discrete_quotient_of_adic_power I K₀ hI hn le_sup_right
  let : DiscreteTopology B₁ :=
    discrete_quotient_of_adic_power I C₁ hI (by omega) le_sup_right
  let : DiscreteTopology C := discrete_quotient_of_adic_power I C₀ hI hn le_sup_right
  let : DiscreteTopology E :=
    discrete_quotient_of_adic_power I K₁ hI (by omega) (le_sup_right)
  have hpairc : Continuous pair := Continuous.subtype_mk (hφc.prodMk hψ₁c) _
  have hgEc : Continuous gE :=
    ((QuotientRing.isOpenQuotientMap_mk K₁).isQuotientMap.continuous).comp hg
  have hqsurj : Function.Surjective q := by
    intro z
    rcases z with ⟨⟨x, y⟩, hxy⟩
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hxy₀ : Ideal.Quotient.mk C₀ x₀ = Ideal.Quotient.mk C₀ y₀ := by
      change Ideal.Quotient.factor hK₀C₀ (Ideal.Quotient.mk K₀ x₀) =
        Ideal.Quotient.factor hC₁C₀ (Ideal.Quotient.mk C₁ y₀) at hxy
      simpa only [Ideal.Quotient.factor_mk] using hxy
    have hmem : x₀ - y₀ ∈ K₀ ⊔ C₁ := by
      rw [hsup]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x₀ y₀).mp hxy₀
    obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩ := Submodule.mem_sup.mp hmem
    refine ⟨Ideal.Quotient.mk K₁ (x₀ - x₁), Subtype.ext (Prod.ext ?_ ?_)⟩
    · change Ideal.Quotient.mk K₀ (x₀ - x₁) = Ideal.Quotient.mk K₀ x₀
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      simpa using K₀.neg_mem hx₁
    · change Ideal.Quotient.mk C₁ (x₀ - x₁) = Ideal.Quotient.mk C₁ y₀
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← eq_sub_iff_add_eq.mp hxy₁]
      convert hy₁ using 1
      abel
  have hproj : (RingHom.pullbackFst u v).comp q = a := by
    ext x
    simp [q, RingHom.codRestrict_apply, RingHom.prod_apply,
      RingHom.pullbackFst, RingHom.comp_apply]
  have hkerA : (RingHom.ker a) ^ 2 = ⊥ := quotient_factor_ker_sq hK₁K₀ hK₀sq
  have hkerle : RingHom.ker q ≤ RingHom.ker a := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [← hproj, RingHom.comp_apply, hx, map_zero]
  have hkerq : (RingHom.ker q) ^ 2 = ⊥ :=
    eq_bot_iff.mpr ((pow_le_pow_left' hkerle 2).trans hkerA.le)
  have hcommStep : pair.comp f = q.comp gE := by
    refine RingHom.ext fun r => Subtype.ext (Prod.ext ?_ ?_)
    · change φ (f r) = Ideal.Quotient.factor hK₁K₀
        (Ideal.Quotient.mk K₁ (g r))
      rw [Ideal.Quotient.factor_mk]
      exact congrArg (fun k : R →+* B₀ => k r) hφf
    · change ψ₁ (f r) = Ideal.Quotient.factor hK₁C₁
        (Ideal.Quotient.mk K₁ (g r))
      rw [Ideal.Quotient.factor_mk]
      exact congrArg (fun k : R →+* B₁ => k r) hψ₁f
  obtain ⟨φ', hφ'c, hφ'f, hqφ'⟩ := exists_formallySmooth_lift f hfs q hqsurj
    gE hgEc pair hpairc hcommStep hkerq
  have hprojS : (RingHom.pullbackFst u v).comp pair = φ := by
    ext s
    simp [pair, RingHom.codRestrict_apply, RingHom.prod_apply,
      RingHom.pullbackFst, RingHom.comp_apply]
  have hprojT : (RingHom.pullbackSnd u v).comp pair = ψ₁ := by
    ext s
    simp [pair, RingHom.codRestrict_apply, RingHom.prod_apply,
      RingHom.pullbackSnd, RingHom.comp_apply]
  have hprojSnd : (RingHom.pullbackSnd u v).comp q = b := by
    ext x
    simp [q, RingHom.codRestrict_apply, RingHom.prod_apply,
      RingHom.pullbackSnd, RingHom.comp_apply]
  have hφ'old : a.comp φ' = φ := by rw [← hproj, RingHom.comp_assoc, hqφ', hprojS]
  have hφ'psi₁ : b.comp φ' = ψ₁ := by rw [← hprojSnd, RingHom.comp_assoc, hqφ', hprojT]
  exact ⟨φ', hφ'c, hφ'f, hφ'old, hφ'psi₁⟩

private theorem ideal_sup_pow_le_sup_pow
    {A : Type*} [CommRing A] (J I : Ideal A) (n : ℕ) :
    (J ⊔ I) ^ n ≤ J ^ n ⊔ I := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      (J ⊔ I) ^ n * (J ⊔ I) ≤ (J ^ n ⊔ I) * (J ⊔ I) :=
        Ideal.mul_mono ih le_rfl
      _ ≤ J ^ (n + 1) ⊔ I := by
        have hPP : J ^ n * J ≤ J ^ (n + 1) ⊔ I := by
          rw [pow_succ]
          exact le_sup_left
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        exact sup_le (sup_le hPP ((Ideal.mul_le_right : J ^ n * I ≤ I).trans le_sup_right))
          (sup_le ((Ideal.mul_le_left : I * J ≤ I).trans le_sup_right)
            ((Ideal.mul_le_left : I * I ≤ I).trans le_sup_right))

private theorem ideal_sup_pow_le_of_pow_le
    {A : Type*} [CommRing A] (J I : Ideal A) (t : ℕ)
    (hJI : J ^ t ≤ I) : (J ⊔ I) ^ t ≤ I :=
  (ideal_sup_pow_le_sup_pow J I t).trans (sup_le hJI le_rfl)

private theorem ideal_pow_le_self
    {A : Type*} [CommRing A] (J : Ideal A) {n : ℕ} (hn : 1 ≤ n) :
    J ^ n ≤ J := by
  simpa using
    (Ideal.pow_le_pow_right (I := J) hn : J ^ n ≤ J ^ 1)

private theorem pow_sup_le_sup {A : Type*} [CommRing A] (J I : Ideal A) {n : ℕ} (hn : 1 ≤ n) :
    J ^ n ⊔ I ≤ J ⊔ I :=
  sup_le ((ideal_pow_le_self J hn).trans le_sup_left) le_sup_right

private theorem ideal_sup_power_square_le
    {A : Type*} [CommRing A] (J I : Ideal A) (n : ℕ) (hn : 1 ≤ n) :
    (J ^ n ⊔ I) ^ 2 ≤ J ^ (n + 1) ⊔ I := by
  have hPP : J ^ n * J ^ n ≤ J ^ (n + 1) ⊔ I := by
    apply le_trans ?_ (le_sup_left : J ^ (n + 1) ≤ J ^ (n + 1) ⊔ I)
    calc
      J ^ n * J ^ n = J ^ (n + n) := by rw [← pow_add]
      _ ≤ J ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  exact sup_square_le _ _ _ hPP ((Ideal.mul_le_right : J ^ n * I ≤ I).trans le_sup_right)
    ((Ideal.mul_le_left : I * J ^ n ≤ I).trans le_sup_right)
    ((Ideal.mul_le_left : I * I ≤ I).trans le_sup_right)

private theorem exists_initial_power_lift
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (hfs : FormallySmoothTop.{w} f)
    (I J : Ideal A) (hI : IsAdic I)
    (g : R →+* A) (hg : Continuous g)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (hψf : ψ.comp f = (Ideal.Quotient.mk J).comp g) (n : ℕ) :
    ∃ φ : S →+* A ⧸ (J ^ (n + 1) ⊔ I),
      Continuous φ ∧
      φ.comp f = (Ideal.Quotient.mk (J ^ (n + 1) ⊔ I)).comp g ∧
      (Ideal.Quotient.factor (pow_sup_le_sup J I n.succ_pos)).comp φ =
        (Ideal.Quotient.factor (show J ≤ J ⊔ I from le_sup_left)).comp ψ := by
  let C := J ⊔ I
  let ψC : S →+* A ⧸ C :=
    (Ideal.Quotient.factor (show J ≤ C from le_sup_left)).comp ψ
  have hψCc : Continuous ψC :=
    (continuous_factor_quotient_adic_discrete J C le_sup_left).comp hψ
  have hψCf : ψC.comp f = (Ideal.Quotient.mk C).comp g := by
    exact factor_comp_comp_eq_mk_comp f g _ hψf
  induction n with
  | zero =>
    let K := J ^ (0 + 1) ⊔ I
    have hCK : C ≤ K := by simp [C, K]
    have hKC : K ≤ C := by simp [C, K]
    let φK := (Ideal.Quotient.factor hCK).comp ψC
    have hφKc : Continuous φK :=
      (continuous_factor_quotient_adic_discrete C K hCK).comp hψCc
    have hφKf : φK.comp f = (Ideal.Quotient.mk K).comp g := by
      exact factor_comp_comp_eq_mk_comp f g _ hψCf
    have hφKC : (Ideal.Quotient.factor hKC).comp φK = ψC := by
      change (Ideal.Quotient.factor hKC).comp
        ((Ideal.Quotient.factor hCK).comp ψC) = ψC
      rw [← RingHom.comp_assoc, Ideal.Quotient.factor_comp]
      have heq : hCK.trans hKC = le_rfl := Subsingleton.elim _ _
      rw [heq, Ideal.Quotient.factor_eq]
      simp
    refine ⟨φK, hφKc, hφKf, ?_⟩
    simpa [K, C, ψC] using hφKC
  | succ n ih =>
    obtain ⟨φ, hφc, hφf, hφψ⟩ := ih
    let Kold := J ^ (n + 1) ⊔ I
    let Knew := J ^ (n + 2) ⊔ I
    have hnewold : Knew ≤ Kold := by
      dsimp [Knew, Kold]
      exact sup_le
        (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)) |>.trans le_sup_left)
        le_sup_right
    have holdC : Kold ≤ C := pow_sup_le_sup J I n.succ_pos
    have hnewC : Knew ≤ C := le_trans hnewold holdC
    have hsq : Kold ^ 2 ≤ Knew := by
      dsimp [Kold, Knew]
      exact ideal_sup_power_square_le J I (n + 1) (by omega)
    have hIK : I ^ 1 ≤ Knew := (pow_one I).le.trans le_sup_right
    obtain ⟨φ', hφ'c, hφ'f, hφ'old⟩ :=
      exists_lift_quotient_step f hfs I hI g hg Knew Kold hnewold hsq
        (n := 1) (by norm_num)
        hIK φ hφc hφf
    refine ⟨φ', hφ'c, hφ'f, Eq.trans ?_ hφψ⟩
    rw [← hφ'old, ← RingHom.comp_assoc, Ideal.Quotient.factor_comp]

private theorem exists_initial_lift_at_power
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (hfs : FormallySmoothTop.{w} f)
    (I J : Ideal A) (hI : IsAdic I)
    (g : R →+* A) (hg : Continuous g)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (hψf : ψ.comp f = (Ideal.Quotient.mk J).comp g)
    (t : ℕ) (ht : 1 ≤ t) :
    ∃ φ : S →+* A ⧸ (J ^ t ⊔ I),
      Continuous φ ∧
      φ.comp f = (Ideal.Quotient.mk (J ^ t ⊔ I)).comp g ∧
      (Ideal.Quotient.factor (pow_sup_le_sup J I ht)).comp φ =
        (Ideal.Quotient.factor (show J ≤ J ⊔ I from le_sup_left)).comp ψ := by
  have hsub : t - 1 + 1 = t := Nat.sub_add_cancel ht
  obtain ⟨φ, hφc, hφf, hφψ⟩ :=
    exists_initial_power_lift f hfs I J hI g hg ψ hψ hψf (t - 1)
  have hOldNew : J ^ (t - 1 + 1) ⊔ I ≤ J ^ t ⊔ I := by
    rw [hsub]
  let φ' : S →+* A ⧸ (J ^ t ⊔ I) :=
    (Ideal.Quotient.factor hOldNew).comp φ
  refine ⟨φ', ?_, ?_, ?_⟩
  · change Continuous ((Ideal.Quotient.factor hOldNew).comp φ)
    exact (continuous_factor_quotient_adic_discrete
      (J ^ (t - 1 + 1) ⊔ I) (J ^ t ⊔ I) hOldNew).comp hφc
  · exact factor_comp_comp_eq_mk_comp f g _ hφf
  · change (Ideal.Quotient.factor (pow_sup_le_sup J I ht)).comp
      ((Ideal.Quotient.factor hOldNew).comp φ) = _
    rw [← RingHom.comp_assoc, Ideal.Quotient.factor_comp]
    exact hφψ

private theorem mem_closed_ideal_of_sup_powers
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I J : Ideal A) (hI : IsAdic I) (hJ : IsClosed (J : Set A))
    {x : A} (hx : ∀ n : ℕ, x ∈ J ⊔ I ^ n) : x ∈ J := by
  by_contra hxJ
  have hnhds' : ({y : A | y ∉ J} : Set A) ∈ @nhds A I.adicTopology x := by
    rw [← hI]
    exact hJ.isOpen_compl.mem_nhds hxJ
  obtain ⟨n, -, hsub⟩ := (Ideal.hasBasis_nhds_adic I x).mem_iff.mp hnhds'
  obtain ⟨j, hj, i, hi, hji⟩ := Submodule.mem_sup.mp (hx n)
  have hplus : j ∈ (fun y : A => x + y) '' ((I ^ n : Ideal A) : Set A) := by
    refine ⟨-i, I ^ n |>.neg_mem hi, ?_⟩
    rw [← hji]
    abel_nf
  exact hsub hplus hj

/-- A formally smooth homomorphism lifts continuously through a closed quotient of an adic
complete ring, provided a positive power of the quotient ideal lies in an ideal of definition. -/
@[stacks 07NJ]
theorem exists_continuous_lift_of_isAdic
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (f : R →+* S) (n : Ideal S) (hn : IsAdic n)
    (hf : RingHom.FormallySmoothTop.{w} f)
    (I : Ideal A) (hI : IsAdic I) [IsAdicComplete I A]
    (J : Ideal A) (hJ : IsClosed (J : Set A))
    (t : ℕ) (ht : 1 ≤ t) (hJI : J ^ t ≤ I)
    (g : R →+* A) (hg : Continuous g)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk J).comp g) :
    ∃ φ : S →+* A, Continuous φ ∧ φ.comp f = g ∧
      (Ideal.Quotient.mk J).comp φ = ψ := by
  obtain ⟨φ₀, hφ₀c, hφ₀f, hφ₀ψ⟩ :=
    exists_initial_lift_at_power f hf I J hI g hg ψ hψ hcomm t ht
  have hGridMono (k : ℕ) := grid_ideal_succ_le J I t k
  have hGridToI (k : ℕ) : gridIdeal J I t k ≤ I ^ k := by
    dsimp [gridIdeal]
    exact sup_le (grid_ideal_power_le J I t k hJI) le_rfl
  have hGridC (k : ℕ) := grid_ideal_le_quotient_ideal J I hJI (k + 1)
  have hJC (k : ℕ) : J ≤ quotientIdeal J I (k + 1) := le_sup_left
  have hbaseGrid : gridIdeal J I t 1 = J ^ t ⊔ I := by
    simp [gridIdeal]
  have hbaseToGrid : J ^ t ⊔ I ≤ gridIdeal J I t 1 := by
    rw [hbaseGrid]
  let hφ₀grid : S →+* A ⧸ gridIdeal J I t 1 :=
    (Ideal.Quotient.factor hbaseToGrid).comp φ₀
  have hφ₀gridc : Continuous hφ₀grid :=
    (continuous_factor_quotient_adic_discrete
      (J ^ t ⊔ I) (gridIdeal J I t 1) hbaseToGrid).comp hφ₀c
  have hφ₀gridf :
      hφ₀grid.comp f =
        (Ideal.Quotient.mk (gridIdeal J I t 1)).comp g := by
    exact factor_comp_comp_eq_mk_comp f g _ hφ₀f
  have hbaseC : J ^ t ⊔ I ≤ quotientIdeal J I 1 := by
    dsimp [quotientIdeal]
    apply sup_le
    · exact (ideal_pow_le_self J ht).trans
        (show J ≤ J ⊔ I ^ 1 from le_sup_left)
    · simpa only [pow_one] using (le_sup_right : I ≤ J ⊔ I)
  have hbaseFactors :
      (Ideal.Quotient.factor (hGridC 0)).comp
          (Ideal.Quotient.factor hbaseToGrid) =
        Ideal.Quotient.factor hbaseC := by
    ext x
    simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk]
  have hφ₀gridψ :
      (Ideal.Quotient.factor (hGridC 0)).comp hφ₀grid =
        (Ideal.Quotient.factor (hJC 0)).comp ψ := by
    have htoC1 : J ⊔ I ≤ quotientIdeal J I 1 := by simp [quotientIdeal]
    change (Ideal.Quotient.factor (hGridC 0)).comp
      ((Ideal.Quotient.factor hbaseToGrid).comp φ₀) = _
    have h := congrArg (Ideal.Quotient.factor htoC1).comp hφ₀ψ
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, Ideal.Quotient.factor_comp,
      Ideal.Quotient.factor_comp] at h
    rwa [← RingHom.comp_assoc, hbaseFactors]
  let D (k : ℕ) :=
    Σ φ : S →+* A ⧸ gridIdeal J I t (k + 1),
      Σ φprev : S →+* A ⧸ gridIdeal J I t k,
        PLift (Continuous φ ∧
        φ.comp f = (Ideal.Quotient.mk (gridIdeal J I t (k + 1))).comp g ∧
        (Ideal.Quotient.factor (hGridC k)).comp φ =
          (Ideal.Quotient.factor (hJC k)).comp ψ ∧
        (Ideal.Quotient.factor (hGridMono k)).comp φ = φprev)
  let φprev₀ : S →+* A ⧸ gridIdeal J I t 0 :=
    (Ideal.Quotient.factor (hGridMono 0)).comp hφ₀grid
  have init : D 0 :=
    ⟨hφ₀grid, φprev₀, ⟨⟨hφ₀gridc, hφ₀gridf, hφ₀gridψ, rfl⟩⟩⟩
  let step : ∀ k, D k → D (k + 1) := by
    intro k d
    rcases d with ⟨φk, _, ⟨⟨hφkc, hφkf, hφkψ, _⟩⟩⟩
    let hstepExists :=
      exists_diagonal_lift f hf I J hI g hg t (k + 1) ht (by omega) hJI ψ hψ
        hcomm φk hφkc hφkf hφkψ
    let φnext := Classical.choose hstepExists
    let hnextSpec := Classical.choose_spec hstepExists
    exact ⟨φnext, φk,
      ⟨⟨hnextSpec.1, hnextSpec.2.1, hnextSpec.2.2.2, hnextSpec.2.2.1⟩⟩⟩
  have hstepPrev (k : ℕ) (d : D k) : (step k d).2.1 = d.1 := by
    rcases d with ⟨φ, φprev, ⟨⟨h₁, h₂, h₃, h₄⟩⟩⟩
    rfl
  let seq : (k : ℕ) → D k := Nat.rec init step
  have hseqPrev (k : ℕ) :
      (Ideal.Quotient.factor (hGridMono (k + 1))).comp (seq (k + 1)).1 =
        (seq k).1 := by
    change (Ideal.Quotient.factor (hGridMono (k + 1))).comp
        (step k (seq k)).1 = (seq k).1
    rw [← hstepPrev k (seq k)]
    exact (step k (seq k)).2.2.down.2.2.2
  let ha : StrictMono (fun k : ℕ => k + 1) :=
    strictMono_nat_of_lt_succ (fun k => Nat.lt_succ_self (k + 1))
  let qmap (k : ℕ) : S →+* A ⧸ I ^ (k + 1) :=
    (Ideal.Quotient.factor (hGridToI (k + 1))).comp (seq k).1
  have hqcompat : ∀ k : ℕ,
      (Ideal.Quotient.factorPow I (ha.monotone (Nat.le_succ k))).comp (qmap (k + 1)) =
        qmap k := by
    intro k
    have hpow : I ^ (k + 2) ≤ I ^ (k + 1) :=
      Ideal.pow_le_pow_right (Nat.le_succ (k + 1))
    change (Ideal.Quotient.factor hpow).comp (qmap (k + 1)) = qmap k
    dsimp only [qmap]
    rw [← hseqPrev k, ← RingHom.comp_assoc, ← RingHom.comp_assoc, Ideal.Quotient.factor_comp,
      Ideal.Quotient.factor_comp]
  let φ : S →+* A :=
    IsAdicComplete.StrictMono.liftRingHom I ha qmap (fun {k} => hqcompat k)
  have hφI (k : ℕ) :
      (Ideal.Quotient.mk (I ^ (k + 1))).comp φ = qmap k := by
    simpa [φ] using
      (IsAdicComplete.StrictMono.mk_comp_liftRingHom I ha qmap
        (fun {m} => hqcompat m) (n := k))
  have hφC (k : ℕ) :
      (Ideal.Quotient.mk (quotientIdeal J I (k + 1))).comp φ =
        (Ideal.Quotient.factor (hJC k)).comp ψ := by
    rw [← Ideal.Quotient.factor_comp_mk
        (show I ^ (k + 1) ≤ quotientIdeal J I (k + 1) from le_sup_right),
      RingHom.comp_assoc, hφI k]
    dsimp only [qmap]
    rw [← RingHom.comp_assoc, Ideal.Quotient.factor_comp]
    exact (seq k).2.2.down.2.2.1
  have hφJ : (Ideal.Quotient.mk J).comp φ = ψ := by
    ext s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ s)
    have hdiff : φ s - a ∈ J := by
      apply mem_closed_ideal_of_sup_powers I J hI hJ
      intro k
      have hmemC : φ s - a ∈ quotientIdeal J I (k + 1) := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (φ s) a).1
        calc
          Ideal.Quotient.mk (quotientIdeal J I (k + 1)) (φ s) =
              (Ideal.Quotient.factor (hJC k)) (ψ s) := by
                simpa [RingHom.comp_apply] using
                  congrArg (fun q : S →+* A ⧸ quotientIdeal J I (k + 1) => q s) (hφC k)
          _ = Ideal.Quotient.mk (quotientIdeal J I (k + 1)) a := by
                rw [← ha]
                simp
      have hle : quotientIdeal J I (k + 1) ≤ J ⊔ I ^ k := by
        dsimp [quotientIdeal]
        exact sup_le le_sup_left
          ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans le_sup_right)
      exact hle hmemC
    calc
      ((Ideal.Quotient.mk J).comp φ) s = Ideal.Quotient.mk J a :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem (φ s) a).2 hdiff
      _ = ψ s := ha
  have hIopen : IsOpen (I : Set A) := by
    simpa using (isAdic_iff.mp hI).1 1
  let U : Set (A ⧸ J) := (Ideal.Quotient.mk J) '' (I : Set A)
  have hUopen : IsOpen U := QuotientRing.isOpenMap_coe J _ hIopen
  have hUzero : (0 : A ⧸ J) ∈ U := ⟨0, I.zero_mem, by simp⟩
  have hpre : ψ ⁻¹' U ∈ nhds (0 : S) :=
    (hψ.isOpen_preimage U hUopen).mem_nhds (by simpa using hUzero)
  obtain ⟨r₀, hr₀⟩ := (isAdic_iff.mp hn).2 (ψ ⁻¹' U) hpre
  let r := max r₀ 1
  have hrpow : n ^ r ≤ n ^ r₀ := Ideal.pow_le_pow_right (le_max_left r₀ 1)
  have hmapr : Ideal.map φ (n ^ r) ≤ J ⊔ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change φ x ∈ J ⊔ I
    have hx₀ : x ∈ n ^ r₀ := hrpow hx
    obtain ⟨i, hi, hψxi⟩ := hr₀ hx₀
    have hdiff : φ x - i ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (φ x) i).1
      ((DFunLike.congr_fun hφJ x).trans hψxi.symm)
    rw [Submodule.mem_sup]
    exact ⟨φ x - i, hdiff, i, hi, by abel⟩
  have hmaprt : Ideal.map φ (n ^ (r * t)) ≤ I := by
    rw [pow_mul, Ideal.map_pow]
    exact (Ideal.pow_right_mono hmapr t).trans
      (ideal_sup_pow_le_of_pow_le J I t hJI)
  have hφadic : @Continuous S A n.adicTopology I.adicTopology φ :=
    (RingHom.continuous_adic_iff φ n I).2
      ⟨r * t, by
        simpa using Nat.mul_le_mul (le_max_right r₀ 1) ht,
        fun x hx => hmaprt (Ideal.mem_map_of_mem φ hx)⟩
  have hφc : Continuous φ := by
    rw [hn, hI]
    exact hφadic
  have hφf : φ.comp f = g := by
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' I ha
    intro k r'
    have hφkf : ((seq k).1).comp f =
        (Ideal.Quotient.mk (gridIdeal J I t (k + 1))).comp g :=
      ((seq k).2.2.down).2.1
    have hred :
        (Ideal.Quotient.mk (I ^ (k + 1))).comp (φ.comp f) =
          (Ideal.Quotient.mk (I ^ (k + 1))).comp g := by
      rw [← RingHom.comp_assoc, hφI k]
      exact factor_comp_comp_eq_mk_comp f g _ hφkf
    exact congrArg (fun q : R →+* A ⧸ I ^ (k + 1) => q r') hred
  exact ⟨φ, hφc, hφf, hφJ⟩

end RingHom.FormallySmoothTop
