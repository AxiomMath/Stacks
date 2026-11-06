module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppMixedReentry
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.DiscreteValuationRing.Inertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolution
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.IntegralClosure.Pi

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: complete integral closures and the trivial weak solution

Weak unramifiedness and levels, `p`-power residue lemmas, ramification index one, the trivial
weak solution, integral closures over complete discrete valuation rings, and towers.

Part of `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue`;
see there for the overview and references.
-/

@[expose] public section

universe uA uB uC uK uL uM

namespace IsDiscreteValuationRing

namespace ReducedTensorTower

open scoped TensorProduct

end ReducedTensorTower

/-- An extension of discrete valuation rings is weakly unramified iff the maximal ideal extends to
the maximal ideal. -/
private lemma isWeaklyUnramified_iff_map_maximalIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B] :
    IsDiscreteValuationRing.IsWeaklyUnramified A B ↔
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  have h := IsDiscreteValuationRing.ramificationIndex_characterization A B
  refine ⟨fun hw => ?_, fun hm => (h.2.2.1 1 le_rfl (by rwa [pow_one])).symm⟩
  rw [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hw, pow_one] at h
  exact h.2.1

/-- A reduced algebra is isomorphic to its quotient by the nilradical. -/
private lemma bijective_mkₐ_nilradical (K T : Type*) [CommRing K] [CommRing T] [Algebra K T]
    [IsReduced T] : Function.Bijective (Ideal.Quotient.mkₐ K (nilradical T)) :=
  (Ideal.Quotient.mk_bijective_iff_eq_bot _).2 (nilradical_eq_zero T)

/-- A formally unramified extension of discrete valuation rings is weakly unramified. -/
theorem isWeaklyUnramified_of_formallyUnramified
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] : IsDiscreteValuationRing.IsWeaklyUnramified A B :=
  (isWeaklyUnramified_iff_map_maximalIdeal A B).2
    (by simpa only [pow_one] using Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B))

/-- Below a fixed initial level, each positive level drops by a fixed positive amount. -/
lemma levelBound_le_sub (p t x : ℚ) (hxt : x ≤ t) :
    max 0 (max (x - 1) (2 * x - p)) ≤ max 0 (x - min 1 (p - t)) := by
  apply max_le (le_max_left _ _)
  apply max_le
  · exact (sub_le_sub_left (min_le_left _ _) x).trans (le_max_right _ _)
  · have hδ := min_le_right (1 : ℚ) (p - t)
    apply le_trans _ (le_max_right _ _)
    linarith

/-- The level-lowering bound gives induction on all nonnegative levels below `p`. -/
theorem induction_on_level {p : ℚ} {P : ℚ → Prop}
    (hzero : P 0)
    (hstep : ∀ x, 0 < x → x < p →
      (∀ y, 0 ≤ y → y ≤ max 0 (max (x - 1) (2 * x - p)) → P y) → P x)
    {t : ℚ} (ht : 0 ≤ t) (htp : t < p) : P t := by
  let δ := min 1 (p - t)
  have hδ : 0 < δ := lt_min (by norm_num) (sub_pos.mpr htp)
  have haux : ∀ n : ℕ, ∀ x : ℚ, 0 ≤ x → x ≤ t → x ≤ n * δ → P x := by
    intro n
    induction n with
    | zero =>
        intro x hx _ hxδ
        have : x = 0 := by simpa using le_antisymm hxδ (by simpa using hx)
        simpa [this] using hzero
    | succ n ih =>
        intro x hx hxt hxδ
        rcases eq_or_lt_of_le hx with h | h
        · simpa [← h] using hzero
        apply hstep x h (hxt.trans_lt htp)
        intro y hy hybound
        have hyδ : y ≤ max 0 (x - δ) :=
          hybound.trans (levelBound_le_sub p t x hxt)
        rcases le_total (x - δ) 0 with hneg | hpos
        · have : y = 0 := le_antisymm (by simpa [max_eq_left hneg] using hyδ) hy
          simpa [this] using hzero
        have hyx : y ≤ x - δ := by simpa [max_eq_right hpos] using hyδ
        apply ih y hy
        · linarith
        · push_cast at hxδ
          linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (t / δ)
  exact haux n t ht le_rfl ((div_lt_iff₀ hδ).mp hn).le

private lemma isSeparable_of_forall_exists_pow
    (F E : Type*) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] [CharP E p]
    {x : E} (hx : ∀ n : ℕ, ∃ y : E, y ^ (p ^ n) = x) : IsSeparable F x := by
  let S := separableClosure F E
  let : Module.Finite S E := Module.Finite.right F S E
  obtain ⟨y, hy⟩ := hx (IsPurelyInseparable.exponent S E)
  have h := IsPurelyInseparable.exponent_def' S p y
  rw [hy] at h
  obtain ⟨z, hz⟩ := h
  exact hz ▸ z.property

private lemma forall_exists_pow_of_pow_eq
    (E : Type*) [Field E] (p : ℕ) [Fact p.Prime] [CharP E p]
    {x y : E} (hx : ∀ n : ℕ, ∃ z : E, z ^ (p ^ n) = x)
    (n : ℕ) (hy : y ^ (p ^ n) = x) : ∀ m : ℕ, ∃ z : E, z ^ (p ^ m) = y := by
  intro m
  obtain ⟨z, hz⟩ := hx (m + n)
  refine ⟨z, ?_⟩
  apply (iterateFrobenius E p n).injective
  change (z ^ (p ^ m)) ^ (p ^ n) = y ^ (p ^ n)
  rw [← pow_mul, ← pow_add, hz, hy]

private lemma minpoly_coeff_mem_of_forall_exists_pow
    (k F E : Type*) [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra F E] [Module.Finite F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] [CharP E p]
    (hF : ∀ a : F, (∀ n : ℕ, 1 ≤ n → ∃ b : F, b ^ (p ^ n) = a) →
      ∃ c : k, algebraMap k F c = a)
    {x : E} (hx : ∀ n : ℕ, ∃ y : E, y ^ (p ^ n) = x) (i : ℕ) :
    ∃ c : k, algebraMap k F c = (minpoly F x).coeff i := by
  apply hF
  intro n _
  obtain ⟨y, hy⟩ := hx n
  have hsep := isSeparable_of_forall_exists_pow F E p
    (forall_exists_pow_of_pow_eq E p hx n hy)
  have hpoly := minpoly.iterateFrobenius_of_isSeparable p n hsep
  refine ⟨(minpoly F y).coeff i, ?_⟩
  simpa only [iterateFrobenius_def, hy, Polynomial.coeff_map] using
    (congrArg (fun f : Polynomial F => f.coeff i) hpoly).symm

private theorem exists_algebraMap_eq_of_forall_exists_pow
    (k F E : Type*) [Field k] [Field F] [Field E] [IsAlgClosed k]
    [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Module.Finite F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] [CharP E p]
    (hF : ∀ a : F, (∀ n : ℕ, 1 ≤ n → ∃ b : F, b ^ (p ^ n) = a) →
      ∃ c : k, algebraMap k F c = a)
    {x : E} (hx : ∀ n : ℕ, ∃ y : E, y ^ (p ^ n) = x) :
    ∃ c : k, algebraMap k E c = x := by
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (minpoly F x)).mp
    ((Polynomial.lifts_iff_coeff_lifts (minpoly F x)).mpr
      (minpoly_coeff_mem_of_forall_exists_pow k F E p hF hx))
  have hqmonic : q.Monic := Polynomial.monic_map_iff.mp
    (hq.symm ▸ minpoly.monic (Algebra.IsIntegral.isIntegral x))
  have hqx : Polynomial.aeval x q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F x q, hq]
    exact minpoly.aeval F x
  have hxint : IsIntegral k x := ⟨q, hqmonic, hqx⟩
  let S := IntermediateField.adjoin k ({x} : Set E)
  let : FiniteDimensional k S := IntermediateField.adjoin.finiteDimensional hxint
  have hS : S = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic S
  have hxS : x ∈ S := IntermediateField.subset_adjoin k _ (Set.mem_singleton x)
  rwa [hS] at hxS

/-- An algebraically closed Frobenius intersection remains unchanged in a finite extension. -/
private theorem forall_exists_pow_iff_of_finite
    (k F E : Type*) [Field k] [Field F] [Field E] [IsAlgClosed k]
    [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Module.Finite F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] [CharP E p]
    (hF : ∀ a : F, (∃ c : k, algebraMap k F c = a) ↔
      ∀ n : ℕ, 1 ≤ n → ∃ b : F, b ^ (p ^ n) = a)
    (x : E) : (∃ c : k, algebraMap k E c = x) ↔
      ∀ n : ℕ, 1 ≤ n → ∃ y : E, y ^ (p ^ n) = x := by
  constructor
  · rintro ⟨c, rfl⟩ n _
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (Fact.out : p.Prime).pos n)
    exact ⟨algebraMap k E b, by rw [← map_pow, hb]⟩
  · exact fun hx => exists_algebraMap_eq_of_forall_exists_pow k F E p (fun a => (hF a).mpr)
      fun | 0 => ⟨x, by simp⟩ | n + 1 => hx (n + 1) n.succ_pos

open scoped TensorProduct

universe uK₁

lemma ramificationIdx_eq_one_of_map_under_eq
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    (hq : (q.under R).map (algebraMap R S) = q) : q.ramificationIdx R = 1 := by
  let Sq := Localization.AtPrime q
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsScalarTower.algebraMap_eq R S Sq, ← Ideal.map_map, hq,
    Localization.AtPrime.map_eq_maximalIdeal]
  exact IsLocalRing.maximalIdeal.isMaximal Sq

private lemma ramificationIdx_eq_one_of_surjective
    (A B R S : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A R] [Algebra B S] [Algebra R S] [Algebra A S]
    [IsScalarTower A B S] [IsScalarTower A R S]
    (hAB : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hA : Function.Surjective (algebraMap A R))
    (hB : Function.Surjective (algebraMap B S))
    (q : Ideal S) (hq : q.IsMaximal) : q.ramificationIdx R = 1 := by
  have hqB : q.comap (algebraMap B S) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hB)
  have hqA : (q.under R).comap (algebraMap A R) = IsLocalRing.maximalIdeal A := by
    rw [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A R S,
      IsScalarTower.algebraMap_eq A B S, ← Ideal.comap_comap, hqB,
      IsLocalRing.maximalIdeal_comap]
  have hp : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = q.under R := by
    rw [← hqA, Ideal.map_comap_of_surjective _ hA]
  apply ramificationIdx_eq_one_of_map_under_eq
  rw [← hp, Ideal.map_map, ← IsScalarTower.algebraMap_eq A R S,
    IsScalarTower.algebraMap_eq A B S, ← Ideal.map_map, hAB, ← hqB,
    Ideal.map_comap_of_surjective _ hB]

open scoped TensorProduct
attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerABB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

theorem isWeakSolution_self
    (A B K L : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B) : D.IsWeakSolution := by
  let : IsIntegralClosure A A K := (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  let : IsIntegralClosure B B L := (isIntegrallyClosed_iff_isIntegralClosure L).mp inferInstance
  let eA := IsIntegralClosure.equiv A A K D.A₁
  have hA : Function.Surjective (algebraMap A D.A₁) := fun x =>
    (eA.surjective x).imp fun a ha => (eA.commutes a).symm.trans ha
  let T := L ⊗[K] K
  let eT := Algebra.TensorProduct.rid K K L
  let : IsReduced T := isReduced_of_injective eT eT.injective
  let eQ : T ≃ₐ[K] (T ⧸ nilradical T) :=
    AlgEquiv.ofBijective (Ideal.Quotient.mkₐ K _) (bijective_mkₐ_nilradical _ _)
  let eL : L ≃ₐ[K] D.L₁ := (eT.symm.trans eQ).trans D.eL₁.symm
  have heL (x : L) : eL x = algebraMap L D.L₁ x := by
    apply D.eL₁.injective
    simpa only [eL, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, D.eL₁_left,
      Algebra.TensorProduct.includeLeft_apply] using
      (show eQ (eT.symm x) = Ideal.Quotient.mk _ (x ⊗ₜ[K] 1) from rfl)
  let eLB : L ≃ₐ[B] D.L₁ :=
    { eL.toRingEquiv with
      commutes' := fun b => by
        change eL (algebraMap B L b) = algebraMap B D.L₁ b
        rw [heL, ← IsScalarTower.algebraMap_apply B L D.L₁] }
  let : IsIntegralClosure B B D.L₁ :=
    IsIntegralClosure.of_algEquiv B eLB (fun b => by
      change algebraMap B D.L₁ b = eL (algebraMap B L b)
      rw [heL, ← IsScalarTower.algebraMap_apply B L D.L₁])
  let eB := IsIntegralClosure.equiv B B D.L₁ D.B₁
  have hB : Function.Surjective (algebraMap B D.B₁) := fun x =>
    (eB.surjective x).imp fun b hb => (eB.commutes b).symm.trans hb
  exact ramificationIdx_eq_one_of_surjective A B D.A₁ D.B₁
    ((isWeaklyUnramified_iff_map_maximalIdeal A B).1 hweak) hA hB

/-- The integral closure of a complete DVR in a finite fraction extension is a finite DVR.

Carries no residue-field hypothesis. -/
@[sga "6 X 7.16" "special case"]
theorem isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete
    (B L M : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field M] [Algebra B L] [Algebra L M] [Algebra B M]
    [IsScalarTower B L M] [IsFractionRing B L] [Module.Finite L M]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    IsDiscreteValuationRing (integralClosure B M) ∧
      Module.Finite B (integralClosure B M) := by
  let T := L ⊗[L] M
  let eT := Algebra.TensorProduct.lid L M
  let : IsReduced T := isReduced_of_injective eT eT.injective
  let eQ : T ≃ₐ[L] (T ⧸ nilradical T) :=
    AlgEquiv.ofBijective (Ideal.Quotient.mkₐ L _) (bijective_mkₐ_nilradical _ _)
  let e : M ≃ₐ[L] (T ⧸ nilradical T) := eT.symm.trans eQ
  have heleft (x : L) : e (algebraMap L M x) =
      Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeLeft : L →ₐ[L] T) x) := by
    change Ideal.Quotient.mk _ (1 ⊗ₜ[L] algebraMap L M x) =
      Ideal.Quotient.mk _ (x ⊗ₜ[L] 1)
    congr 1
    simpa only [Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one,
      TensorProduct.smul_tmul'] using
      (TensorProduct.tmul_smul (R := L) x (1 : L) (1 : M))
  have heright (x : M) : e x =
      Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeRight : M →ₐ[L] T) x) := rfl
  let : IsDiscreteValuationRing.IsExtension B B := ⟨⟩
  have h := IsDiscreteValuationRing.integralClosures_after_finite_fraction_field_extension
    B B L L M M (integralClosure B M) (integralClosure B M)
    e (AlgEquiv.refl) (AlgEquiv.refl) heleft heright
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcomplete, _, _, _, _, hfinite, _⟩ := h
  exact ⟨(hcomplete inferInstance).choose_spec,
    hfinite IsNagataRing.of_isPrecomplete_maximalIdeal⟩

private theorem isIntegralClosure_of_valuationRing
    (R S K : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsLocalRing S] [IsIntegrallyClosed S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
    [IsFractionRing S K] [IsScalarTower R S K] [IsLocalHom (algebraMap R S)]
    [ValuationRing (integralClosure R K)]
    [IsFractionRing (integralClosure R K) K] : IsIntegralClosure S R K := by
  let T := integralClosure R K
  let : IsLocalRing T := ValuationRing.isLocalRing T
  let : IsIntegralClosure S S K := (isIntegrallyClosed_iff_isIntegralClosure K).mp
    inferInstance
  let j : T →ₐ[R] (integralClosure S K).restrictScalars R :=
    Subalgebra.inclusion (fun _ hx => hx.tower_top)
  let e := IsIntegralClosure.equiv S S K (integralClosure S K)
  let f : T →ₐ[R] S := (e.symm.restrictScalars R).toAlgHom.comp j
  have hf (x : T) : algebraMap S K (f x) = (x : K) :=
    IsIntegralClosure.algebraMap_equiv S (integralClosure S K) K S (j x)
  let : Algebra T S := f.toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : IsScalarTower T S K := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  let q := (IsLocalRing.maximalIdeal S).comap f.toRingHom
  have hqR : q.under R = IsLocalRing.maximalIdeal R := by
    change ((IsLocalRing.maximalIdeal S).comap f.toRingHom).comap
      (algebraMap R T) = _
    rw [Ideal.comap_comap, show f.toRingHom.comp (algebraMap R T) = algebraMap R S from
      RingHom.ext f.commutes, IsLocalRing.maximalIdeal_comap]
  have hqmax : q.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    change (q.under R).IsMaximal
    rw [hqR]
    infer_instance
  have hq : q = IsLocalRing.maximalIdeal T := IsLocalRing.eq_maximalIdeal hqmax
  let : IsLocalHom (algebraMap T S) := ⟨fun x hx => by
    by_contra hnx
    exact (hq.symm ▸ hnx : x ∈ q) hx⟩
  have hsurj : Function.Surjective f :=
    surjective_of_isLocalHom_of_isFractionRing T S K (IsFractionRing.injective S K)
  refine ⟨IsFractionRing.injective S K, fun {x} => ⟨fun hx => ⟨f ⟨x, hx⟩, hf ⟨x, hx⟩⟩, ?_⟩⟩
  rintro ⟨s, rfl⟩
  obtain ⟨t, rfl⟩ := hsurj s
  rw [hf]
  exact t.property

/-- A DVR over a complete DVR is the integral closure in its finite fraction extension.

Together with `isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete` above, this
gives module-finiteness of the top of a complete tower over its middle, which is what makes
completeness of the top derivable rather than an added hypothesis. -/
theorem isIntegralClosure_of_isAdicComplete
    (B C L M : Type*)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M] [Algebra B C] [Algebra B L] [Algebra C M]
    [Algebra L M] [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
    [IsFractionRing B L] [IsFractionRing C M] [IsLocalHom (algebraMap B C)]
    [Module.Finite L M] [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    IsIntegralClosure C B M := by
  let := (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).1
  let := IsIntegralClosure.isFractionRing_of_finite_extension B L M (integralClosure B M)
  exact isIntegralClosure_of_valuationRing B C M

/-- At level zero the cyclotomic extension is weakly unramified. -/
theorem isWeaklyUnramified_of_extensionLevel_eq_zero
    (B C L M : Type*)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M] [Algebra B C] [Algebra B L] [Algebra C M]
    [Algebra L M] [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
    [IsFractionRing B L] [IsFractionRing C M] [IsDiscreteValuationRing.IsExtension B C]
    [IsIntegralClosure C B M] [CharZero L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (π : B) (hπ : Irreducible π) (e₁ : ℕ) (he₁ : 0 < e₁)
    (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π).Nonempty)
    (hlevel : Stacks.DegreePExtensionLevel.extensionLevel B L M P π e₁ he₁ hne = 0) :
    IsDiscreteValuationRing.IsWeaklyUnramified B C := by
  have hn : sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π) = 0 := by
    have heQ : (e₁ : ℚ) ≠ 0 := by exact_mod_cast he₁.ne'
    have h := (div_eq_zero_iff).mp hlevel
    exact_mod_cast h.resolve_right heQ
  have hzmem := Nat.sInf_mem hne
  rw [hn] at hzmem
  rcases hzmem with ⟨ξ, z, hgen, hz, a, ha⟩
  have hξ : ξ = algebraMap B L a := by simpa using ha.symm
  have hz' : Polynomial.aeval z P = algebraMap L M ξ := by
    rwa [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M]
  obtain ⟨_, _, _, hzero, _⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient
      B L M p f P hP ξ z hz' hgen π hπ
  rcases hzero ⟨a, hξ⟩ with htrivial | ⟨_, hunram⟩
  · let e : L ≃ₐ[B] M :=
      (AlgEquiv.ofBijective (Algebra.ofId L M)
        ⟨(algebraMap L M).injective, htrivial⟩).restrictScalars B
    let : IsFractionRing B M := IsFractionRing.of_algEquiv e
    have hsurj := surjective_of_isLocalHom_of_isFractionRing B C M
      (IsFractionRing.injective C M)
    have hmap : (IsLocalRing.maximalIdeal B).map (algebraMap B C) =
        IsLocalRing.maximalIdeal C := by
      rw [← IsLocalRing.eq_maximalIdeal
          (Ideal.comap_isMaximal_of_surjective (f := algebraMap B C)
            (K := IsLocalRing.maximalIdeal C) hsurj),
        Ideal.map_comap_of_surjective _ hsurj]
    exact (isWeaklyUnramified_iff_map_maximalIdeal B C).2 hmap
  let e := IsIntegralClosure.equiv B (integralClosure B M) M C
  let q := (IsLocalRing.maximalIdeal C).comap e.toRingHom
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective
  obtain ⟨_, hqidx, _⟩ := hunram q hq
  have hidx : (IsLocalRing.maximalIdeal B).ramificationIdx'
      (IsLocalRing.maximalIdeal C) = 1 := by
    rwa [← Ideal.ramificationIdx'_comap_eq (IsLocalRing.maximalIdeal B) e]
  exact (Stacks.DiscreteValuationRing.Ramification.ramificationIdx_def B C).trans hidx

/-- A finite extension of DVRs inherits completeness from its base.

Completeness of the top of the tower is derived, not assumed, exactly as Tag 09F8 derives it at
the end of its own proof. -/
theorem isAdicComplete_of_finite
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsDiscreteValuationRing.IsExtension R S] [Module.Finite R S]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  let I := IsLocalRing.maximalIdeal R
  have hsep : IsHausdorff I S := IsHausdorff.of_le_jacobson I S
    (IsLocalRing.maximalIdeal_le_jacobson _)
  have hcomp : IsAdicComplete I S := isAdicComplete_of_iInf_smul_eq_bot I
    hsep.iInf_pow_smul
  have hmap : IsAdicComplete (I.map (algebraMap R S)) S :=
    (IsAdicComplete.map_algebraMap_iff I S).mpr hcomp
  obtain ⟨he, hm, _⟩ := IsDiscreteValuationRing.ramificationIndex_characterization R S
  change IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S at hmap
  rw [hm] at hmap
  apply (completeness_preserved ((IsLocalRing.maximalIdeal S) ^
    IsDiscreteValuationRing.ramificationIndex R S) (IsLocalRing.maximalIdeal S)
    (c := 1) (d := IsDiscreteValuationRing.ramificationIndex R S) (by decide) he
    (by simpa using (Ideal.pow_le_self (I := IsLocalRing.maximalIdeal S)
      (n := IsDiscreteValuationRing.ramificationIndex R S) (by omega))) le_rfl S).mp hmap

/-- The residue-field intersection condition ascends along a finite local extension. -/
theorem residueField_forall_exists_pow_iff_of_finite
    (A B C : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap A C)] [Module.Finite B C]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hB : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (x : IsLocalRing.ResidueField C) :
    (∃ a : IsLocalRing.ResidueField A,
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) a = x) ↔
      ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField C, y ^ (p ^ n) = x := by
  let : CharP (IsLocalRing.ResidueField B) p := CharP.of_ringHom_of_ne_zero
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) p
    (Fact.out : p.Prime).ne_zero
  let : CharP (IsLocalRing.ResidueField C) p := CharP.of_ringHom_of_ne_zero
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)) p
    (Fact.out : p.Prime).ne_zero
  exact forall_exists_pow_iff_of_finite (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField C) p hB x

/-- A weak solution for the top of a tower is a weak solution for its intermediate ring.

This is the go-down half of Tag 09ES packaged at the level of the existential. Carries no
residue-field hypothesis of any kind. -/
theorem exists_isWeakSolution_of_tower
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M]
    (h : ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
          max uM uK, uK, max uM uK} A C K M K₁, D.IsWeakSolution) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁, D.IsWeakSolution := by
  obtain ⟨K₁, _, _, _, _, _, DAC, hDAC⟩ := h
  obtain ⟨DAB⟩ := nonempty_integralClosureBaseChange A B K L K₁
  exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    DAB, (IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose.{uA, uB, uC,
      uK, uL, uM, uK, 0, max uL uK, uK, max uL uK, max uM uK, uK,
      max uM uK, 0, 0, 0}
      A B C K L M K₁ DAB DAC).1.1 hDAC⟩

-- The Stacks proof of Tag 09F8 argues at one point that, `A` being complete with algebraically
-- closed residue field, the base-changed extension is separable and totally ramified.  The
-- induction below does not need total ramification: it propagates the `IsAlgClosed` instance
-- itself along each finite extension, via `isAlgClosed_residueField_of_finite`, an appeal to
-- `IsAlgClosed.ringHom_bijective_of_isIntegral`.  Algebraic closedness is used in
-- `exists_algebraMap_eq_of_forall_exists_pow` (the `⊥`-descent of an infinitely `p`-divisible
-- element) together with the surjectivity half of
-- `residueField_forall_exists_pow_iff_of_finite_square`, at the two induction joints where
-- `hresidue` has to ascend along a finite extension.

end IsDiscreteValuationRing
