module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Category
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.RingTheory.Module.ReduceModIdealExact
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.DelayedIso

/-!
# Ext over adic quotients: the explicit comparison (Tag 0EGZ)

The transition maps of the system of adic quotients of `Ext^i_A(M, N)`, and the explicit
content of the delayed isomorphism of tag 0EGY: kernels and cokernels of the canonical maps
between the two systems are annihilated by fixed powers of `I`.
-/

@[expose] public section

/-! ## Tag 0EGZ -/

section

open CategoryTheory CategoryTheory.Abelian Filter

universe u v

namespace Stacks.AdicSystem.ExtComparison

open Stacks.Modules.AdicSystem Stacks.AdicSystem.ExtDelayedIso
open Stacks.Modules.AdicSystem.AdicModuleSystem

noncomputable section


variable {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
  {M N : Type v}
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- The canonical transition from the quotient of `Ext_A^i(M,N)` modulo `I ^ m` to its
quotient modulo `I ^ n`, when `n ≤ m`. -/
public noncomputable def extAdicQuotientTransition (I : Ideal A) (M N : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (i : ℕ)
    {n m : ℕ+} (h : n ≤ m) :
    AdicModuleSystem.underlying (extAdicQuotientSystem I M N i) m →ₗ[A]
      AdicModuleSystem.underlying (extAdicQuotientSystem I M N i) n :=
  (I ^ (m : ℕ) • (⊤ : Submodule A
      (Ext (ModuleCat.of A M) (ModuleCat.of A N) i))).mapQ
    (I ^ (n : ℕ) • (⊤ : Submodule A
      (Ext (ModuleCat.of A M) (ModuleCat.of A N) i))) LinearMap.id <| by
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

end
end Stacks.AdicSystem.ExtComparison

end

section

open CategoryTheory CategoryTheory.Abelian Filter

universe u v

namespace Stacks.AdicSystem.ExtComparison

open Stacks.Modules.AdicSystem Stacks.AdicSystem.ExtDelayedIso
  Stacks.Modules.AdicSystem.AdicModuleSystem

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A}
  {E F : AdicModuleSystem.{u, v} A I}

private theorem powerPart_self_eq_bot (E : AdicModuleSystem.{u, v} A I) (n : ℕ+) :
    powerPart E n n = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  show x = 0
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha z _
    change (E.module n).obj at z
    show (Ideal.Quotient.mk (I ^ (n : ℕ))) a • z = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]
  · intro x y hx hy
    rw [hx, hy, add_zero]

private theorem powerPart_le_torsionPart (E : AdicModuleSystem.{u, v} A I) (n : ℕ+)
    (a b : ℕ) (h : (n : ℕ) ≤ a + b) :
    powerPart E n a ≤ torsionPart E n b := by
  intro x hx
  show x ∈ Submodule.torsionBySet A (underlying E n) (↑(I ^ b) : Set A)
  rw [Submodule.mem_torsionBySet_iff]
  intro ⟨t, ht⟩
  show t • x = 0
  have hm : t • x ∈ powerPart E n (a + b) := by
    rw [powerPart_add_eq_smul]
    exact Submodule.smul_mem_smul ht hx
  have hz := powerPart_antitone E n h hm
  rwa [powerPart_self_eq_bot] at hz

private def powerMap {n m : ℕ+}
    (f : underlying E m →ₗ[A] underlying E n) (a : ℕ) :
    powerPart E m a →ₗ[A] powerPart E n a :=
  (f.comp (powerPart E m a).subtype).codRestrict _
    (fun x => map_powerPart_mem (I ^ a) f x x.2)

private theorem powerMap_surjective {n m : ℕ+}
    (f : underlying E m →ₗ[A] underlying E n) (hf : Function.Surjective f) (a : ℕ) :
    Function.Surjective (powerMap f a) := by
  intro x
  have hx : x.1 ∈ (powerPart E m a).map f := by
    rw [powerPart, Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    exact x.2
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

private theorem map_mem_torsion {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : X →ₗ[A] Y) (J : Ideal A)
    {x : X} (hx : x ∈ Submodule.torsionBySet A X (↑J : Set A)) :
    f x ∈ Submodule.torsionBySet A Y (↑J : Set A) := by
  rw [Submodule.mem_torsionBySet_iff] at hx ⊢
  intro ⟨a, ha⟩
  show a • f x = 0
  rw [← map_smul, hx ⟨a, ha⟩, map_zero]

private theorem exists_cross_map
    (r : HomRepresentative E F) (s : HomRepresentative F E)
    (n m : ℕ+) (hn : s.delay + r.delay ≤ (n : ℕ)) (hnm : n ≤ m)
    (f : underlying E m →ₗ[A] underlying E n) :
    ∃ g : powerPart F m (s.delay + r.delay) →ₗ[A]
        underlying F n ⧸ torsionPart F n (s.delay + r.delay),
      (∀ (z : powerPart F m (s.delay + r.delay)) (y : powerPart E m r.delay),
        s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
          ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩ =
          (torsionPart E m s.delay).mkQ y.1 →
        g z = quotientTransitionOfLE F n (Nat.le_add_left _ _)
          (r.map n ((Nat.le_add_left _ _).trans hn) (powerMap f r.delay y))) ∧
      (powerPart F m (n : ℕ)).comap (powerPart F m (s.delay + r.delay)).subtype ≤ g.ker := by
  let k := compositeSourceMap E m s.delay r.delay
  let t := (compositeTargetMap r n ((Nat.le_add_left _ _).trans hn) s.delay).comp
    (powerMap f r.delay)
  have hkt : k.ker ≤ t.ker := by
    intro y hy
    have hy' : y.1 ∈ torsionPart E m s.delay :=
      (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hy)
    have hfy : f y.1 ∈ torsionPart E n s.delay := map_mem_torsion f (I ^ s.delay) hy'
    exact composite_kernel_le r n ((Nat.le_add_left _ _).trans hn) s.delay
      ((Submodule.Quotient.mk_eq_zero _).mpr hfy)
  obtain ⟨l, hl⟩ := Stacks.AdicModuleSystem.IsomorphismCriterion.exists_factor_range k t hkt
  let g := l.comp (compositeRangeMap s r m (hn.trans hnm))
  have hg (z : powerPart F m (s.delay + r.delay)) (y : powerPart E m r.delay)
      (hy : s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
        ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩ =
        (torsionPart E m s.delay).mkQ y.1) :
      g z = quotientTransitionOfLE F n (Nat.le_add_left _ _)
        (r.map n ((Nat.le_add_left _ _).trans hn) (powerMap f r.delay y)) := by
    have hz : compositeRangeMap s r m (hn.trans hnm) z =
        ⟨k y, LinearMap.mem_range_self k y⟩ := Subtype.ext hy
    show l (compositeRangeMap s r m (hn.trans hnm) z) = t y
    rw [hz, hl]
  refine ⟨g, hg, ?_⟩
  intro z hz
  have hs : s.delay ≤ (n : ℕ) := (Nat.le_add_right _ _).trans hn
  have hsum : s.delay + ((n : ℕ) - s.delay) = n := Nat.add_sub_of_le hs
  let z' : powerPart F m (s.delay + ((n : ℕ) - s.delay)) :=
    ⟨z, by simpa only [hsum] using (show z.1 ∈ powerPart F m (n : ℕ) from hz)⟩
  obtain ⟨y, hy⟩ := composite_lift s ((n : ℕ) - s.delay) m
    (by simpa only [hsum] using (show (n : ℕ) ≤ (m : ℕ) from hnm)) z'
  have ha : r.delay ≤ (n : ℕ) - s.delay := by omega
  let y' : powerPart E m r.delay := ⟨y, powerPart_antitone E m ha y.2⟩
  have hgy := hg z y' hy
  rw [LinearMap.mem_ker, hgy]
  apply composite_kernel_le r n ((Nat.le_add_left _ _).trans hn) s.delay
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply powerPart_le_torsionPart E n ((n : ℕ) - s.delay) s.delay (by omega)
  exact map_powerPart_mem (I ^ ((n : ℕ) - s.delay)) f y y.2

private theorem smul_mem_map_power_of_cokernel_torsion
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) (J K : Ideal A)
    (hc : Module.IsTorsionBySet A (Y ⧸ f.range) (↑K : Set A))
    (y : Y) (hy : y ∈ J • (⊤ : Submodule A Y)) (a : A) (ha : a ∈ K) :
    a • y ∈ (J • (⊤ : Submodule A X)).map f := by
  rw [Submodule.map_smul'', Submodule.map_top]
  have hc' := (Module.isTorsionBySet_quotient_iff f.range _).mp hc
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro b hb z _
    rw [smul_comm a b]
    exact Submodule.smul_mem_smul hb (hc' z a ha)
  · intro x y hx hy
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

/-- If `b • c • x ∈ P` for all `b ∈ J`, `c ∈ K`, then `a • x ∈ P` for all `a ∈ J * K`. -/
private theorem smul_mem_of_mul_smul_mem {X : Type*} [AddCommGroup X] [Module A X]
    (P : Submodule A X) {J K : Ideal A} {x : X} (h : ∀ b ∈ J, ∀ c ∈ K, b • c • x ∈ P)
    {a : A} (ha : a ∈ J * K) : a • x ∈ P := by
  refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) fun a b ha hb => ?_
  · rw [mul_smul]
    exact h b hb c hc
  · rw [add_smul]
    exact P.add_mem ha hb

private theorem smul_mem_power_of_map_mem
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) (J K : Ideal A)
    (hk : Module.IsTorsionBySet A f.ker (↑K : Set A))
    (hc : Module.IsTorsionBySet A (Y ⧸ f.range) (↑K : Set A))
    (x : X) (hx : f x ∈ J • (⊤ : Submodule A Y)) (a : A) (ha : a ∈ K * K) :
    a • x ∈ J • (⊤ : Submodule A X) := by
  refine smul_mem_of_mul_smul_mem _ (fun b hb c hcK => ?_) ha
  obtain ⟨w, hw, he⟩ := smul_mem_map_power_of_cokernel_torsion f J K hc _ hx c hcK
  have hz : c • x - w ∈ f.ker := by
    rw [LinearMap.mem_ker, map_sub, map_smul, he, sub_self]
  have heq : b • (c • x - w) = 0 := congrArg Subtype.val (@hk ⟨c • x - w, hz⟩ ⟨b, hb⟩)
  rw [smul_sub, sub_eq_zero] at heq
  rw [heq]
  exact Submodule.smul_mem _ b hw

private theorem smul_eq_zero_of_kernel_torsion
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) (J : Ideal A)
    (hk : Module.IsTorsionBySet A f.ker (↑J : Set A))
    (x : X) (hx : f x = 0) (a : A) (ha : a ∈ J) : a • x = 0 :=
  congrArg Subtype.val (@hk ⟨x, LinearMap.mem_ker.mpr hx⟩ ⟨a, ha⟩)

private theorem smul_mem_of_cross_eq_zero
    (r : HomRepresentative E F) (s : HomRepresentative F E)
    (n m : ℕ+) (hn : s.delay + r.delay ≤ (n : ℕ)) (hnm : n ≤ m)
    (f : underlying E m →ₗ[A] underlying E n)
    (hf : f.ker ≤ powerPart E m (n : ℕ)) (k : ℕ)
    (hrk : Module.IsTorsionBySet A (r.map n ((Nat.le_add_left _ _).trans hn)).ker
      (↑(I ^ k) : Set A))
    (hsk : Module.IsTorsionBySet A (s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))).ker
      (↑(I ^ k) : Set A))
    (hsc : Module.IsTorsionBySet A
      ((underlying E m ⧸ torsionPart E m s.delay) ⧸
        (s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))).range) (↑(I ^ k) : Set A))
    (z : powerPart F m (s.delay + r.delay)) (y : powerPart E m r.delay)
    (hy : s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
      ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩ =
      (torsionPart E m s.delay).mkQ y.1)
    (hz : quotientTransitionOfLE F n (Nat.le_add_left r.delay s.delay)
      (r.map n ((Nat.le_add_left _ _).trans hn) (powerMap f r.delay y)) = 0)
    (a : A) (ha : a ∈ I ^ ((k + k) + (k + (s.delay + r.delay)))) :
    a • z.1 ∈ powerPart F m (n : ℕ) := by
  let R := r.map n ((Nat.le_add_left _ _).trans hn)
  let S := s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
  let x : powerPart F m s.delay := ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩
  have hzero (t : A) (ht : t ∈ I ^ (k + (s.delay + r.delay))) : t • f y.1 = 0 := by
    rw [pow_add] at ht
    refine smul_mem_of_mul_smul_mem ⊥ (fun b hb c hc => ?_) ht
    have hR : R (c • powerMap f r.delay y) = 0 := by
      rw [map_smul]
      have he :=
        Stacks.AdicModuleSystem.IsomorphismCriterion.smul_eq_of_quotientTransition_eq F n
          (Nat.le_add_left r.delay s.delay) (R (powerMap f r.delay y)) 0 (by simpa using hz) c hc
      simpa using he
    have he := smul_eq_zero_of_kernel_torsion R (I ^ k) hrk _ hR b hb
    exact (Submodule.mem_bot A).2 (congrArg Subtype.val he)
  rw [pow_add] at ha
  refine smul_mem_of_mul_smul_mem _ (fun b hb c hc => ?_) ha
  have hym : c • y.1 ∈ powerPart E m (n : ℕ) := by
    apply hf
    rw [LinearMap.mem_ker, map_smul]
    exact hzero c hc
  have hS : S (c • x) ∈ I ^ (n : ℕ) •
      (⊤ : Submodule A (underlying E m ⧸ torsionPart E m s.delay)) := by
    rw [map_smul, show S x = _ from hy, ← map_smul]
    exact map_powerPart_mem (I ^ (n : ℕ)) (torsionPart E m s.delay).mkQ _ hym
  have hb' : b ∈ I ^ k * I ^ k := by simpa only [pow_add] using hb
  have he := smul_mem_power_of_map_mem S (I ^ (n : ℕ)) (I ^ k) hsk hsc (c • x) hS b hb'
  exact map_powerPart_mem (I ^ (n : ℕ)) (powerPart F m s.delay).subtype _ he

private theorem smul_mem_range_cross
    (r : HomRepresentative E F) (s : HomRepresentative F E)
    (n m : ℕ+) (hn : s.delay + r.delay ≤ (n : ℕ)) (hnm : n ≤ m)
    (f : underlying E m →ₗ[A] underlying E n) (hf : Function.Surjective f) (k : ℕ)
    (hrc : Module.IsTorsionBySet A
      ((underlying F n ⧸ torsionPart F n r.delay) ⧸
        (r.map n ((Nat.le_add_left _ _).trans hn)).range) (↑(I ^ k) : Set A))
    (hsc : Module.IsTorsionBySet A
      ((underlying E m ⧸ torsionPart E m s.delay) ⧸
        (s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))).range) (↑(I ^ k) : Set A))
    (g : powerPart F m (s.delay + r.delay) →ₗ[A]
      underlying F n ⧸ torsionPart F n (s.delay + r.delay))
    (hg : ∀ (z : powerPart F m (s.delay + r.delay)) (y : powerPart E m r.delay),
      s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
        ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩ =
        (torsionPart E m s.delay).mkQ y.1 →
      g z = quotientTransitionOfLE F n (Nat.le_add_left _ _)
        (r.map n ((Nat.le_add_left _ _).trans hn) (powerMap f r.delay y)))
    (z : underlying F n ⧸ torsionPart F n (s.delay + r.delay))
    (a : A) (ha : a ∈ I ^ ((r.delay + k) + k)) : a • z ∈ g.range := by
  let R := r.map n ((Nat.le_add_left _ _).trans hn)
  let S := s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
  have hR := (Module.isTorsionBySet_quotient_iff R.range _).mp hrc
  have hS := (Module.isTorsionBySet_quotient_iff S.range _).mp hsc
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    rw [pow_add] at ha
    refine smul_mem_of_mul_smul_mem g.range (fun b hb c hc => ?_) ha
    obtain ⟨y, hy⟩ := hR ((torsionPart F n r.delay).mkQ z) c hc
    obtain ⟨y', hy'⟩ := powerMap_surjective f hf r.delay y
    rw [pow_add] at hb
    refine smul_mem_of_mul_smul_mem g.range (fun d hd e he => ?_) hb
    obtain ⟨x, hx⟩ := hS ((torsionPart E m s.delay).mkQ y'.1) e he
    let x' : powerPart F m (s.delay + r.delay) :=
      ⟨d • x.1, by rw [powerPart_add_eq_smul]; exact Submodule.smul_mem_smul hd x.2⟩
    have hxy : S ⟨x', powerPart_add_le_left F m s.delay r.delay x'.2⟩ =
        (torsionPart E m s.delay).mkQ (d • e • y').1 := by
      show S (d • x) = _
      rw [map_smul, hx]
      simp only [Submodule.coe_smul_of_tower, map_smul]
    have heq := hg x' (d • e • y') hxy
    refine ⟨x', ?_⟩
    rw [heq]
    simp only [map_smul, hy']
    rw [show r.map n ((Nat.le_add_left _ _).trans hn) y = _ from hy]
    simp only [map_smul, quotientTransitionOfLE_mkQ]
    rfl

private theorem exists_cross_quotient
    (r : HomRepresentative E F) (s : HomRepresentative F E)
    (n m : ℕ+) (hn : s.delay + r.delay ≤ (n : ℕ)) (hnm : n ≤ m)
    (f : underlying E m →ₗ[A] underlying E n) :
    ∃ g : (powerPart F m (s.delay + r.delay) ⧸
        (powerPart F m (n : ℕ)).comap (powerPart F m (s.delay + r.delay)).subtype) →ₗ[A]
        underlying F n ⧸ torsionPart F n (s.delay + r.delay),
      ∀ (z : powerPart F m (s.delay + r.delay)) (y : powerPart E m r.delay),
        s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
          ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩ =
          (torsionPart E m s.delay).mkQ y.1 →
        g (Quotient.mk _ z) = quotientTransitionOfLE F n (Nat.le_add_left _ _)
          (r.map n ((Nat.le_add_left _ _).trans hn) (powerMap f r.delay y)) := by
  obtain ⟨g, hg, hk⟩ := exists_cross_map r s n m hn hnm f
  exact ⟨((powerPart F m (n : ℕ)).comap
    (powerPart F m (s.delay + r.delay)).subtype).liftQ g hk, hg⟩

private theorem cross_quotient_torsion
    (r : HomRepresentative E F) (s : HomRepresentative F E)
    (n m : ℕ+) (hn : s.delay + r.delay ≤ (n : ℕ)) (hnm : n ≤ m)
    (f : underlying E m →ₗ[A] underlying E n)
    (hf : Function.Surjective f) (hfk : f.ker ≤ powerPart E m (n : ℕ)) (k : ℕ)
    (hrk : Module.IsTorsionBySet A (r.map n ((Nat.le_add_left _ _).trans hn)).ker
      (↑(I ^ k) : Set A))
    (hrc : Module.IsTorsionBySet A
      ((underlying F n ⧸ torsionPart F n r.delay) ⧸
        (r.map n ((Nat.le_add_left _ _).trans hn)).range) (↑(I ^ k) : Set A))
    (hsk : Module.IsTorsionBySet A (s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))).ker
      (↑(I ^ k) : Set A))
    (hsc : Module.IsTorsionBySet A
      ((underlying E m ⧸ torsionPart E m s.delay) ⧸
        (s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))).range) (↑(I ^ k) : Set A))
    (g : (powerPart F m (s.delay + r.delay) ⧸
        (powerPart F m (n : ℕ)).comap (powerPart F m (s.delay + r.delay)).subtype) →ₗ[A]
        underlying F n ⧸ torsionPart F n (s.delay + r.delay))
    (hg : ∀ (z : powerPart F m (s.delay + r.delay)) (y : powerPart E m r.delay),
      s.map m ((Nat.le_add_right _ _).trans (hn.trans hnm))
        ⟨z, powerPart_add_le_left F m s.delay r.delay z.2⟩ =
        (torsionPart E m s.delay).mkQ y.1 →
      g (Quotient.mk _ z) = quotientTransitionOfLE F n (Nat.le_add_left _ _)
        (r.map n ((Nat.le_add_left _ _).trans hn) (powerMap f r.delay y))) :
    Module.IsTorsionBySet A g.ker (↑(I ^ (6 * k + 2 * (s.delay + r.delay))) : Set A) ∧
    Module.IsTorsionBySet A
      ((underlying F n ⧸ torsionPart F n (s.delay + r.delay)) ⧸ g.range)
      (↑(I ^ (6 * k + 2 * (s.delay + r.delay))) : Set A) := by
  let T := (powerPart F m (n : ℕ)).comap (powerPart F m (s.delay + r.delay)).subtype
  have hk : Module.IsTorsionBySet A g.ker
      (↑(I ^ ((k + k) + (k + (s.delay + r.delay)))) : Set A) := by
    intro x ⟨a, ha⟩
    apply Subtype.ext
    show a • x.1 = 0
    obtain ⟨z, hz⟩ := T.mkQ_surjective x.1
    have hx := LinearMap.mem_ker.mp x.2
    rw [← hz] at hx ⊢
    obtain ⟨y, hy⟩ := composite_lift s r.delay m (hn.trans hnm) z
    change g (Quotient.mk _ z) = 0 at hx
    rw [hg z y hy] at hx
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact smul_mem_of_cross_eq_zero r s n m hn hnm f hfk k hrk hsk hsc z y hy hx a ha
  have hc : Module.IsTorsionBySet A
      ((underlying F n ⧸ torsionPart F n (s.delay + r.delay)) ⧸ g.range)
      (↑(I ^ ((r.delay + k) + k)) : Set A) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro z a ha
    obtain ⟨x, hx⟩ := smul_mem_range_cross r s n m hn hnm f hf k hrc hsc
      (g.comp T.mkQ) hg z a ha
    exact ⟨T.mkQ x, hx⟩
  constructor
  · exact Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right (by omega)) hk
  · exact Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right (by omega)) hc

private theorem exists_eventual_component_bounds
    (r : HomRepresentative E F) (s : HomRepresentative F E)
    (hrs : homOfRepresentative (representativeComp r s) =
      homOfRepresentative (identityRepresentative E))
    (hsr : homOfRepresentative (representativeComp s r) =
      homOfRepresentative (identityRepresentative F)) :
    ∃ k : ℕ, ∀ᶠ n : ℕ+ in atTop, ∀ hn : r.delay ≤ (n : ℕ),
      Module.IsTorsionBySet A (r.map n hn).ker (↑(I ^ k) : Set A) ∧
      Module.IsTorsionBySet A
        ((underlying F n ⧸ torsionPart F n r.delay) ⧸ (r.map n hn).range)
        (↑(I ^ k) : Set A) := by
  obtain ⟨d, hd⟩ :=
    Stacks.AdicModuleSystem.IsomorphismCriterion.kernel_torsion_of_composite_eq_identity r s hrs
  obtain ⟨e, he⟩ :=
    Stacks.AdicModuleSystem.IsomorphismCriterion.cokernel_torsion_of_composite_eq_identity r s hsr
  refine ⟨(d + d) + (e + e), ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨⟨d + e + 1, by omega⟩, ?_⟩
  intro n hn hr
  have hn' : d + e + 1 ≤ (n : ℕ) := hn
  constructor
  · exact Module.isTorsionBySet_of_subset
      (Ideal.pow_le_pow_right (by omega : d + d ≤ (d + d) + (e + e)))
      (hd n (by omega) hr)
  · exact Module.isTorsionBySet_of_subset
      (Ideal.pow_le_pow_right (by omega : e + e ≤ (d + d) + (e + e)))
      (he n (by omega) hr)

variable [IsNoetherianRing A] [Small.{v} A]
  (M N : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

private theorem extAdicQuotientTransition_surjective (i : ℕ) {n m : ℕ+} (h : n ≤ m) :
    Function.Surjective (extAdicQuotientTransition I M N i h) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => exact ⟨Quotient.mk _ x, rfl⟩

private theorem ker_extAdicQuotientTransition_le (i : ℕ) {n m : ℕ+} (h : n ≤ m) :
    (extAdicQuotientTransition I M N i h).ker ≤
      powerPart (extAdicQuotientSystem I M N i) m (n : ℕ) := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hx' : x ∈ I ^ (n : ℕ) •
        (⊤ : Submodule A (Ext (ModuleCat.of A M) (ModuleCat.of A N) i)) :=
      (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx)
    exact map_powerPart_mem (I ^ (n : ℕ))
      (I ^ (m : ℕ) • (⊤ : Submodule A
        (Ext (ModuleCat.of A M) (ModuleCat.of A N) i))).mkQ x hx'

/-- **Stacks 0EGZ.** There are powers `I ^ c` and `I ^ d` such that, for `m ≫ n ≫ 0`, canonical
maps from `I ^ c Ext_{A_m}^i(M_m,N_m) / I ^ n Ext_{A_m}^i(M_m,N_m)` to
`Ext_{A_n}^i(M_n,N_n) / Ext_{A_n}^i(M_n,N_n)[I ^ c]` have kernel and cokernel annihilated
by `I ^ d`. The displayed factorization characterizes these maps in terms of mutually
inverse representatives of the isomorphism of Tag 0EGY.

The source's single exponent is split: maps are defined on I^c-multiples, and their
kernel/cokernel are annihilated by some possibly larger power I^d; with one exponent the
claim fails, e.g. for A = k[x,y,z,w]/(xy), I = (x,y,z,w), M = N = A/(x), i = 2. -/
@[stacks 0EGZ]
public theorem exists_eventually_extOfAdicQuotients_comparison (I : Ideal A) (M N : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (i : ℕ) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    let E := extAdicQuotientSystem I M N i
    let F := extOfAdicQuotientsSystem I M N i
    ∃ (e : E ≅ F) (r : AdicModuleSystem.HomRepresentative E F)
        (s : AdicModuleSystem.HomRepresentative F E),
      AdicModuleSystem.homOfRepresentative r = e.hom ∧
      AdicModuleSystem.homOfRepresentative s = e.inv ∧
      let c := s.delay + r.delay
      ∃ d : ℕ,
      ∃ comparison : ∀ (n m : ℕ+) (_ : c ≤ (n : ℕ)) (_ : n ≤ m),
          (AdicModuleSystem.powerPart F m c ⧸
              (AdicModuleSystem.powerPart F m (n : ℕ)).comap
                (AdicModuleSystem.powerPart F m c).subtype) →ₗ[A]
            AdicModuleSystem.underlying F n ⧸ AdicModuleSystem.torsionPart F n c,
        ∀ᶠ n : ℕ+ in atTop, ∀ᶠ m : ℕ+ in atTop,
          ∀ (hn : c ≤ (n : ℕ)) (hnm : n ≤ m),
            (∀ z : AdicModuleSystem.powerPart F m c,
              ∃ (yₘ : AdicModuleSystem.powerPart E m r.delay)
                (yₙ : AdicModuleSystem.powerPart E n r.delay),
                s.map m (le_trans (Nat.le_add_right s.delay r.delay)
                    (le_trans hn (mod_cast hnm)))
                    ⟨z, AdicModuleSystem.powerPart_add_le_left F m s.delay r.delay z.2⟩ =
                  (AdicModuleSystem.torsionPart E m s.delay).mkQ yₘ.1 ∧
                extAdicQuotientTransition I M N i hnm yₘ = yₙ ∧
                comparison n m hn hnm
                    (Quotient.mk _ z) =
                  AdicModuleSystem.quotientTransitionOfLE F n
                    (Nat.le_add_left r.delay s.delay)
                    (r.map n (le_trans (Nat.le_add_left r.delay s.delay) hn) yₙ)) ∧
            Module.IsTorsionBySet A (comparison n m hn hnm).ker
              (↑(I ^ d) : Set A) ∧
            Module.IsTorsionBySet A
              ((AdicModuleSystem.underlying F n ⧸ AdicModuleSystem.torsionPart F n c) ⧸
                LinearMap.range (comparison n m hn hnm)) (↑(I ^ d) : Set A) := by
  let := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
  let E := extAdicQuotientSystem I M N i
  let F := extOfAdicQuotientsSystem I M N i
  obtain ⟨e⟩ := extAdicQuotientSystem_iso_extOfAdicQuotientsSystem I M N i
  obtain ⟨r, hr⟩ := Quot.exists_rep e.hom
  obtain ⟨s, hs⟩ := Quot.exists_rep e.inv
  change homOfRepresentative r = e.hom at hr
  change homOfRepresentative s = e.inv at hs
  have hrs : homOfRepresentative (representativeComp r s) =
      homOfRepresentative (identityRepresentative E) := by
    show (homOfRepresentative r : E ⟶ F) ≫ homOfRepresentative s = 𝟙 E
    rw [hr, hs, e.hom_inv_id]
  have hsr : homOfRepresentative (representativeComp s r) =
      homOfRepresentative (identityRepresentative F) := by
    show (homOfRepresentative s : F ⟶ E) ≫ homOfRepresentative r = 𝟙 F
    rw [hs, hr, e.inv_hom_id]
  obtain ⟨k, hk⟩ := exists_eventual_component_bounds r s hrs hsr
  obtain ⟨l, hl⟩ := exists_eventual_component_bounds s r hsr hrs
  have hg (n m : ℕ+) (hn : s.delay + r.delay ≤ (n : ℕ)) (hnm : n ≤ m) :=
    exists_cross_quotient r s n m hn hnm (extAdicQuotientTransition I M N i hnm)
  choose g hg using hg
  refine ⟨e, r, s, hr, hs, 6 * (k + l) + 2 * (s.delay + r.delay), g, ?_⟩
  filter_upwards [hk] with n hkn
  filter_upwards [hl] with m hlm
  intro hn hnm
  constructor
  · intro z
    obtain ⟨y, hy⟩ := composite_lift s r.delay m (hn.trans hnm) z
    exact ⟨y, powerMap (extAdicQuotientTransition I M N i hnm) r.delay y,
      hy, rfl, hg n m hn hnm z y hy⟩
  · obtain ⟨hrk, hrc⟩ := hkn ((Nat.le_add_left _ _).trans hn)
    obtain ⟨hsk, hsc⟩ := hlm ((Nat.le_add_right _ _).trans (hn.trans hnm))
    apply cross_quotient_torsion r s n m hn hnm (extAdicQuotientTransition I M N i hnm)
      (extAdicQuotientTransition_surjective M N i hnm)
      (ker_extAdicQuotientTransition_le M N i hnm) (k + l)
      (Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right (Nat.le_add_right k l)) hrk)
      (Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right (Nat.le_add_right k l)) hrc)
      (Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right (Nat.le_add_left l k)) hsk)
      (Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right (Nat.le_add_left l k)) hsc)
      (g n m hn hnm) (hg n m hn hnm)

end
end Stacks.AdicSystem.ExtComparison

end

end
