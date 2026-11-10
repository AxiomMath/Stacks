module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Order.RelSeries
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtrations of modules acted on by finite p-groups

A module annihilated by a power of a prime and carrying an action of a finite group of
prime-power order admits a finite filtration on whose successive quotients the group acts
trivially. In particular, this applies to the finite modules over Noetherian rings in the
source, and is the input to the trace method.

## Main results

* `Module.exists_relSeries_trivial_action_subquotient` gives the filtration by group-ring
  submodules.

## Implementation notes

The action is represented by a module over the group ring `MonoidAlgebra Λ H`. A step from `N₁`
to `N₂` has trivial action on its quotient precisely when `N₁ ≤ N₂` and `([g] - 1) x ∈ N₁` for
every `g : H` and `x ∈ N₂`. A `RelSeries` packages both the finite filtration and this condition
on every successive quotient.

The filtration is produced from nilpotence of the augmentation ideal of the group ring: a simple
module over that ring has trivial action, so the augmentation ideal lies in the Jacobson radical,
and since the ring is a quotient of an Artinian one the ideal is nilpotent. The powers of the
augmentation ideal acting on the module then give the required series.

The statement is placed in the `Module` namespace: nothing geometric enters it.

## References

* [Stacks Project, Tag 0GIZ](https://stacks.math.columbia.edu/tag/0GIZ)
-/

@[expose] public section


private noncomputable def pGroupModuleActionHom {R H V : Type*}
    [Semiring R] [Group H] [AddCommMonoid V] [Module (MonoidAlgebra R H) V] :
    H →* Function.End V where
  toFun g := fun v => MonoidAlgebra.of R H g • v
  map_one' := by
    funext v
    rw [show MonoidAlgebra.of R H (1 : H) = 1 from map_one _]
    exact one_smul _ _
  map_mul' g h := by
    funext v
    change (MonoidAlgebra.of R H (g * h)) • v =
      MonoidAlgebra.of R H g • (MonoidAlgebra.of R H h • v)
    rw [← smul_assoc]
    congr 1
    exact map_mul (MonoidAlgebra.of R H) g h

@[instance_reducible]
private noncomputable def pGroupModuleAction {R H V : Type*}
    [Semiring R] [Group H] [AddCommMonoid V] [Module (MonoidAlgebra R H) V] :
    MulAction H V := MulAction.ofEndHom (pGroupModuleActionHom (R := R) (H := H) (V := V))

private theorem p_dvd_card_of_nontrivial {p n : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod (p ^ n)) V] [Finite V]
    (hV : Nontrivial V) : p ∣ Nat.card V := by
  let : Nontrivial V := hV
  have hexp : Monoid.exponent (Multiplicative V) ∣ p ^ n := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    change Multiplicative.ofAdd ((p ^ n) • (Multiplicative.toAdd x)) = 1
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)) (p ^ n) (Multiplicative.toAdd x),
      ZMod.natCast_self, zero_smul]
    rfl
  have hp : IsPGroup p (Multiplicative V) := IsPGroup.of_exponent_dvd_pow hexp
  rcases hp.card_eq_or_dvd with h | h
  · have hc : 1 < Nat.card (Multiplicative V) := Finite.one_lt_card
    rw [h] at hc
    omega
  · rw [← Nat.card_congr (Multiplicative.toAdd : Multiplicative V ≃ V)]
    exact h

private theorem simple_module_pgroup_action_trivial {p n : ℕ} [Fact p.Prime]
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V]
    [Module (MonoidAlgebra (ZMod (p ^ n)) H) V] [Module (ZMod (p ^ n)) V]
    [IsScalarTower (ZMod (p ^ n)) (MonoidAlgebra (ZMod (p ^ n)) H) V]
    [SMulCommClass (ZMod (p ^ n)) (MonoidAlgebra (ZMod (p ^ n)) H) V] [Finite V]
    (hH : IsPGroup p H) [IsSimpleModule (MonoidAlgebra (ZMod (p ^ n)) H) V]
    (g : H) (v : V) : MonoidAlgebra.of (ZMod (p ^ n)) H g • v = v := by
  classical
  let := pGroupModuleAction (R := ZMod (p ^ n)) (H := H) (V := V)
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod (p ^ n)) H) V
  have hdvd : p ∣ Nat.card V := p_dvd_card_of_nontrivial (p := p) (n := n) inferInstance
  obtain ⟨w, hw, hw0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    V hdvd (a := (0 : V)) (by
      intro g
      change MonoidAlgebra.of (ZMod (p ^ n)) H g • (0 : V) = 0
      simp)
  have hwne : w ≠ 0 := by simpa using hw0.symm
  have hwfix : ∀ g : H, g • w = w := by
    simpa only [MulAction.mem_fixedPoints] using hw
  have hspan : ∀ a : MonoidAlgebra (ZMod (p ^ n)) H,
      a • w ∈ Submodule.span (ZMod (p ^ n)) ({w} : Set V) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
        change g • w ∈ _
        rw [hwfix g]
        exact Submodule.subset_span (by simp)
    | add a b ha hb =>
        rw [add_smul]
        exact (Submodule.span (ZMod (p ^ n)) ({w} : Set V)).add_mem ha hb
    | smul c a ha =>
        rw [IsScalarTower.smul_assoc]
        exact (Submodule.span (ZMod (p ^ n)) ({w} : Set V)).smul_mem c ha
  obtain ⟨a, rfl⟩ := (isSimpleModule_iff_toSpanSingleton_surjective.mp
    (show IsSimpleModule (MonoidAlgebra (ZMod (p ^ n)) H) V from inferInstance)).2 w hwne v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan a)
  change MonoidAlgebra.of (ZMod (p ^ n)) H g • (a • w) = a • w
  rw [← hc]
  change MonoidAlgebra.of (ZMod (p ^ n)) H g • (c • w) = c • w
  rw [smul_comm]
  change c • (g • w) = c • w
  rw [hwfix]

private noncomputable def pGroupAlgebraAugmentationIdeal {R H : Type*} [CommRing R] [Group H] :
    Ideal (MonoidAlgebra R H) :=
  Ideal.span (Set.range fun g : H => MonoidAlgebra.of R H g - 1)

private noncomputable def groupAlgebraAugmentationMap {R H : Type*}
    [CommSemiring R] [Monoid H] : MonoidAlgebra R H →ₐ[R] R :=
  MonoidAlgebra.lift R R H 1

private theorem sub_algebraMap_augmentation_mem {R H : Type*} [CommRing R] [Group H]
    (P : Submodule R (MonoidAlgebra R H)) (hP : ∀ g : H, MonoidAlgebra.of R H g - 1 ∈ P)
    (a : MonoidAlgebra R H) :
    a - algebraMap R (MonoidAlgebra R H) (groupAlgebraAugmentationMap (R := R) (H := H) a) ∈
      P := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have hεg : groupAlgebraAugmentationMap (R := R) (H := H) (MonoidAlgebra.of R H g) = 1 := by
      simp [groupAlgebraAugmentationMap]
    rw [hεg]
    simpa [MonoidAlgebra.one_def] using hP g
  | add a b ha hb =>
    rw [map_add, map_add, add_sub_add_comm]
    exact P.add_mem ha hb
  | smul c a ha =>
    have heq : c • a - algebraMap R (MonoidAlgebra R H)
        (groupAlgebraAugmentationMap (R := R) (H := H) (c • a)) =
        c • (a - algebraMap R (MonoidAlgebra R H)
          (groupAlgebraAugmentationMap (R := R) (H := H) a)) := by
      rw [AlgHom.map_smul_of_tower]
      simp only [Algebra.smul_def, map_mul, mul_sub, Algebra.algebraMap_self]
      rw [RingHom.id_apply]
    rw [heq]
    exact P.smul_mem c ha

private theorem groupAlgebraAugmentationIdeal_eq_ker {R H : Type*}
    [CommRing R] [Group H] :
    pGroupAlgebraAugmentationIdeal (R := R) (H := H) =
      RingHom.ker (groupAlgebraAugmentationMap (R := R) (H := H)).toRingHom := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro _ ⟨g, rfl⟩
    change groupAlgebraAugmentationMap (R := R) (H := H)
      (MonoidAlgebra.of R H g - 1) = 0
    simp [groupAlgebraAugmentationMap]
  · intro a ha
    have hε : groupAlgebraAugmentationMap (R := R) (H := H) a = 0 := RingHom.mem_ker.mp ha
    simpa [hε] using sub_algebraMap_augmentation_mem
      ((pGroupAlgebraAugmentationIdeal (R := R) (H := H)).restrictScalars R)
      (fun g => show _ ∈ pGroupAlgebraAugmentationIdeal (R := R) (H := H) from
        Ideal.subset_span ⟨g, rfl⟩) a

private noncomputable def groupAlgebraAugmentationSubmodule {R H : Type*}
    [CommRing R] [Group H] : Submodule R (MonoidAlgebra R H) :=
  Submodule.span R (Set.range fun g : H => MonoidAlgebra.of R H g - 1)

private theorem groupAlgebraAugmentationSubmodule_eq_ker {R H : Type*}
    [CommRing R] [Group H] :
    groupAlgebraAugmentationSubmodule (R := R) (H := H) =
      (RingHom.ker
        (groupAlgebraAugmentationMap (R := R) (H := H)).toRingHom).restrictScalars R := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨g, rfl⟩
    change groupAlgebraAugmentationMap (R := R) (H := H)
      (MonoidAlgebra.of R H g - 1) = 0
    simp [groupAlgebraAugmentationMap]
  · intro a ha
    have hε : groupAlgebraAugmentationMap (R := R) (H := H) a = 0 := RingHom.mem_ker.mp ha
    simpa [hε] using sub_algebraMap_augmentation_mem
      (groupAlgebraAugmentationSubmodule (R := R) (H := H))
      (fun g => Submodule.subset_span ⟨g, rfl⟩) a

private theorem pGroupAlgebra_augmentation_le_jacobson {p n : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] (hH : IsPGroup p H) :
    pGroupAlgebraAugmentationIdeal (R := ZMod (p ^ n)) (H := H) ≤
      Ring.jacobson (MonoidAlgebra (ZMod (p ^ n)) H) := by
  classical
  let A := MonoidAlgebra (ZMod (p ^ n)) H
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (ZMod (p ^ n)) := Fintype.ofFinite (ZMod (p ^ n))
  let : Finite A := Finite.of_injective MonoidAlgebra.coeff
    MonoidAlgebra.coeff_injective
  apply Ideal.span_le.2
  rintro _ ⟨g, rfl⟩
  change MonoidAlgebra.of (ZMod (p ^ n)) H g - 1 ∈ Module.jacobson A A
  rw [Module.jacobson, Submodule.mem_sInf]
  intro S hS
  let V := A ⧸ S
  let : IsSimpleModule A V := (isSimpleModule_iff_isCoatom).2 hS
  let : Finite V := Finite.of_surjective (S.mkQ) S.mkQ_surjective
  have hquot : Submodule.Quotient.mk (p := S) (MonoidAlgebra.of (ZMod (p ^ n)) H g) =
      Submodule.Quotient.mk (p := S) (1 : A) := by
    calc
      _ = Submodule.Quotient.mk (p := S)
          ((MonoidAlgebra.of (ZMod (p ^ n)) H g) • (1 : A)) := by simp
      _ = MonoidAlgebra.of (ZMod (p ^ n)) H g • Submodule.Quotient.mk (p := S) (1 : A) :=
        Submodule.Quotient.mk_smul S _ _
      _ = _ := simple_module_pgroup_action_trivial (p := p) (n := n) hH g _
  apply (Submodule.Quotient.mk_eq_zero (p := S)).mp
  change S.mkQ (MonoidAlgebra.of (ZMod (p ^ n)) H g - 1) = 0
  simpa only [map_sub, Submodule.mkQ_apply, sub_eq_zero] using hquot

private theorem pGroupAlgebra_augmentation_nilpotent {p n : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] (hH : IsPGroup p H) :
    ∃ N : ℕ, (pGroupAlgebraAugmentationIdeal (R := ZMod (p ^ n)) (H := H)) ^ N = ⊥ := by
  classical
  let A := MonoidAlgebra (ZMod (p ^ n)) H
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (ZMod (p ^ n)) := Fintype.ofFinite (ZMod (p ^ n))
  let : Finite A := Finite.of_injective MonoidAlgebra.coeff
    MonoidAlgebra.coeff_injective
  let : Fintype A := Fintype.ofFinite A
  let : IsArtinianRing A := isArtinian_of_finite (R := A) (M := A)
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := A)
  refine ⟨N, le_antisymm ?_ bot_le⟩
  calc
    (pGroupAlgebraAugmentationIdeal (R := ZMod (p ^ n)) (H := H)) ^ N ≤
        (Ring.jacobson A) ^ N := Ideal.pow_right_mono
          (pGroupAlgebra_augmentation_le_jacobson (p := p) (n := n) hH) N
    _ = ⊥ := by simp [hN]

private instance isTwoSided_pGroupAlgebraAugmentationIdeal {R H : Type*} [CommRing R]
    [Group H] : (pGroupAlgebraAugmentationIdeal (R := R) (H := H)).IsTwoSided := by
  rw [groupAlgebraAugmentationIdeal_eq_ker]
  infer_instance

/-- An antitone chain of group-ring submodules from `⊤` down to `⊥`, each of whose steps is
lowered by `[g] - 1` for every `g : H`, is a filtration with trivial group action on every
successive quotient. -/
private theorem Module.exists_relSeries_trivial_action_subquotient_of_antitone
    {Λ H M : Type*} [Semiring Λ] [Monoid H] [AddCommGroup M] [Module (MonoidAlgebra Λ H) M]
    (K : ℕ → Submodule (MonoidAlgebra Λ H) M) (N : ℕ) (h₀ : K 0 = ⊤) (hN : K N = ⊥)
    (hK : ∀ i, K (i + 1) ≤ K i)
    (hstep : ∀ i (g : H) (x : M), x ∈ K i →
      MonoidAlgebra.single g (1 : Λ) • x - x ∈ K (i + 1)) :
    ∃ X : RelSeries {p : Submodule (MonoidAlgebra Λ H) M ×
        Submodule (MonoidAlgebra Λ H) M |
      p.1 ≤ p.2 ∧ ∀ (g : H) (x : p.2),
        MonoidAlgebra.single g (1 : Λ) • (x : M) - x ∈ p.1},
      X.head = ⊥ ∧ X.last = ⊤ := by
  refine ⟨{ length := N, toFun := fun i => K (N - i.val), step := fun i => ?_ }, ?_, ?_⟩
  · have hidx : N - i.val = N - (i.val + 1) + 1 := by
      have := i.isLt
      omega
    change K (N - i.val) ≤ K (N - (i.val + 1)) ∧
      ∀ (g : H) (x : K (N - (i.val + 1))),
        MonoidAlgebra.single g (1 : Λ) • (x : M) - x ∈ K (N - i.val)
    rw [hidx]
    exact ⟨hK _, fun g x => hstep _ g x.1 x.2⟩
  · change K N = ⊥
    exact hN
  · change K (N - N) = ⊤
    simpa using h₀

section AugmentationFiltration

variable (Λ H : Type*) {M : Type*} [CommRing Λ] [Group H] [AddCommGroup M]
  [Module (MonoidAlgebra Λ H) M] {ℓ n : ℕ} (hM : ∀ x : M, (ℓ ^ n) • x = 0)

include hM

private noncomputable def zmodGroupAlgebraEnd :
    MonoidAlgebra (ZMod (ℓ ^ n)) H →+* AddMonoid.End M :=
  letI : Module (ZMod (ℓ ^ n)) M := AddCommGroup.zmodModule hM
  MonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd (ZMod (ℓ ^ n)) M)
    ((DistribMulAction.toAddMonoidEnd (MonoidAlgebra Λ H) M).comp (MonoidAlgebra.of Λ H))
    fun a g => by
      change _ * _ = _ * _
      ext x
      exact (ZMod.map_smul (DistribSMul.toAddMonoidHom M (MonoidAlgebra.of Λ H g)) a x).symm

private theorem zmodGroupAlgebraEnd_single (g : H) (x : M) :
    zmodGroupAlgebraEnd Λ H hM (MonoidAlgebra.single g 1) x =
      MonoidAlgebra.single g (1 : Λ) • x := by
  rw [zmodGroupAlgebraEnd, MonoidAlgebra.liftNCRingHom_single, map_one, one_mul]
  rfl

private noncomputable def augmentationFiltration (i : ℕ) : Submodule (MonoidAlgebra Λ H) M :=
  Submodule.span _ (Set.range fun t : ((pGroupAlgebraAugmentationIdeal (R := ZMod (ℓ ^ n))
    (H := H)) ^ i : Ideal (MonoidAlgebra (ZMod (ℓ ^ n)) H)) × M =>
      zmodGroupAlgebraEnd Λ H hM (t.1 : MonoidAlgebra (ZMod (ℓ ^ n)) H) t.2)

private theorem augmentationFiltration_zero : augmentationFiltration Λ H hM 0 = ⊤ :=
  top_unique fun x _ => Submodule.subset_span
    ⟨⟨⟨1, by simp [Submodule.pow_zero, Ideal.one_eq_top]⟩, x⟩, by simp⟩

private theorem augmentationFiltration_succ_le (i : ℕ) :
    augmentationFiltration Λ H hM (i + 1) ≤ augmentationFiltration Λ H hM i :=
  Submodule.span_mono fun _ ⟨⟨a, x⟩, h⟩ =>
    ⟨⟨⟨a.1, Ideal.pow_le_pow_right (Nat.le_succ i) a.2⟩, x⟩, h⟩

private theorem augmentationFiltration_eq_bot {N : ℕ}
    (hN : (pGroupAlgebraAugmentationIdeal (R := ZMod (ℓ ^ n)) (H := H)) ^ N = ⊥) :
    augmentationFiltration Λ H hM N = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro _ ⟨⟨a, x⟩, rfl⟩
  have ha : (a : MonoidAlgebra (ZMod (ℓ ^ n)) H) ∈
      (⊥ : Ideal (MonoidAlgebra (ZMod (ℓ ^ n)) H)) := hN ▸ a.2
  rw [Submodule.mem_bot] at ha
  simp [ha]

private theorem smul_mem_augmentationFiltration_succ_of_mem_submodule {i : ℕ}
    {b : MonoidAlgebra Λ H} (hb : b ∈ groupAlgebraAugmentationSubmodule (R := Λ) (H := H))
    (c : ((pGroupAlgebraAugmentationIdeal (R := ZMod (ℓ ^ n)) (H := H)) ^ i :
      Ideal (MonoidAlgebra (ZMod (ℓ ^ n)) H))) (x : M) :
    b • zmodGroupAlgebraEnd Λ H hM (c : MonoidAlgebra (ZMod (ℓ ^ n)) H) x ∈
      augmentationFiltration Λ H hM (i + 1) := by
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨g, rfl⟩ := hd
    have hc : (MonoidAlgebra.single g 1 - 1) * c.1 ∈
        (pGroupAlgebraAugmentationIdeal (R := ZMod (ℓ ^ n)) (H := H)) ^ (i + 1) := by
      rw [Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (Ideal.subset_span ⟨g, rfl⟩) c.2
    refine Submodule.subset_span ⟨⟨⟨_, hc⟩, x⟩, ?_⟩
    change zmodGroupAlgebraEnd Λ H hM ((MonoidAlgebra.single g 1 - 1) * c.1) x =
      (MonoidAlgebra.single g (1 : Λ) - 1) • zmodGroupAlgebraEnd Λ H hM c x
    rw [map_mul, map_sub, map_one, sub_smul, one_smul, ← zmodGroupAlgebraEnd_single Λ H hM]
    rfl
  | zero => simp
  | add d e _ _ hd he =>
    rw [add_smul]
    exact add_mem hd he
  | smul r d _ hd =>
    rw [Algebra.smul_def, mul_smul]
    exact Submodule.smul_mem _ _ hd

private theorem smul_mem_augmentationFiltration_succ {i : ℕ} {b : MonoidAlgebra Λ H}
    (hb : b ∈ pGroupAlgebraAugmentationIdeal (R := Λ) (H := H)) {x : M}
    (hx : x ∈ augmentationFiltration Λ H hM i) :
    b • x ∈ augmentationFiltration Λ H hM (i + 1) := by
  induction hx using Submodule.span_induction generalizing b with
  | mem y hy =>
    obtain ⟨⟨c, z⟩, rfl⟩ := hy
    refine smul_mem_augmentationFiltration_succ_of_mem_submodule Λ H hM ?_ c z
    simpa [groupAlgebraAugmentationIdeal_eq_ker, groupAlgebraAugmentationSubmodule_eq_ker]
      using hb
  | zero => simp
  | add y z _ _ hy hz =>
    rw [smul_add]
    exact add_mem (hy hb) (hz hb)
  | smul a y _ hy =>
    rw [← mul_smul]
    exact hy (Ideal.mul_mem_right a _ hb)

end AugmentationFiltration

/-- A module over the group ring of a finite `ℓ`-group, annihilated by a power of `ℓ`,
has a finite filtration by group-ring submodules with trivial group action on every successive
quotient. -/
@[stacks 0GIZ, sga "5 I App.1.3.1" "trivial action quotients"]
theorem Module.exists_relSeries_trivial_action_subquotient
    (Λ H M : Type*) [CommRing Λ] [Group H] [Finite H]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hH : IsPGroup ℓ H)
    [AddCommGroup M] [Module (MonoidAlgebra Λ H) M]
    (hM : ∀ x : M, (ℓ ^ n) • x = 0) :
    ∃ X : RelSeries {p : Submodule (MonoidAlgebra Λ H) M ×
        Submodule (MonoidAlgebra Λ H) M |
      p.1 ≤ p.2 ∧ ∀ (g : H) (x : p.2),
        MonoidAlgebra.single g (1 : Λ) • (x : M) - x ∈ p.1},
      X.head = ⊥ ∧ X.last = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨N, hN⟩ := pGroupAlgebra_augmentation_nilpotent (p := ℓ) (n := n) hH
  refine Module.exists_relSeries_trivial_action_subquotient_of_antitone
    (augmentationFiltration Λ H hM) N (augmentationFiltration_zero Λ H hM)
    (augmentationFiltration_eq_bot Λ H hM hN) (augmentationFiltration_succ_le Λ H hM)
    fun i g x hx => ?_
  have h := smul_mem_augmentationFiltration_succ Λ H hM
    (b := MonoidAlgebra.single g (1 : Λ) - 1) (Ideal.subset_span ⟨g, rfl⟩) hx
  rwa [sub_smul, one_smul] at h

