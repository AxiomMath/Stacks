module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.SectionsAlgebra
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Away

/-!
# Gluing ring maps at finitely many maximal ideals

A collection of ring maps defined over the localizations at finitely many distinct maximal
ideals can be realized by one global ring map. Kernel and cokernel remain killed, with a uniform
bound, by a power of the intersection of those maximal ideals
(`Stacks.RingHomGluing.KernelIsKilledByIdealPower` and
`Stacks.RingHomGluing.CokernelIsKilledByIdealPower`). Finiteness, injectivity, and surjectivity
of all the local maps are inherited by the same global map.

That the localization of the global map is the prescribed map is expressed by a map from the
global target to the prescribed local target which commutes with the maps from the source and
satisfies the universal characterization `Submonoid.IsLocalizationMap`.

## Main results

* `Stacks.RingHomGluing.exists_ringHom_inducing_at_maximal_ideal`: the glueing of the prescribed
  local maps.

## References

* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public section

universe w v u


namespace Stacks.RingHomGluing

open scoped ChangeOfRings TensorProduct
open FormalGlueing CategoryTheory
open TensorProduct

private theorem flat_pi_of_finite {R : Type*} [CommSemiring R]
    {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  let := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R ι M).symm


private theorem kernel_isIPowerTorsion {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal R)
    (h : KernelIsKilledByIdealPower f J) :
    IsIPowerTorsion R (↥(RingHom.ker f)) J := by
  obtain ⟨n, hn⟩ := h
  intro x
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  intro a ha
  apply Subtype.ext
  show a * x.1 = 0
  exact hn a (Ideal.pow_le_pow_right n.le_succ ha) x.1 x.2

private theorem cokernel_isIPowerTorsion {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal R)
    (h : CokernelIsKilledByIdealPower f J) :
    letI : Algebra R S := f.toAlgebra
    IsIPowerTorsion R (S ⧸ (Algebra.linearMap R S).range) J := by
  let : Algebra R S := f.toAlgebra
  obtain ⟨n, hn⟩ := h
  intro z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
    (Algebra.linearMap R S).range z
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  intro a ha
  rw [← Submodule.Quotient.mk_smul]
  apply (Submodule.Quotient.mk_eq_zero (Algebra.linearMap R S).range).mpr
  obtain ⟨x, hx⟩ := hn a (Ideal.pow_le_pow_right n.le_succ ha) y
  exact ⟨x, by simpa only [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra,
    Algebra.smul_def] using hx⟩

private theorem isIPowerTorsion_of_linearEquiv {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (J : Ideal R) (h : IsIPowerTorsion R N J) :
    IsIPowerTorsion R M J := by
  intro x
  obtain ⟨n, hn, hkill⟩ := h (e x)
  refine ⟨n, hn, fun a ha ↦ e.injective ?_⟩
  simpa only [map_smul, map_zero] using hkill a ha

private theorem annihilatedByIdealPower_of_linearEquiv {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (J : Ideal R)
    (h : ∃ n : ℕ, ∀ a ∈ J ^ n, ∀ x : N, a • x = 0) :
    ∃ n : ℕ, ∀ a ∈ J ^ n, ∀ x : M, a • x = 0 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun a ha x ↦ e.injective (by simpa only [map_smul, map_zero] using hn a ha (e x))⟩

private theorem localizedMap_bijective_of_torsion {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (J : Ideal R) (g : M →ₗ[R] N)
    (hker : IsIPowerTorsion R g.ker J)
    (hcoker : IsIPowerTorsion R (N ⧸ g.range) J)
    (s : R) (hs : s ∈ J) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers s) g) := by
  let U := Submonoid.powers s
  constructor
  · apply IsLocalizedModule.injective_of_map_zero U (LocalizedModule.mkLinearMap U M)
    intro x hx
    change LocalizedModule.map U g (LocalizedModule.mk x 1) = 0 at hx
    rw [LocalizedModule.map_mk] at hx
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff U
      (LocalizedModule.mkLinearMap U N)).1 hx
    have hg : g ((t : R) • x) = 0 := by
      simpa only [map_smul, Submonoid.smul_def] using ht
    obtain ⟨n, _, hn⟩ := hker ⟨(t : R) • x, hg⟩
    apply (IsLocalizedModule.eq_zero_iff U (LocalizedModule.mkLinearMap U M)).2
    refine ⟨⟨s ^ n, ⟨n, rfl⟩⟩ * t, ?_⟩
    have hzero : s ^ n • ((t : R) • x) = 0 :=
      congrArg Subtype.val (hn (s ^ n) (Ideal.pow_mem_pow hs n))
    simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hzero
  · intro z
    induction z using LocalizedModule.induction_on with
    | h x t =>
      obtain ⟨n, _, hn⟩ := hcoker (g.range.mkQ x)
      have hx : s ^ n • x ∈ g.range := by
        apply (Submodule.Quotient.mk_eq_zero g.range).1
        simpa using hn (s ^ n) (Ideal.pow_mem_pow hs n)
      obtain ⟨y, hy⟩ := hx
      let q : U := ⟨s ^ n, ⟨n, rfl⟩⟩
      refine ⟨LocalizedModule.mk y (q * t), ?_⟩
      rw [LocalizedModule.map_mk, hy]
      exact LocalizedModule.mk_cancel_common_left q t x

private theorem localizedMap_bijective_of_linearEquiv {R M N : Type*}
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (U : Submonoid R) (e : M ≃ₗ[R] N) :
    Function.Bijective (LocalizedModule.map U e.toLinearMap) := by
  have hleft (z : LocalizedModule U M) :
      LocalizedModule.map U e.symm.toLinearMap
        (LocalizedModule.map U e.toLinearMap z) = z := by
    induction z using LocalizedModule.induction_on with
    | h x s => simp [LocalizedModule.map_mk]
  have hright (z : LocalizedModule U N) :
      LocalizedModule.map U e.toLinearMap
        (LocalizedModule.map U e.symm.toLinearMap z) = z := by
    induction z using LocalizedModule.induction_on with
    | h x s => simp [LocalizedModule.map_mk]
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

private theorem localizedMap_bijective_comp {R M N P : Type*}
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] (U : Submonoid R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Bijective (LocalizedModule.map U f))
    (hg : Function.Bijective (LocalizedModule.map U g)) :
    Function.Bijective (LocalizedModule.map U (g.comp f)) := by
  have h : (LocalizedModule.map U (g.comp f)) =
      (LocalizedModule.map U g).comp (LocalizedModule.map U f) := by
    ext z
    induction z using LocalizedModule.induction_on with
    | h x s => simp [LocalizedModule.map_mk]
  rw [h]
  exact hg.comp hf

/-- A member of a power of a product ideal has components in the corresponding powers. -/
private theorem apply_mem_pow_of_mem_pi_pow {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] (J : ∀ i, Ideal (R i)) (N : ℕ) {c : ∀ i, R i}
    (hc : c ∈ (Ideal.pi J) ^ N) (i : ι) : c i ∈ (J i) ^ N := by
  have hmap : Ideal.map (Pi.evalRingHom R i) ((Ideal.pi J) ^ N) = (J i) ^ N := by
    rw [Ideal.map_pow, Ideal.map_evalRingHom_pi]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hc

private theorem kernel_pi_isKilledByIdealPower {ι : Type*} [Finite ι]
    {R S : ι → Type*} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (J : ∀ i, Ideal (R i))
    (h : ∀ i, KernelIsKilledByIdealPower (f i) (J i)) :
    KernelIsKilledByIdealPower
      (RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))) (Ideal.pi J) := by
  classical
  let := Fintype.ofFinite ι
  choose n hn using h
  let N : ℕ := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro c hc x hx
  funext i
  have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  exact hn i (c i) (Ideal.pow_le_pow_right hle (apply_mem_pow_of_mem_pi_pow J N hc i))
    (x i) (congrFun hx i)

private theorem cokernel_pi_isKilledByIdealPower {ι : Type*} [Finite ι]
    {R S : ι → Type*} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (J : ∀ i, Ideal (R i))
    (h : ∀ i, CokernelIsKilledByIdealPower (f i) (J i)) :
    CokernelIsKilledByIdealPower
      (RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))) (Ideal.pi J) := by
  classical
  let := Fintype.ofFinite ι
  choose n hn using h
  let N : ℕ := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro c hc y
  have hle (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  choose x hx using (fun i ↦ hn i (c i)
    (Ideal.pow_le_pow_right (hle i) (apply_mem_pow_of_mem_pi_pow J N hc i)) (y i))
  exact ⟨x, funext hx⟩

private theorem pi_ringHom_injective {ι : Type*}
    {R S : ι → Type*} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective
      (RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))) :=
  fun _ _ h ↦ funext fun i ↦ hf i (congrFun h i)

private theorem pi_ringHom_surjective {ι : Type*}
    {R S : ι → Type*} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective
      (RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))) := by
  intro y
  choose x hx using fun i ↦ hf i (y i)
  exact ⟨x, funext hx⟩

private theorem pi_ringHom_finite {ι : Type*} [Finite ι]
    {R S : ι → Type*} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (hf : ∀ i, (f i).Finite) :
    (RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))).Finite := by
  classical
  let F : (∀ i, R i) →+* (∀ i, S i) :=
    RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))
  let : Algebra (∀ i, R i) (∀ i, S i) := F.toAlgebra
  let g (i : ι) : (∀ j, R j) →+* S i :=
    (f i).comp (Pi.evalRingHom R i)
  let (i : ι) : Algebra (∀ j, R j) (S i) := (g i).toAlgebra
  have (i : ι) : Module.Finite (∀ j, R j) (S i) := by
    have he : Function.Surjective (Pi.evalRingHom R i) := fun x ↦ ⟨Pi.single i x, by simp⟩
    exact (hf i).comp (RingHom.Finite.of_surjective _ he)
  have hmod : (Pi.module ι S (∀ i, R i) : Module (∀ i, R i) (∀ i, S i)) =
      (Algebra.toModule : Module (∀ i, R i) (∀ i, S i)) := by
    apply Module.ext'
    intro r x
    funext i
    rfl
  show Module.Finite (∀ i, R i) (∀ i, S i)
  exact hmod ▸ (inferInstance : @Module.Finite (∀ i, R i) (∀ i, S i) _ _
    (Pi.module ι S (∀ i, R i)))

attribute [local instance] LocalizedModule.algebraOfIsLocalization

attribute [local instance] restrictScalarsCommRing

attribute [local instance] canonicalLocalCommRing

attribute [local instance] canonicalLocalAlgebra

private theorem replaceGenericAlphaAlgEquiv_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (B T : Type (max u v w)) [CommRing B] [CommRing T]
    [Algebra R B] [Algebra S T] (q : S ⊗[R] B →ₐ[S] T)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q.toLinearMap))
    (i : Fin r) (x : S ⊗[R] B) :
    replaceGenericAlphaAlgEquiv f B T q hq i
        (LocalizedModule.mkLinearMap _ T (q x)) =
      canonicalAlpha S f (ModuleCat.of R B) i
        (LocalizedModule.mkLinearMap _ (S ⊗[R] B) x) := by
  let U := Submonoid.powers (algebraMap R S (f i))
  have hmap : localizedAlgHomMap U q
      (LocalizedModule.mkLinearMap U (S ⊗[R] B) x) =
      LocalizedModule.mkLinearMap U T (q x) :=
    LocalizedModule.map_mk U q.toLinearMap x 1
  rw [← hmap]
  show (canonicalAlphaAlgEquiv (S := S) f B i)
      ((AlgEquiv.ofBijective (localizedAlgHomMap U q) (hq i)).symm
        (localizedAlgHomMap U q (LocalizedModule.mkLinearMap U (S ⊗[R] B) x))) = _
  have hcancel :
      (AlgEquiv.ofBijective (localizedAlgHomMap U q) (hq i)).symm
        (localizedAlgHomMap U q (LocalizedModule.mkLinearMap U (S ⊗[R] B) x)) =
      LocalizedModule.mkLinearMap U (S ⊗[R] B) x :=
    (AlgEquiv.ofBijective (localizedAlgHomMap U q) (hq i)).symm_apply_apply _
  rw [hcancel]
  rfl

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (B T : Type (max u v w)) [CommRing B] [CommRing T]
    [Algebra R B] [Algebra S T] (q : S ⊗[R] B →ₐ[S] T)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q.toLinearMap))

variable [Algebra R T] [IsScalarTower R S T]

private theorem mem_canonicalSections_of_mem_sectionsSubalgebra
    (d : sectionsSubalgebra f B T q hq) (z : S ⊗[R] B)
    (hz : q z = d.1.1) :
    (z, d.1.2) ∈ compatibleSections S f (localizationComparisons f)
      (canonicalDatum S f (ModuleCat.of R B)) := by
  have hd := (mem_sections_iff f B T q hq d.1).1 d.2
  constructor
  · intro i
    have hα := replaceGenericAlphaAlgEquiv_mk f B T q hq i z
    rw [hz] at hα
    exact hα.symm.trans (hd.1 i)
  · exact hd.2

end

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {I : Type w} [Finite I]
  (m : I → Ideal A) [∀ i, (m i).IsMaximal]
  (B : I → Type v) [∀ i, CommRing (B i)]

@[ega "IV 2.5.8.8" "partial", sga "3 XXII 5.9.10" "partial"]
private noncomputable def quotientInfEquivPiQuotient
    (hm : Pairwise fun i j ↦ m i ≠ m j) :
    A ⧸ ⨅ i, m i ≃+* (∀ i, A ⧸ m i) :=
  Ideal.quotientInfRingEquivPiQuotient m (fun _ _ hij ↦
    Ideal.isCoprime_of_isMaximal (hm hij))

omit [IsNoetherianRing A] [Finite I] in
private theorem inf_eq_prod [Fintype I] (hm : Pairwise fun i j ↦ m i ≠ m j) :
    (⨅ i, m i) = ∏ i ∈ (Finset.univ : Finset I), m i := by
  have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := (Finset.univ : Finset I)) (J := m)
    (fun i _ j _ hij ↦ Ideal.isCoprime_of_isMaximal (hm hij))
  simpa using h.symm

private theorem map_prod_ideals {R S : Type*} [CommRing R] [CommRing S]
    {ι : Type*} (f : R →+* S) (J : ι → Ideal R) (s : Finset ι) :
    Ideal.map f (∏ i ∈ s, J i) = ∏ i ∈ s, Ideal.map f (J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ideal.map_top f
  | @insert i s his ih =>
    simp only [Finset.prod_insert his, Ideal.map_mul, ih]

private theorem map_pi_eq_pi_map {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] {S : ι → Type*} [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* S i) (J : Ideal R) :
    Ideal.map (RingHom.pi f) J = Ideal.pi (fun i ↦ Ideal.map (f i) J) := by
  apply (Ideal.piOrderIso).injective
  funext i
  show Ideal.map (Pi.evalRingHom S i) (Ideal.map (RingHom.pi f) J) =
    Ideal.map (Pi.evalRingHom S i) (Ideal.pi fun i ↦ Ideal.map (f i) J)
  rw [Ideal.map_map, Ideal.map_evalRingHom_pi]
  rfl

private noncomputable def quotientPiEquiv {ι : Type*} {S : ι → Type*}
    [∀ i, CommRing (S i)] (J : ∀ i, Ideal (S i)) :
    ((∀ i, S i) ⧸ Ideal.pi J) ≃+* (∀ i, S i ⧸ J i) := by
  classical
  let q : (∀ i, S i) →+* (∀ i, S i ⧸ J i) :=
    RingHom.pi (fun i ↦ (Ideal.Quotient.mk (J i)).comp (Pi.evalRingHom S i))
  have hsurj : Function.Surjective q := by
    intro y
    choose x hx using (fun i ↦ Ideal.Quotient.mk_surjective (y i))
    exact ⟨x, funext hx⟩
  have hker : RingHom.ker q = Ideal.pi J := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_pi]
    constructor
    · intro h i
      have hi := congrFun h i
      change (Ideal.Quotient.mk (J i)) (x i) = 0 at hi
      exact Ideal.Quotient.eq_zero_iff_mem.mp hi
    · intro h
      funext i
      change (Ideal.Quotient.mk (J i)) (x i) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

private theorem quotientPiEquiv_apply_mk {ι : Type*} {S : ι → Type*}
    [∀ i, CommRing (S i)] (J : ∀ i, Ideal (S i)) (x : ∀ i, S i) :
    quotientPiEquiv J (Ideal.Quotient.mk (Ideal.pi J) x) =
      fun i ↦ Ideal.Quotient.mk (J i) (x i) := by
  unfold quotientPiEquiv
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ x

omit [IsNoetherianRing A] in
private theorem map_inf_atPrime_eq
    (hm : Pairwise fun i j ↦ m i ≠ m j) (i : I) :
    Ideal.map (algebraMap A (Localization.AtPrime (m i))) (⨅ j, m j) =
      Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i) := by
  let := Fintype.ofFinite I
  rw [inf_eq_prod m hm, map_prod_ideals]
  apply Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
  intro j _ hji
  have hnle : ¬m j ≤ m i := by
    intro h
    exact hm hji (Ideal.IsMaximal.eq_of_le (inferInstance : (m j).IsMaximal)
      (Ideal.IsMaximal.ne_top (inferInstance : (m i).IsMaximal)) h)
  rw [Ideal.one_eq_top]
  exact IsLocalization.AtPrime.map_eq_top_of_not_le
    (Localization.AtPrime (m i)) hnle

omit [IsNoetherianRing A] in
private theorem map_inf_pi_eq_pi_max
    (hm : Pairwise fun i j ↦ m i ≠ m j) :
    Ideal.map (RingHom.pi (fun i ↦ algebraMap A (Localization.AtPrime (m i))))
        (⨅ j, m j) =
      Ideal.pi (fun i ↦ Ideal.map
        (algebraMap A (Localization.AtPrime (m i))) (m i)) := by
  rw [map_pi_eq_pi_map]
  congr 1
  funext i
  exact map_inf_atPrime_eq m hm i

private noncomputable def quotientMaximalEquivLocalizationQuotient (i : I) :
    A ⧸ m i ≃+*
      Localization.AtPrime (m i) ⧸
        (m i).map (algebraMap A (Localization.AtPrime (m i))) :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (m i)
    (Localization.AtPrime (m i))).toRingEquiv.trans
      (Ideal.quotEquivOfEq <|
        (IsLocalization.AtPrime.map_eq_maximalIdeal (m i)
          (Localization.AtPrime (m i))).symm)

omit [IsNoetherianRing A] in
private theorem quotientMap_inf_bijective
    (hm : Pairwise fun i j ↦ m i ≠ m j) :
    Function.Bijective (Ideal.quotientMap
      ((⨅ i, m i).map
        (RingHom.pi (fun i ↦ algebraMap A (Localization.AtPrime (m i)))))
      (RingHom.pi (fun i ↦ algebraMap A (Localization.AtPrime (m i))))
      Ideal.le_comap_map) := by
  let a : A →+* (∀ i, Localization.AtPrime (m i)) :=
    RingHom.pi (fun i ↦ algebraMap A (Localization.AtPrime (m i)))
  let J : Ideal A := ⨅ i, m i
  let K (i : I) : Ideal (Localization.AtPrime (m i)) :=
    (m i).map (algebraMap A (Localization.AtPrime (m i)))
  have h : J.map a = Ideal.pi K := map_inf_pi_eq_pi_max m hm
  let e : A ⧸ J ≃+* (∀ i, Localization.AtPrime (m i)) ⧸ J.map a :=
    ((quotientInfEquivPiQuotient m hm).trans
      (RingEquiv.piCongrRight (fun i ↦ quotientMaximalEquivLocalizationQuotient m i))).trans
      ((quotientPiEquiv K).symm.trans
        (Ideal.quotEquivOfEq h).symm)
  have he (x : A) : e (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (J.map a) (a x) := by
    apply (Ideal.quotEquivOfEq h).injective
    apply (quotientPiEquiv K).injective
    funext i
    simp only [e, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
      Ideal.quotEquivOfEq_mk, quotientPiEquiv_apply_mk,
      RingEquiv.piCongrRight_apply]
    show quotientMaximalEquivLocalizationQuotient m i
      ((quotientInfEquivPiQuotient m hm) (Ideal.Quotient.mk J x) i) =
      Ideal.Quotient.mk (K i) ((a x) i)
    have hcrt : (quotientInfEquivPiQuotient m hm
        (Ideal.Quotient.mk J x)) i = Ideal.Quotient.mk (m i) x := rfl
    rw [hcrt]
    simp only [quotientMaximalEquivLocalizationQuotient, RingEquiv.coe_trans,
      Function.comp_apply, AlgEquiv.coe_toRingEquiv,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
      Ideal.Quotient.mk_algebraMap, RingHom.pi_apply, K, a]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk]
    rfl
  have heq : Ideal.quotientMap (J.map a) a Ideal.le_comap_map = e.toRingHom := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn with
    | _ x => exact (Ideal.quotientMap_mk ..).trans (he x).symm
  simpa only [a, J] using (heq ▸ e.bijective)

/-- If base change along a localization `R → L` identifies `L ⊗[R] D` with `C` compatibly with
the structure map of `D`, then `C` is the localization of `D` at the image of `M`. -/
private theorem localizationMap_of_tensorAlgEquiv
    {R : Type u} {L : Type v} {D : Type w} {C : Type*}
    [CommRing R] [CommRing L] [CommRing D] [CommRing C]
    [Algebra R L] [Algebra R D] [Algebra R C] [Algebra L C] [Algebra D C]
    [IsScalarTower R L C] [IsScalarTower R D C]
    (M : Submonoid R) [IsLocalization M L]
    (e : L ⊗[R] D ≃ₐ[L] C)
    (he : ∀ d : D, e (1 ⊗ₜ[R] d) = algebraMap D C d) :
    (M.map (algebraMap R D)).IsLocalizationMap (algebraMap D C) := by
  apply (isLocalization_iff_isLocalizationMap _ _).mp
  apply (Algebra.isLocalization_iff_isPushout M L).mpr
  apply (Algebra.IsPushout.comm R D L C).mpr
  apply (Algebra.isPushout_iff R L D C).mpr
  exact IsBaseChange.of_equiv e.toLinearEquiv he

private noncomputable def tensorPiLeftAlgEquiv
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Type v) [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)]
    (D : Type w) [CommRing D] [Algebra R D] :
    ((∀ i, L i) ⊗[R] D) ≃ₐ[R] (∀ i, L i ⊗[R] D) :=
  (Algebra.TensorProduct.comm R (∀ i, L i) D).trans
    (((Algebra.TensorProduct.piRight R D D L).restrictScalars R).trans
      (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm R D (L i)))

private theorem tensorPiLeftAlgEquiv_tmul
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Type v) [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)]
    (D : Type w) [CommRing D] [Algebra R D]
    (s : ∀ i, L i) (d : D) (i : ι) :
    tensorPiLeftAlgEquiv L D (s ⊗ₜ[R] d) i = s i ⊗ₜ[R] d := rfl

private theorem pi_eq_single_of_mul_single_one_eq
    {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, CommRing (X i)]
    (i : ι) (z : ∀ j, X j)
    (h : (Pi.single i (1 : X i)) * z = z) : z = Pi.single i (z i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · have hz := congrArg (fun z : ∀ j, X j => z j) h
    simp [hj] at hz
    simp [hj, hz]

private theorem single_one_mul_single
    {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, CommRing (X i)]
    (i : ι) (x : X i) :
    (Pi.single i (1 : X i)) * Pi.single i x = Pi.single i x := by rw [← Pi.single_mul, one_mul]

private noncomputable def piRingEquivComponent
    {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} {Y : ι → Type*}
    [∀ i, CommRing (X i)] [∀ i, CommRing (Y i)]
    (E : (∀ i, X i) ≃+* (∀ i, Y i))
    (hE : ∀ i, E (Pi.single i (1 : X i)) = Pi.single i (1 : Y i))
    (i : ι) : X i ≃+* Y i := by
  have hsx (x : X i) : E (Pi.single i x) = Pi.single i (E (Pi.single i x) i) := by
    apply pi_eq_single_of_mul_single_one_eq i
    rw [← hE i, ← map_mul, single_one_mul_single]
  have hsy (y : Y i) : E.symm (Pi.single i y) =
      Pi.single i (E.symm (Pi.single i y) i) := by
    apply pi_eq_single_of_mul_single_one_eq i
    have he : E.symm (Pi.single i (1 : Y i)) = Pi.single i (1 : X i) := by
      rw [← hE i, E.symm_apply_apply]
    rw [← he, ← map_mul, single_one_mul_single]
  refine {
    toFun := fun x => E (Pi.single i x) i
    invFun := fun y => E.symm (Pi.single i y) i
    left_inv := fun x => ?_
    right_inv := fun y => ?_
    map_mul' := fun x y => ?_
    map_add' := fun x y => ?_ }
  · have h := congrArg (fun z : ∀ j, X j => z i)
      (congrArg E.symm (hsx x))
    simpa using h.symm
  · have h := congrArg (fun z : ∀ j, Y j => z i)
      (congrArg E (hsy y))
    simpa using h.symm
  · rw [Pi.single_mul, map_mul]
    rfl
  · rw [Pi.single_add, map_add]
    rfl

private noncomputable def piAlgEquivComponent
    {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} {Y : ι → Type*}
    [∀ i, CommRing (X i)] [∀ i, CommRing (Y i)]
    [∀ i, Algebra R (X i)] [∀ i, Algebra R (Y i)]
    (E : (∀ i, X i) ≃ₐ[R] (∀ i, Y i))
    (hE : ∀ i, E (Pi.single i (1 : X i)) = Pi.single i (1 : Y i))
    (i : ι) : X i ≃ₐ[R] Y i :=
  AlgEquiv.ofRingEquiv (f := piRingEquivComponent E.toRingEquiv hE i) (by
    intro r
    change E (Pi.single i (algebraMap R (X i) r)) i = algebraMap R (Y i) r
    have hx : Pi.single i (algebraMap R (X i) r) =
        Pi.single i (1 : X i) * algebraMap R (∀ j, X j) r := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · simp [hj]
    rw [hx, map_mul, hE, E.commutes]
    simp)

set_option maxHeartbeats 800000 in
/-- Ring maps over the localizations at finitely many pairwise distinct maximal ideals glue to
one global ring map. The map has kernel and cokernel killed by powers of the
intersection, and it inherits finiteness, injectivity, or surjectivity when all the local maps
have the corresponding property. -/
@[stacks 0EAE]
theorem exists_ringHom_inducing_at_maximal_ideal
    (hm : Pairwise fun i j ↦ m i ≠ m j)
    (f : ∀ i, Localization.AtPrime (m i) →+* B i)
    (hker : ∀ i, KernelIsKilledByIdealPower (f i)
      ((m i).map (algebraMap A (Localization.AtPrime (m i)))))
    (hcoker : ∀ i, CokernelIsKilledByIdealPower (f i)
      ((m i).map (algebraMap A (Localization.AtPrime (m i))))) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (g : A →+* B'),
      (∀ i, ∃ gᵢ : B' →+* B i,
        gᵢ.comp g = (f i).comp (algebraMap A (Localization.AtPrime (m i))) ∧
        (Submonoid.map g (m i).primeCompl).IsLocalizationMap gᵢ) ∧
      KernelIsKilledByIdealPower g (⨅ i, m i) ∧
      CokernelIsKilledByIdealPower g (⨅ i, m i) ∧
      ((∀ i, (f i).Finite) → g.Finite) ∧
      ((∀ i, Function.Injective (f i)) → Function.Injective g) ∧
      ((∀ i, Function.Surjective (f i)) → Function.Surjective g) := by
  let S : Type (max u w) := ∀ i, Localization.AtPrime (m i)
  let : Algebra A S := Pi.algebra I (fun i ↦ Localization.AtPrime (m i))
  let a : A →+* S := algebraMap A S
  have hflat : @Module.Flat A S _ _ Algebra.toModule := flat_pi_localizationAtPrime m
  have hfg : (⨅ i, m i).FG := Ideal.fg_of_isNoetherianRing _
  have hq : Function.Bijective (Ideal.quotientMap
      ((⨅ i, m i).map (algebraMap A S)) (algebraMap A S)
      Ideal.le_comap_map) := by
    show Function.Bijective (Ideal.quotientMap
      ((⨅ i, m i).map (RingHom.pi
        (fun i ↦ algebraMap A (Localization.AtPrime (m i)))))
      (RingHom.pi (fun i ↦ algebraMap A (Localization.AtPrime (m i))))
      Ideal.le_comap_map)
    exact quotientMap_inf_bijective m hm
  obtain ⟨r, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  change Ideal.span (Set.range t) = ⨅ i, m i at ht
  have hq' : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range t)).map (algebraMap A S)) (algebraMap A S)
      Ideal.le_comap_map) := by
    rw [ht]
    exact hq
  let T : Type (max v w) := ∀ i, B i
  let F : S →+* T := RingHom.pi (fun i ↦
    (f i).comp (Pi.evalRingHom (fun i ↦ Localization.AtPrime (m i)) i))
  have hmapF : (⨅ i, m i).map (algebraMap A S) =
      Ideal.pi (fun i ↦ (m i).map (algebraMap A (Localization.AtPrime (m i)))) :=
    map_inf_pi_eq_pi_max m hm
  have hkerF : KernelIsKilledByIdealPower F
      ((⨅ i, m i).map (algebraMap A S)) := by
    rw [hmapF]
    exact kernel_pi_isKilledByIdealPower f _ hker
  have hcokerF : CokernelIsKilledByIdealPower F
      ((⨅ i, m i).map (algebraMap A S)) := by
    rw [hmapF]
    exact cokernel_pi_isKilledByIdealPower f _ hcoker
  have hcokerT : let : Algebra S T := F.toAlgebra
      IsIPowerTorsion S (T ⧸ (Algebra.linearMap S T).range)
        ((⨅ i, m i).map (algebraMap A S)) :=
    cokernel_isIPowerTorsion F _ hcokerF
  let : Algebra S T := F.toAlgebra
  have hkerLin : IsIPowerTorsion S (Algebra.linearMap S T).ker
      ((⨅ i, m i).map (algebraMap A S)) := by
    exact kernel_isIPowerTorsion F _ hkerF
  have hlocF (j : Fin r) : Function.Bijective
      (LocalizedModule.map (Submonoid.powers (a (t j))) (Algebra.linearMap S T)) := by
    have htj : t j ∈ (⨅ i, m i) := by
      rw [← ht]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hsj : a (t j) ∈ (⨅ i, m i).map (algebraMap A S) := by
      show (algebraMap A S) (t j) ∈ _
      exact Ideal.mem_map_of_mem _ htj
    exact localizedMap_bijective_of_torsion _ (Algebra.linearMap S T)
      hkerLin hcokerT _ hsj
  let T₀ : Type (max u v w) := ULift.{max u v w, max v w} T
  let : Algebra S T₀ := ULift.algebra
  let : Algebra A (ULift.{max u v w, u} A) := ULift.algebra
  let : Module A (ULift.{max u v w, u} A) := ULift.module'
  let eB : S ⊗[A] ULift.{max u v w, u} A ≃ₐ[S] S :=
    (Algebra.TensorProduct.congr AlgEquiv.refl ULift.algEquiv).trans
      (Algebra.TensorProduct.rid A S S)
  let q : S ⊗[A] ULift.{max u v w, u} A →ₐ[S] T₀ :=
    (Algebra.ofId S T₀).comp eB.toAlgHom
  have hqLinear : q.toLinearMap =
      (ULift.algEquiv (R := S)).symm.toLinearEquiv.toLinearMap.comp
        ((Algebra.linearMap S T).comp eB.toLinearEquiv.toLinearMap) :=
    LinearMap.ext fun _ ↦ rfl
  have hlocq (j : Fin r) : Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap A S (t j))) q.toLinearMap) := by
    let U := Submonoid.powers (algebraMap A S (t j))
    have h₁ := localizedMap_bijective_of_linearEquiv U eB.toLinearEquiv
    have h₂ : Function.Bijective (LocalizedModule.map U (Algebra.linearMap S T)) := by
      simpa only [U] using hlocF j
    have h₃ := localizedMap_bijective_of_linearEquiv U
      ((ULift.algEquiv (R := S) (A := T) : T₀ ≃ₐ[S] T).symm.toLinearEquiv)
    rw [hqLinear]
    exact localizedMap_bijective_comp U _ _
      (localizedMap_bijective_comp U _ _ h₁ h₂) h₃
  let : Algebra A T₀ := Algebra.compHom T₀ (algebraMap A S)
  let : Module A S := Algebra.toModule
  let : Module S T₀ := Algebra.toModule
  let : Module A T₀ := Algebra.toModule
  let : SMul A S := (Algebra.toModule : Module A S).toSMul
  let : SMul S T₀ := (Algebra.toModule : Module S T₀).toSMul
  let : SMul A T₀ := (Algebra.toModule : Module A T₀).toSMul
  have : IsScalarTower A S T₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let D := sectionsSubalgebra.{u, max u w, v}
    t (ULift.{max u v w, u} A) T₀ q hlocq
  obtain ⟨E, hE⟩ := exists_algEquiv_tensor_sectionsSubalgebra.{u, max u w, v}
    t (ULift.{max u v w, u} A) T₀ q hlocq hflat hq'
  let g : A →+* D := algebraMap A D
  let p (i : I) : D →+* B i :=
    { toFun := fun x => x.1.1.down i
      map_one' := rfl
      map_mul' := by intros; rfl
      map_zero' := rfl
      map_add' := by intros; rfl }
  have hp (i : I) : (p i).comp g =
      (f i).comp (algebraMap A (Localization.AtPrime (m i))) :=
    RingHom.ext fun _ ↦ rfl
  have hE_i (i : I) (s : S) (d : D) :
      (E (s ⊗ₜ[A] d)).down i = (f i) (s i) * p i d := by
    rw [hE]
    rfl
  let (i : I) : Algebra (Localization.AtPrime (m i)) (B i) := (f i).toAlgebra
  let (i : I) : Algebra A (B i) :=
    Algebra.compHom (B i) (algebraMap A (Localization.AtPrime (m i)))
  let : Algebra A T := Pi.algebra I B
  have : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let E' : S ⊗[A] D ≃ₐ[S] T :=
    E.trans (ULift.algEquiv (R := S) (A := T))
  classical
  let : Fintype I := Fintype.ofFinite I
  let P : S ⊗[A] D ≃ₐ[A]
      (∀ i, Localization.AtPrime (m i) ⊗[A] D) :=
    tensorPiLeftAlgEquiv (fun i => Localization.AtPrime (m i)) D
  have hP_tmul (s : S) (d : D) (i : I) :
      P (s ⊗ₜ[A] d) i = s i ⊗ₜ[A] d :=
    tensorPiLeftAlgEquiv_tmul (fun i => Localization.AtPrime (m i)) D s d i
  let E'' : S ⊗[A] D ≃ₐ[A] T :=
    AlgEquiv.ofRingEquiv (f := E'.toRingEquiv) (by
      intro x
      show E' (algebraMap S (S ⊗[A] D) (a x)) = algebraMap S T (a x)
      exact E'.commutes (a x))
  let H : (∀ i, Localization.AtPrime (m i) ⊗[A] D) ≃ₐ[A] T :=
    P.symm.trans E''
  have hP_pure (i : I) (l : Localization.AtPrime (m i)) (d : D) :
      P.symm (Pi.single i (l ⊗ₜ[A] d)) = (Pi.single i l : S) ⊗ₜ[A] d := by
    calc
      P.symm (Pi.single i (l ⊗ₜ[A] d)) =
          P.symm (P ((Pi.single i l : S) ⊗ₜ[A] d)) := by
        congr 1
        funext j
        rw [hP_tmul]
        by_cases hj : j = i
        · subst j
          simp
        · simp [hj]
      _ = _ := P.symm_apply_apply _
  have hP_single (i : I) :
      P.symm (Pi.single i
        (1 : Localization.AtPrime (m i) ⊗[A] D)) =
        (Pi.single i (1 : Localization.AtPrime (m i)) : S) ⊗ₜ[A] (1 : D) := by
    simpa only [Algebra.TensorProduct.one_def] using hP_pure i 1 1
  have hH_single (i : I) :
      H (Pi.single i (1 : Localization.AtPrime (m i) ⊗[A] D)) =
        Pi.single i (1 : B i) := by
    show E' (P.symm _) = _
    rw [hP_single]
    ext j
    show (E ((Pi.single i (1 : Localization.AtPrime (m i)) : S) ⊗ₜ[A]
      (1 : D))).down j = Pi.single i (1 : B i) j
    rw [hE_i]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  let C (i : I) : (Localization.AtPrime (m i) ⊗[A] D) ≃ₐ[A] B i :=
    piAlgEquivComponent H hH_single i
  have hC_pure (i : I) (l : Localization.AtPrime (m i)) (d : D) :
      C i (l ⊗ₜ[A] d) = f i l * p i d := by
    show (E (P.symm (Pi.single i (l ⊗ₜ[A] d)))).down i = _
    rw [hP_pure, hE_i]
    simp
  have hp_apply (i : I) (x : A) :
      p i (g x) = f i (algebraMap A (Localization.AtPrime (m i)) x) :=
    congrArg (fun h : A →+* B i => h x) (hp i)
  have hDfinite (hf : ∀ i, (f i).Finite) : Module.Finite A D := by
    have hFT : F.Finite := pi_ringHom_finite f hf
    have : Module.Finite S T := hFT
    have : Module.Finite S T₀ :=
      Module.Finite.equiv (ULift.moduleEquiv (R := S) (M := T)).symm
    have : Module.Finite A (ULift.{max u v w, u} A) :=
      Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A)).symm
    exact finite_sectionsSubalgebra.{u, max u w, v}
      t (ULift.{max u v w, u} A) T₀ q hlocq hflat hq'
  have hgfinite : (∀ i, (f i).Finite) → g.Finite := by
    intro hf
    have : Module.Finite A D := hDfinite hf
    show (algebraMap A D).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hploc (i : I) :
      (Submonoid.map g (m i).primeCompl).IsLocalizationMap (p i) := by
    have : IsScalarTower A (Localization.AtPrime (m i)) (B i) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : Algebra D (B i) := (p i).toAlgebra
    have : IsScalarTower A D (B i) := IsScalarTower.of_algebraMap_eq (hp_apply i)
    let C' : (Localization.AtPrime (m i) ⊗[A] D) ≃ₐ[Localization.AtPrime (m i)] B i :=
      AlgEquiv.ofRingEquiv (f := (C i).toRingEquiv) (by
        intro l
        show C i (l ⊗ₜ[A] (1 : D)) = f i l
        rw [hC_pure, map_one, mul_one])
    have he (d : D) : C' (1 ⊗ₜ[A] d) = algebraMap D (B i) d := by
      show C i (1 ⊗ₜ[A] d) = p i d
      rw [hC_pure, map_one, one_mul]
    show (Submonoid.map (algebraMap A D) (m i).primeCompl).IsLocalizationMap
      (algebraMap D (B i))
    exact localizationMap_of_tensorAlgEquiv (m i).primeCompl C' he
  have hlocal_val (i : Fin r) (x : A) :
      canonicalLocalMk t (ModuleCat.of A (ULift.{max u v w, u} A)) i
        (ULift.up x) = (g x).1.2 i := by
    show (canonicalLocalAlgHom t (ULift.{max u v w, u} A) i)
      ((ULift.algEquiv (R := A)).symm x) =
        algebraMap A (awayLocalPiece
          t (ULift.{max u v w, u} A) i) x
    exact (canonicalLocalAlgHom t (ULift.{max u v w, u} A) i).commutes x
  have heB_one (x : A) : eB (1 ⊗ₜ[A] ULift.up x) = a x := by
    simp [eB, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]
    rfl
  have hunit_bijective : Function.Bijective
      (canonicalToCompatibleSections.{u, max u w, max u v w} S t
        (ModuleCat.of A (ULift.{max u v w, u} A))) := by
    let c₀ := moduleGlueingConstruction.{u, max u w, max u v w} S t
    let := c₀.category
    have h := FormalGlueing.canonicalSectionsUnit_isIso.{u, max u w, max u v w}
      A S t hflat hq'
    exact ConcreteCategory.bijective_of_isIso
      (c₀.canonicalSectionsUnit.app (ModuleCat.of A (ULift.{max u v w, u} A)))
  have hunit_inj (x y : A) (h₁ : a x = a y) (h₂ : ∀ i, (g x).1.2 i = (g y).1.2 i) : x = y := by
    have hcan : canonicalToCompatibleSections.{u, max u w, max u v w} S t
          (ModuleCat.of A (ULift.{max u v w, u} A)) (ULift.up x) =
        canonicalToCompatibleSections.{u, max u w, max u v w} S t
          (ModuleCat.of A (ULift.{max u v w, u} A)) (ULift.up y) := by
      apply Subtype.ext
      apply Prod.ext
      · apply eB.injective
        show eB (1 ⊗ₜ[A] ULift.up x) = eB (1 ⊗ₜ[A] ULift.up y)
        simpa only [heB_one] using h₁
      · exact funext fun i ↦ (hlocal_val i x).trans ((h₂ i).trans (hlocal_val i y).symm)
    exact ULift.up_injective (hunit_bijective.1 hcan)
  have hg_injective (hf : ∀ i, Function.Injective (f i)) : Function.Injective g := by
    have hF : Function.Injective F := pi_ringHom_injective f hf
    intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    exact hunit_inj x y (hF (congrArg (fun z : T₀ × ∀ i, awayLocalPiece
      t (ULift.{max u v w, u} A) i => z.1.down) hxy'))
      fun i ↦ congrArg (fun z => z.2 i) hxy'
  have hmapPow (n : ℕ) (c : A) (hc : c ∈ (⨅ i, m i) ^ n) :
      a c ∈ ((⨅ i, m i).map (algebraMap A S)) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc
  have hgker : KernelIsKilledByIdealPower g (⨅ i, m i) := by
    obtain ⟨n, hn⟩ := hkerF
    refine ⟨n, fun c hc x hx ↦ ?_⟩
    have hgen : F (a x) = 0 := congrArg (fun z : T₀ × ∀ i, awayLocalPiece
      t (ULift.{max u v w, u} A) i => z.1.down) (congrArg Subtype.val hx)
    refine hunit_inj _ _ ?_ fun i ↦ ?_
    · simpa only [map_mul, map_zero] using hn (a c) (hmapPow n c hc) (a x) hgen
    · exact congrArg (fun z : D => z.1.2 i) ((g.map_mul c x).trans
        ((congrArg (g c * ·) hx).trans ((mul_zero (g c)).trans g.map_zero.symm)))
  have lift_of_generic (d : D) (s : S)
      (hs : F s = d.1.1.down) : ∃ x : A, g x = d := by
    let z : (S ⊗[A] ULift.{max u v w, u} A) ×
        ∀ j, awayLocalPiece t
          (ULift.{max u v w, u} A) j :=
      (eB.symm s, d.1.2)
    have hqz : q z.1 = d.1.1 := by
      show (Algebra.ofId S T₀) (eB (eB.symm s)) = d.1.1
      rw [eB.apply_symm_apply]
      apply ULift.down_injective
      show F s = d.1.1.down
      exact hs
    have hz : z ∈ compatibleSections.{u, max u w, max u v w}
        S t (localizationComparisons t)
        (canonicalDatum.{u, max u w, max u v w}
          S t (ModuleCat.of A (ULift.{max u v w, u} A))) :=
      mem_canonicalSections_of_mem_sectionsSubalgebra
        t (ULift.{max u v w, u} A) T₀ q hlocq d z.1 hqz
    let z' : compatibleSections.{u, max u w, max u v w}
        S t (localizationComparisons t)
        (canonicalDatum.{u, max u w, max u v w}
          S t (ModuleCat.of A (ULift.{max u v w, u} A))) :=
      ⟨z, hz⟩
    obtain ⟨⟨x⟩, hx⟩ := hunit_bijective.2 z'
    have hxval := congrArg Subtype.val hx
    have hax : a x = s := by
      have hh := congrArg (fun y => eB y.1) hxval
      change eB (1 ⊗ₜ[A] ULift.up x) = eB (eB.symm s) at hh
      simpa only [heB_one, eB.apply_symm_apply] using hh
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply ULift.down_injective
      show F (a x) = d.1.1.down
      rw [hax]
      exact hs
    · funext j
      have hh := congrArg (fun y => y.2 j) hxval
      change canonicalLocalMk t (ModuleCat.of A (ULift.{max u v w, u} A)) j
        (ULift.up x) = d.1.2 j at hh
      exact (hlocal_val j x).symm.trans hh
  have hgcoker : CokernelIsKilledByIdealPower g (⨅ i, m i) := by
    obtain ⟨n, hn⟩ := hcokerF
    refine ⟨n, fun c hc d ↦ ?_⟩
    obtain ⟨s, hs⟩ := hn (a c) (hmapPow n c hc) d.1.1.down
    exact lift_of_generic (g c * d) s hs
  have hg_surjective (hf : ∀ i, Function.Surjective (f i)) :
      Function.Surjective g := by
    have hF : Function.Surjective F := pi_ringHom_surjective f hf
    intro d
    obtain ⟨s, hs⟩ := hF d.1.1.down
    exact lift_of_generic d s hs
  exact ⟨D, inferInstance, g, fun i => ⟨p i, hp i, hploc i⟩,
    hgker, hgcoker, hgfinite, hg_injective, hg_surjective⟩

end Stacks.RingHomGluing
