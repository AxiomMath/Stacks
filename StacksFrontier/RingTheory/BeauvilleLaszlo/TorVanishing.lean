module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueingPair
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.BaseChange

@[expose] public section

/-!
# Tor vanishing over a glueing pair

Let `(R → R', f)` be a glueing pair, i.e. `R/fⁿR → R'/fⁿR'` is an isomorphism for every
`n > 0` and `0 → R → R' ⊕ R_f → R'_f → 0` is exact. Even though `R → R'` is typically not
flat, `R'` behaves flatly against the modules that arise in the Beauville--Laszlo
construction. This file records those computations: for the ideals `fⁿR`, for the quotient
`R / R[f^∞]` by the `f`-power torsion, and for the cokernel of `M → M_f`.

## Main results

* `isZero_Tor_one_ideal_pow_of_beauvilleLaszlo_shortExact` (Stacks 0BNZ):
  `Tor₁ᴿ(R', fⁿR) = 0` for every `n > 0`.
* `isZero_Tor_one_quotient_powerTorsion_of_beauvilleLaszlo_shortExact` (Stacks 0BP0):
  `Tor₁ᴿ(R', R / R[f^∞]) = 0`.
* `isZero_Tor_one_coker_localizationMap_of_beauvilleLaszlo_shortExact` (Stacks 0BP1):
  `Tor₁ᴿ(R', coker(M → M_f)) = 0` for every `R`-module `M`.

## Implementation notes

Tor is the categorical `CategoryTheory.Tor` on `ModuleCat`, so `R'` enters as the restriction
of scalars of `R'` along `R → R'` and the vanishing statement is `Limits.IsZero` of the
resulting object.

The proof of Stacks 0BNZ is the source's: from `0 → R[fⁿ] → R → fⁿR → 0` it suffices that
`R[fⁿ] ⊗[R] R' → R'` is injective, and `R[fⁿ] ⊗[R] R' = R[fⁿ]` because `R[fⁿ]` is
`f`-power torsion (Stacks 0BNK), while `R[f^∞] → R'` is injective because `(R → R', f)` is a
glueing pair (Stacks 0BNR).

Stacks 0BP0 writes `R / R[f^∞]` as the filtered colimit of the `R / R[fⁿ⁺¹]`, each of which
is isomorphic to the ideal `fⁿ⁺¹R`, and uses that `Tor` commutes with filtered colimits
(Stacks 0BNF, `tor_flip_preservesColimit_directLimit`).

Stacks 0BP1 reduces to the `f`-power torsion case: the cokernel of `M → M_f` is the union of
its `f`-torsion submodules, on each of which the Tor vanishing follows from the flatness of
`R / fR → R' / fR'` together with Stacks 0BP0 in the case `M = R`. Since the ring, the
target and the module may live in independent universes, the statement is made for the
canonical `ULift` copies, which is what the monoidal category defining `Tor` requires.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BNZ](https://stacks.math.columbia.edu/tag/0BNZ)
* [Stacks Project, Tag 0BP0](https://stacks.math.columbia.edu/tag/0BP0)
* [Stacks Project, Tag 0BP1](https://stacks.math.columbia.edu/tag/0BP1)
-/

namespace BeauvilleLaszlo
section

open CategoryTheory


universe u

end

section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


universe u

private theorem tensor_mk_bijective_of_annihilated
    {R : Type u} [CommRing R] (I : Ideal R)
    {S M : Type u} [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    (n : ℕ) (hM : ∀ x : M, ∀ r ∈ I ^ n, r • x = 0)
    (e : (R ⧸ I ^ n) ≃ₐ[R]
      (S ⧸ Ideal.map (algebraMap R S) (I ^ n))) :
    Function.Bijective (fun x : M ↦ TensorProduct.mk R M S x 1) := by
  classical
  let J := Ideal.map (algebraMap R S) (I ^ n)
  let : Module (R ⧸ I ^ n) M :=
    (show Module.IsTorsionBySet R M ((I ^ n : Ideal R) : Set R) from
      fun {x} r ↦ hM x r.1 r.2).module
  let q : S →+* (R ⧸ I ^ n) :=
    e.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J)
  let : Module S M := Module.compHom M q
  have hq (r : R) : q (algebraMap R S r) = Ideal.Quotient.mk (I ^ n) r := by
    apply e.injective
    change e (e.symm (Ideal.Quotient.mk J (algebraMap R S r))) =
      e (Ideal.Quotient.mk (I ^ n) r)
    rw [e.apply_symm_apply]
    calc
      Ideal.Quotient.mk J (algebraMap R S r) =
          algebraMap R (S ⧸ J) r := by simp
      _ = e (Ideal.Quotient.mk (I ^ n) r) := by
        simpa only [Ideal.Quotient.algebraMap_eq] using (e.commutes r).symm
  let action : M →ₗ[R] S →ₗ[R] M :=
    { toFun := fun x ↦
        { toFun := fun s ↦ q s • x
          map_add' := by intros; simp [add_smul]
          map_smul' := by
            intro r s
            change q (r • s) • x = r • (q s • x)
            rw [Algebra.smul_def, map_mul, hq]
            rw [show r • (q s • x) =
              (Ideal.Quotient.mk (I ^ n) r) • (q s • x) by rfl]
            rw [mul_smul] }
      map_add' := by intros; ext; simp
      map_smul' := by
        intro r x
        ext s
        change q s • ((Ideal.Quotient.mk (I ^ n) r) • x) =
          (Ideal.Quotient.mk (I ^ n) r) • (q s • x)
        rw [← mul_smul, mul_comm, mul_smul] }
  let inv : M ⊗[R] S →ₗ[R] M := TensorProduct.lift action
  let can : M →ₗ[R] M ⊗[R] S :=
    { toFun := fun x ↦ x ⊗ₜ[R] (1 : S)
      map_add' := by intros; exact TensorProduct.add_tmul _ _ _
      map_smul' := by intros; rfl }
  have hinv : Function.LeftInverse inv can := by
    intro x
    change q 1 • x = x
    simp [q]
  have hright : ∀ z, can (inv z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x s =>
        change (q s • x) ⊗ₜ[R] (1 : S) = x ⊗ₜ[R] s
        obtain ⟨r, hr⟩ :=
          Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk J s))
        have heq : Ideal.Quotient.mk J (algebraMap R S r) =
            Ideal.Quotient.mk J s := by
          calc
            _ = e (Ideal.Quotient.mk (I ^ n) r) := by
              rw [Ideal.Quotient.mk_algebraMap]
              exact (e.commutes r).symm
            _ = _ := by simpa using congrArg e hr
        have hd : s - algebraMap R S r ∈ J := by
          apply (Ideal.Quotient.eq_zero_iff_mem).mp
          rw [map_sub, heq, sub_self]
        have hz : x ⊗ₜ[R] (s - algebraMap R S r) = 0 := by
          have hd' : s - algebraMap R S r ∈
              (I ^ n) • (⊤ : Submodule R S) := by
            rw [Ideal.smul_top_eq_map]
            exact hd
          refine Submodule.smul_induction_on hd' ?_ ?_
          · intro a ha t _
            rw [TensorProduct.tmul_smul]
            change (a • x) ⊗ₜ[R] t = 0
            rw [hM x a ha, TensorProduct.zero_tmul]
          · intro y z hy hz
            rw [TensorProduct.tmul_add, hy, hz, add_zero]
        have hs : q s • x = r • x := by
          change e.symm (Ideal.Quotient.mk J s) • x = r • x
          rw [← hr]
          rfl
        rw [hs, TensorProduct.smul_tmul, Algebra.smul_def]
        conv_rhs => rw [show s = algebraMap R S r + (s - algebraMap R S r) by ring]
        rw [TensorProduct.tmul_add, hz, add_zero, mul_one]
    | add x y hx hy => simp [hx, hy]
  exact ⟨hinv.injective, fun z ↦ ⟨inv z, hright z⟩⟩

/-- If `(R → R', f)` is a gluing pair, then
`Tor₁ʿ(R', f ^ n R) = 0` for every positive `n`. -/
@[stacks 0BNZ]
public theorem isZero_Tor_one_ideal_pow_of_beauvilleLaszlo_shortExact
    {R S : Type u} [CommRing R] [CommRing S] (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n φ))
    (hglue : (beauvilleLaszloSequence f φ).ShortExact) :
    ∀ n : ℕ, 0 < n →
      Limits.IsZero (((Tor (ModuleCat.{u} R) 1).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
        (ModuleCat.of R ↑((Ideal.span {f}) ^ n))) := by
  intro n hn
  let : Algebra R S := φ.toAlgebra
  let I : Ideal R := (Ideal.span {f}) ^ n
  let g : (Fin 1 → R) →ₗ[R] I :=
    { toFun := fun x ↦ ⟨f ^ n * x 0, by
        change f ^ n * x 0 ∈ (Ideal.span {f}) ^ n
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨x 0, rfl⟩⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; dsimp; ring }
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    rw [show I = Ideal.span {f ^ n} by simp [I, Ideal.span_singleton_pow],
      Ideal.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    refine ⟨fun _ ↦ a, ?_⟩
    ext
    simp [g]
  let K := LinearMap.ker g
  have hKfixed : ∀ x : K, ∀ r ∈ (Ideal.span {f}) ^ n, r • x = 0 := by
    intro x r hr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
    obtain ⟨a, rfl⟩ := hr
    apply Subtype.ext
    funext i
    fin_cases i
    have hx := congrArg Subtype.val x.property
    change f ^ n * x.1 0 = 0 at hx
    change (f ^ n * a) * x.1 0 = 0
    rw [mul_assoc, mul_comm a, ← mul_assoc, hx, zero_mul]
  have hmk : Function.Bijective
      (fun x : K ↦ TensorProduct.mk R K S x (1 : S)) :=
    let hi : Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n) =
        (Ideal.span {φ f}) ^ n := by
      change Ideal.map φ ((Ideal.span {f}) ^ n) =
        (Ideal.span {φ f}) ^ n
      rw [Ideal.map_pow, Ideal.map_span]
      simp
    let e₀ : (R ⧸ (Ideal.span {f}) ^ n) ≃ₐ[R]
        (S ⧸ (Ideal.span {φ f}) ^ n) :=
      AlgEquiv.ofBijective
        ({ quotientPowMap f n φ with
          commutes' := by intro r; rfl } :
          (R ⧸ (Ideal.span {f}) ^ n) →ₐ[R]
            (S ⧸ (Ideal.span {φ f}) ^ n))
        (hφ n hn)
    tensor_mk_bijective_of_annihilated (Ideal.span {f}) n
      hKfixed
      (e₀.trans (Ideal.quotientEquivAlgOfEq R hi.symm))
  have hpow : Function.Injective (powerTorsionMap f φ) :=
    (((beauvilleLaszloSequence_exactness_iff_powerTorsionMap f φ hφ).2.2.2.1).1
      hglue).1
  have hmap : Function.Injective
      ((torBaseNT (ModuleCat.of R I) g).app
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).hom := by
    intro z w hzw
    obtain ⟨x, rfl⟩ := hmk.2 z
    obtain ⟨y, rfl⟩ := hmk.2 w
    congr 1
    apply Subtype.ext
    funext i
    fin_cases i
    let tx : powerTorsion f := ⟨x.1 0, by
      refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
      exact congrArg Subtype.val x.property⟩
    let ty : powerTorsion f := ⟨y.1 0, by
      refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
      exact congrArg Subtype.val y.property⟩
    have ht : tx = ty := hpow (by
      apply Subtype.ext
      change TensorProduct.map (LinearMap.ker g).subtype
          (LinearMap.id (R := R) (M := S)) (x ⊗ₜ[R] (1 : S)) =
        TensorProduct.map (LinearMap.ker g).subtype
          (LinearMap.id (R := R) (M := S)) (y ⊗ₜ[R] (1 : S)) at hzw
      let ev : (Fin 1 → R) ⊗[R] S →ₗ[R] S :=
        (TensorProduct.lid R S).toLinearMap.comp
          (TensorProduct.map
            { toFun := fun z : Fin 1 → R ↦ z 0
              map_add' := by simp
              map_smul' := by simp }
            (LinearMap.id (R := R) (M := S)))
      have := congrArg
        (fun q : (Fin 1 → R) ⊗[R] S ↦ ev q) hzw
      simpa [ev, tx, ty, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using this)
    exact congrArg Subtype.val ht
  have : Mono ((torBaseNT (ModuleCat.of R I) g).app
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))) :=
    (ModuleCat.mono_iff_injective _).2 hmap
  let swap := Classical.choice
    (tor_symm_canonically_iso (R := R) 1)
  exact IsZero.of_iso
    (isZero_kernel_of_mono ((torBaseNT (ModuleCat.of R I) g).app
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))))
    ((swap.app ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).app
      (ModuleCat.of R I) ≪≫
      torOneIsoKerApp (ModuleCat.of R I) g hg
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))

end

section

open CategoryTheory CategoryTheory.Limits


universe u

/-- The submodule of `R` annihilated by `f ^ (n + 1)`. -/
private def torsionByPowSucc {R : Type u} [CommRing R] (f : R) (n : ℕ) : Submodule R R :=
  Submodule.torsionBy R R (f ^ (n + 1))

/-- The transition map `R / R[f ^ (i + 1)] → R / R[f ^ (j + 1)]` for `i ≤ j`. -/
private def torsionByPowSuccTransition {R : Type u} [CommRing R] (f : R)
    (i j : ULift.{u} ℕ) (h : i ≤ j) :
    (R ⧸ torsionByPowSucc f i.down) →ₗ[R] (R ⧸ torsionByPowSucc f j.down) :=
  Submodule.mapQ (torsionByPowSucc f i.down) (torsionByPowSucc f j.down) LinearMap.id (by
    intro x hx
    change x ∈ torsionByPowSucc f j.down
    change f ^ (i.down + 1) • x = 0 at hx
    change f ^ (j.down + 1) • x = 0
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk]
    calc
      f ^ (i.down + k + 1) • x = f ^ k • (f ^ (i.down + 1) • x) := by
        rw [← mul_smul, ← pow_add]
        congr 2
        omega
      _ = 0 := by rw [hx, smul_zero])

private instance torsionByPowSuccDirectedSystem {R : Type u} [CommRing R] (f : R) :
    DirectedSystem (fun n : ULift.{u} ℕ ↦ R ⧸ torsionByPowSucc f n.down)
      (fun _ _ h ↦ torsionByPowSuccTransition f _ _ h) where
  map_self i x := by
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  map_map k j i hij hjk x := by
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

/-- The map `R / R[f ^ (n + 1)] → R / R[f^∞]`. -/
private def torsionByPowSuccToQuotient {R : Type u} [CommRing R] (f : R) (n : ULift.{u} ℕ) :
    (R ⧸ torsionByPowSucc f n.down) →ₗ[R] (R ⧸ powerTorsion f) :=
  Submodule.mapQ (torsionByPowSucc f n.down) (powerTorsion f) LinearMap.id (by
    intro x hx
    change f ^ (n.down + 1) • x = 0 at hx
    exact ⟨⟨f ^ (n.down + 1), ⟨n.down + 1, rfl⟩⟩, hx⟩)

private theorem torsionByPowSuccToQuotient_compat {R : Type u} [CommRing R] (f : R)
    (i j : ULift.{u} ℕ) (h : i ≤ j) (x : R ⧸ torsionByPowSucc f i.down) :
    torsionByPowSuccToQuotient f j (torsionByPowSuccTransition f i j h x) =
      torsionByPowSuccToQuotient f i x := by
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

/-- The canonical map `colimₙ R / R[f ^ (n + 1)] → R / R[f^∞]`. -/
private noncomputable def directLimitToQuotientPowerTorsion {R : Type u} [CommRing R] (f : R) :
    Module.DirectLimit (fun n : ULift.{u} ℕ ↦ R ⧸ torsionByPowSucc f n.down)
      (torsionByPowSuccTransition f) →ₗ[R] (R ⧸ powerTorsion f) :=
  Module.DirectLimit.lift R (ULift.{u} ℕ) (fun n ↦ R ⧸ torsionByPowSucc f n.down)
    (torsionByPowSuccTransition f) (torsionByPowSuccToQuotient f)
    (torsionByPowSuccToQuotient_compat f)

private theorem directLimitToQuotientPowerTorsion_bijective {R : Type u} [CommRing R] (f : R) :
    Function.Bijective (directLimitToQuotientPowerTorsion f) := by
  constructor
  · intro z w hzw
    obtain ⟨i, x, y, hx, hy⟩ := Module.DirectLimit.exists_of₂ z w
    rw [← hx, ← hy] at hzw ⊢
    simp only [directLimitToQuotientPowerTorsion, Module.DirectLimit.lift_of] at hzw
    induction x using Submodule.Quotient.induction_on with
    | H x =>
     induction y using Submodule.Quotient.induction_on with
     | H y =>
        change Submodule.Quotient.mk x = Submodule.Quotient.mk y at hzw
        rw [Submodule.Quotient.eq] at hzw
        obtain ⟨⟨_, ⟨n, rfl⟩⟩, hn⟩ := hzw
        let j : ULift.{u} ℕ := ⟨max i.down n⟩
        have hij : i ≤ j := le_max_left _ _
        have hstage : torsionByPowSuccTransition f i j hij (Submodule.Quotient.mk x) =
            torsionByPowSuccTransition f i j hij (Submodule.Quotient.mk y) := by
          change Submodule.Quotient.mk x = Submodule.Quotient.mk y
          rw [Submodule.Quotient.eq]
          change f ^ (j.down + 1) • (x - y) = 0
          have hnj : n ≤ j.down + 1 := le_trans (le_max_right i.down n) (Nat.le_succ _)
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnj
          change f ^ n * (x - y) = 0 at hn
          rw [hk, pow_add]
          change (f ^ n * f ^ k) * (x - y) = 0
          rw [mul_comm (f ^ n) (f ^ k), mul_assoc, hn, mul_zero]
        have heq := congrArg
          (Module.DirectLimit.of R (ULift.{u} ℕ)
            (fun q ↦ R ⧸ torsionByPowSucc f q.down) (torsionByPowSuccTransition f) j) hstage
        simpa only [Module.DirectLimit.of_f] using heq
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      exact ⟨Module.DirectLimit.of R (ULift.{u} ℕ)
        (fun n ↦ R ⧸ torsionByPowSucc f n.down) (torsionByPowSuccTransition f) ⟨0⟩
        (Submodule.Quotient.mk x), Module.DirectLimit.lift_of _ _ _⟩

/-- Multiplication by `f ^ (n + 1)` identifies `R / R[f ^ (n + 1)]` with the ideal
`f ^ (n + 1) R`. -/
private noncomputable def quotTorsionByPowSuccEquivIdealPow {R : Type u} [CommRing R]
    (f : R) (n : ℕ) :
    (R ⧸ torsionByPowSucc f n) ≃ₗ[R] ((Ideal.span {f}) ^ (n + 1) : Ideal R) := by
  let g : R →ₗ[R] ((Ideal.span {f}) ^ (n + 1) : Ideal R) :=
    { toFun := fun r ↦ ⟨f ^ (n + 1) * r, by
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨r, rfl⟩⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [smul_eq_mul]; ring }
  have hker : LinearMap.ker g = torsionByPowSucc f n := by
    ext x
    change g x = 0 ↔ f ^ (n + 1) • x = 0
    simp [g, smul_eq_mul]
  rw [← hker]
  apply g.quotKerEquivOfSurjective
  rintro ⟨x, hx⟩
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

/-- `Tor₁ᴿ(N, -)` vanishes on a direct limit of modules on each of which it vanishes. -/
private theorem isZero_Tor_one_of_directLimit_equiv
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [DecidableEq ι] (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (t : (i j : ι) → i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h ↦ t i j h)]
    {Q : Type u} [AddCommGroup Q] [Module R Q] (c : Module.DirectLimit G t ≃ₗ[R] Q)
    (N : ModuleCat.{u} R)
    (hzero : ∀ i, IsZero (((Tor (ModuleCat.{u} R) 1).obj N).obj (ModuleCat.of R (G i)))) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj N).obj (ModuleCat.of R Q)) := by
  let F := (Tor (ModuleCat.{u} R) 1).flip.obj N
  let e := Classical.choice (tor_symm_canonically_iso (R := R) 1)
  have : PreservesColimit (ModuleCat.directLimitDiagram G t) F :=
    tor_flip_preservesColimit_directLimit G t N 1
  have hz : IsZero (F.obj (ModuleCat.of R (Module.DirectLimit G t))) :=
    (isColimitOfPreserves F (ModuleCat.directLimitIsColimit G t)).isZero_pt
      (Functor.isZero _ (fun i ↦ IsZero.of_iso (hzero i)
        (((e.app N).app (ModuleCat.of R (G i))).symm)))
  exact IsZero.of_iso (IsZero.of_iso hz (F.mapIso c.toModuleIso).symm)
    ((e.app N).app (ModuleCat.of R Q))

private theorem isZero_Tor_one_quotTorsionByPowSucc
    {R S : Type u} [CommRing R] [CommRing S] (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ))
    (hglue : (beauvilleLaszloSequence f φ).ShortExact) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
      (ModuleCat.of R (R ⧸ torsionByPowSucc f n))) := by
  have hn : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
      (ModuleCat.of R ((Ideal.span {f}) ^ (n + 1) : Ideal R))) :=
    isZero_Tor_one_ideal_pow_of_beauvilleLaszlo_shortExact f φ hφ hglue (n + 1) (by omega)
  exact IsZero.of_iso hn (((Tor (ModuleCat.{u} R) 1).obj
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).mapIso
      (quotTorsionByPowSuccEquivIdealPow f n).toModuleIso)

/-- If `(R → R', f)` is a glueing pair, then
`Tor₁ᴿ(R', R / R[f^∞]) = 0`. -/
@[stacks 0BP0]
public theorem isZero_Tor_one_quotient_powerTorsion_of_beauvilleLaszlo_shortExact
    {R S : Type u} [CommRing R] [CommRing S] (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ))
    (hglue : (beauvilleLaszloSequence f φ).ShortExact) :
    Limits.IsZero (((Tor (ModuleCat.{u} R) 1).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
      (ModuleCat.of R (R ⧸ powerTorsion f))) := by
  exact isZero_Tor_one_of_directLimit_equiv (fun n : ULift.{u} ℕ ↦ R ⧸ torsionByPowSucc f n.down)
    (torsionByPowSuccTransition f)
    (LinearEquiv.ofBijective (directLimitToQuotientPowerTorsion f)
      (directLimitToQuotientPowerTorsion_bijective f))
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
    (fun n ↦ isZero_Tor_one_quotTorsionByPowSucc f φ hφ hglue n.down)

end

section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


universe u v w

private theorem rTensor_span_subtype_injective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (f : R)
    (h : ∀ s : S, f • s = 0 → ∃ r : R, f * r = 0 ∧ algebraMap R S r = s) :
    Function.Injective (LinearMap.rTensor S (Ideal.span {f}).subtype) := by
  let I : Ideal R := Ideal.span {f}
  let g : R →ₗ[R] I :=
    { toFun := fun r ↦ ⟨f * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; dsimp; ring }
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨r, rfl⟩
  have hsurj := LinearMap.rTensor_surjective S hg
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨t, rfl⟩ := hsurj z
  obtain ⟨s, rfl⟩ := (TensorProduct.lid R S).symm.surjective t
  have hs : f • s = 0 := by
    simpa [g, LinearMap.rTensor, TensorProduct.lid_symm_apply] using
      congrArg (TensorProduct.lid R S) hz
  obtain ⟨r, hr, hrs⟩ := h s hs
  have he : (TensorProduct.lid R S).symm s = r ⊗ₜ[R] (1 : S) := by
    rw [← hrs]
    apply (TensorProduct.lid R S).injective
    simp [Algebra.smul_def]
  rw [he]
  change g r ⊗ₜ[R] (1 : S) = 0
  rw [show g r = 0 from Subtype.ext hr, TensorProduct.zero_tmul]

private theorem tor_one_quotient_span_isZero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (f : R)
    (h : ∀ s : S, f • s = 0 → ∃ r : R, f * r = 0 ∧ algebraMap R S r = s) :
    Tor1Vanishes R (R ⧸ Ideal.span {f}) S := by
  apply tor1_vanishes_of_shortExact_rTensor_injective
    (Ideal.span {f}).subtype (Ideal.span {f}).mkQ
    Subtype.val_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  · exact isZero_Tor_one_of_flat (ModuleCat.of R R) (ModuleCat.of R S)
  · exact rTensor_span_subtype_injective f h

private theorem flat_quotient_of_quotientMap_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (h : Function.Bijective (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.Flat (R ⧸ I) (S ⧸ I • (⊤ : Submodule R S)) := by
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ Ideal.map (algebraMap R S) I) :=
    AlgEquiv.ofBijective
      { toRingHom := Ideal.quotientMap _ (algebraMap R S) Ideal.le_comap_map
        commutes' := by intro r; rfl } h
  let e' : (R ⧸ I) ≃ₗ[R] (S ⧸ I • (⊤ : Submodule R S)) :=
    e.toLinearEquiv ≪≫ₗ
      (Submodule.Quotient.restrictScalarsEquiv R _).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I).symm
  exact Module.Flat.of_linearEquiv
    (e'.extendScalarsOfSurjective Ideal.Quotient.mk_surjective).symm

/-- `Tor₁ᴿ(N, -)` vanishes on a module exhausted by a directed family of submodules on each of
which it vanishes. -/
private theorem tor_one_isZero_of_directed_union
    {R Q : Type u} [CommRing R] [AddCommGroup Q] [Module R Q]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (P : ι → Submodule R Q) (hP : Monotone P)
    (hcover : ∀ x : Q, ∃ i, x ∈ P i) (N : ModuleCat.{u} R)
    (hzero : ∀ i, IsZero (((Tor (ModuleCat.{u} R) 1).obj N).obj
      (ModuleCat.of R (P i)))) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj N).obj (ModuleCat.of R Q)) := by
  classical
  let G : ι → Type u := fun i ↦ P i
  let t : (i j : ι) → i ≤ j → G i →ₗ[R] G j :=
    fun i j h ↦ Submodule.inclusion (hP h)
  let : DirectedSystem G (fun i j h ↦ t i j h) :=
    { map_self := by intros; rfl
      map_map := by intros; rfl }
  let c : Module.DirectLimit G t →ₗ[R] Q :=
    Module.DirectLimit.lift R ι G t (fun i ↦ (P i).subtype) (by intros; rfl)
  have hc : Function.Bijective c := by
    refine ⟨Module.DirectLimit.lift_injective _ _ (fun i ↦ Subtype.val_injective), ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨Module.DirectLimit.of R ι G t i ⟨x, hi⟩,
      Module.DirectLimit.lift_of _ _ _⟩
  exact isZero_Tor_one_of_directLimit_equiv G t (LinearEquiv.ofBijective c hc) N hzero

private theorem tor_one_isZero_of_power_torsion
    {R S Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup Q] [Module R Q] (f : R)
    (hquot : Function.Bijective (Ideal.quotientMap
      (Ideal.map (algebraMap R S) (Ideal.span {f}))
      (algebraMap R S) Ideal.le_comap_map))
    (hlift : ∀ s : S, f • s = 0 → ∃ r : R, f * r = 0 ∧ algebraMap R S r = s)
    (hQ : ∀ x : Q, ∃ n : ℕ, f ^ n • x = 0) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R S)).obj
      (ModuleCat.of R Q)) := by
  let P : ULift.{u} ℕ → Submodule R Q :=
    fun n ↦ Submodule.torsionBy R Q (f ^ n.down)
  have hP : Monotone P := by
    intro i j hij x hx
    change f ^ i.down • x = 0 at hx
    change f ^ j.down • x = 0
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
    rw [hk, pow_add, mul_comm, mul_smul, hx, smul_zero]
  apply tor_one_isZero_of_directed_union P hP
    (fun x ↦ by obtain ⟨n, hn⟩ := hQ x; exact ⟨⟨n⟩, hn⟩)
  intro i
  have hz := tor1_vanishes_of_annihilated (Ideal.span {f})
    (flat_quotient_of_quotientMap_bijective (Ideal.span {f}) hquot)
    (tor_one_quotient_span_isZero f hlift) (P i) i.down (by
      apply le_antisymm _ bot_le
      apply Submodule.smul_le.mpr
      intro r hr x _
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
      obtain ⟨a, rfl⟩ := hr
      change (f ^ i.down * a) • x = 0
      rw [mul_comm, mul_smul, Submodule.smul_torsionBy, smul_zero])
  exact IsZero.of_iso hz
    ((Classical.choice (tor_symm_canonically_iso (R := R) 1)).app
      (ModuleCat.of R S) |>.app (ModuleCat.of R (P i)))

private theorem quotientPowMap_ulift_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R) (φ : R →+* S) (n : ℕ)
    (h : Function.Bijective (quotientPowMap f n φ)) :
    Function.Bijective (quotientPowMap (ULift.up f) n (φ.ulift.{w, w})) := by
  let eR := Ideal.quotientEquiv
    ((Ideal.span {ULift.up f}) ^ n) ((Ideal.span {f}) ^ n)
    (ULift.ringEquiv : ULift.{w} R ≃+* R) (by
      rw [Ideal.map_pow, Ideal.map_span]
      simp only [Set.image_singleton]
      rfl)
  let eS := Ideal.quotientEquiv
    ((Ideal.span {ULift.up (φ f)}) ^ n) ((Ideal.span {φ f}) ^ n)
    (ULift.ringEquiv : ULift.{w} S ≃+* S) (by
      rw [Ideal.map_pow, Ideal.map_span]
      simp only [Set.image_singleton]
      rfl)
  have he (x) : eS (quotientPowMap (ULift.up f) n φ.ulift x) =
      quotientPowMap f n φ (eR x) := by
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  constructor
  · exact fun a b hab ↦ eR.injective (h.1 (by rw [← he, ← he, hab]))
  · intro x
    obtain ⟨y, hy⟩ := h.2 (eS x)
    refine ⟨eR.symm y, eS.injective ?_⟩
    rw [he, eR.apply_symm_apply, hy]

private theorem exists_pow_smul_eq_zero_coker_localizationMap
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (f : R) (x : LocalizedModule (Submonoid.powers f) M ⧸
      LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :
    ∃ n : ℕ, f ^ n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨m, ?_⟩
    simpa only [Submonoid.smul_def, ← hn] using hs.symm

/-- If `(R → R', f)` is a Beauville--Laszlo glueing pair, then for every `R`-module `M`,
`Tor₁ᴿ(R', coker(M → M_f)) = 0`. -/
@[stacks 0BP1]
public theorem isZero_Tor_one_coker_localizationMap_of_beauvilleLaszlo_shortExact
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ))
    (hglue : (beauvilleLaszloSequence f φ).ShortExact) :
    Limits.IsZero (((Tor (ModuleCat.{max u v w}
      (ULift.{max u v w} R)) 1).obj
      ((ModuleCat.restrictScalars (φ.ulift.{max u v w, max u v w})).obj
        (ModuleCat.of (ULift.{max u v w} S) (ULift.{max u v w} S)))).obj
      (ModuleCat.of (ULift.{max u v w} R)
        (ULift.{max u v w}
          (LocalizedModule (Submonoid.powers f) M ⧸
            LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))))) := by
  let : Algebra (ULift.{max u v w} R) (ULift.{max u v w} S) :=
    φ.ulift.toAlgebra
  have hpow : Function.Bijective (powerTorsionMap f φ) :=
    ((beauvilleLaszloSequence_exactness_iff_powerTorsionMap f φ hφ).2.2.2.1).mp hglue
  apply tor_one_isZero_of_power_torsion (ULift.up f)
  · have h := quotientPowMap_ulift_bijective.{u, v, max u v w} f φ 1 (hφ 1 (by omega))
    let eR := (Ideal.quotEquivOfEq
      (pow_one (Ideal.span {ULift.up f} : Ideal (ULift.{max u v w} R)))).symm
    let eS := Ideal.quotEquivOfEq (show
        (Ideal.span {φ.ulift (ULift.up f)} : Ideal (ULift.{max u v w} S)) ^ 1 =
          Ideal.map φ.ulift (Ideal.span {ULift.up f}) by
      rw [pow_one, Ideal.map_span, Set.image_singleton])
    convert eS.bijective.comp (h.comp eR.bijective) using 1
    funext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  · intro s hs
    have hs' : φ f * s.down = 0 := congrArg ULift.down hs
    let t : powerTorsion (φ f) := ⟨s.down, ⟨⟨φ f, ⟨1, pow_one _⟩⟩, hs'⟩⟩
    obtain ⟨r, hr⟩ := hpow.2 t
    have hrφ : φ r = s.down := congrArg Subtype.val hr
    have hfr : f * (r : R) = 0 := by
      have he : powerTorsionMap f φ (f • r) = powerTorsionMap f φ 0 := by
        apply Subtype.ext
        change φ (f * (r : R)) = φ 0
        rw [map_mul, hrφ, hs', map_zero]
      exact congrArg Subtype.val (hpow.1 he)
    exact ⟨ULift.up (r : R), congrArg ULift.up hfr, ULift.ext hrφ⟩
  · intro x
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_coker_localizationMap f x.down
    exact ⟨n, ULift.ext hn⟩

end

end BeauvilleLaszlo

end
